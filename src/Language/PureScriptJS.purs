-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript
-- Copyright   :  (c) Phil Freeman 2013-14
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- The main compiler module
--
-----------------------------------------------------------------------------

module Language.PureScriptJS (
    compile
  ) where

import Data.Array
import Data.Maybe
import Data.Tuple
import Data.Tuple3
import Data.Either
import Data.Function (on)
import Data.String (joinWith)
import Data.Foldable (all, any, elem, find, traverse_)
import Data.Traversable (for, traverse)
import Data.Foreign
import Data.Foreign.NullOrUndefined
import Data.Foreign.Class

import qualified Data.Array.Unsafe as Unsafe
import qualified Data.Maybe.Unsafe as Unsafe

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.Error.Class
import Control.Monad.State
import Control.Monad.State.Class
import Control.Monad.Error.Trans
import Control.Monad.Eff
import Control.Monad.Free

import Control.Apply

import Math (min)

import Language.PureScript.Types
import Language.PureScript.Kinds
import Language.PureScript.Declarations
import Language.PureScript.Names
import Language.PureScript.Options
import Language.PureScript.ModuleDependencies
import Language.PureScript.Environment
import Language.PureScript.Errors
{- import Language.PureScript.DeadCodeElimination -}
import Language.PureScript.Supply

import Language.PureScript.CodeGen.Common
import Language.PureScript.CodeGen.JS
import Language.PureScript.CodeGen.JS.AST
import Language.PureScript.CodeGen.Externs

import Language.PureScript.TypeChecker
import Language.PureScript.TypeChecker.Monad

import Language.PureScript.Sugar
import Language.PureScript.Sugar.BindingGroups

import Language.PureScript.Parser.Lexer (lex)
import Language.PureScript.Parser.Common
import Language.PureScript.Parser.Declarations (parseModule)

import Language.PureScript.Pretty.JS

import Debug.Trace

--import Node.Path

import qualified Language.PureScript.Constants as C

--foreign import procFilePath " var procFilePath = require('fs').realpathSync(process.argv[1]); " :: String

-- |
-- Compile a collection of modules
--
-- The compilation pipeline proceeds as follows:
--
--  * Sort the modules based on module dependencies, checking for cyclic dependencies.
--
--  * Perform a set of desugaring passes.
--
--  * Type check, and elaborate values to include type annotations and type class dictionaries.
--
--  * Regroup values to take into account new value dependencies introduced by elaboration.
--
--  * Eliminate dead code.
--
--  * Generate Javascript, and perform optimization passes.
--
--  * Pretty-print the generated Javascript
--

data Application a = Application (forall eff. ErrorT String (Eff (trace :: Trace | eff)) a)

unApplication :: forall eff a. Application a -> ErrorT String (Eff (trace :: Trace | eff)) a
unApplication (Application m) = m

instance functorApplication :: Functor Application where
  (<$>) f (Application m) = Application (f <$> m)

instance applyApplication :: Apply Application where
  (<*>) (Application f) (Application x) = Application (f <*> x)

instance applicativeApplication :: Applicative Application where
  pure a = Application (pure a)

instance bindApplication :: Bind Application where
  (>>=) (Application m) f = Application (m >>= (unApplication <<< f))

instance monadApplication :: Monad Application

instance monadErrorApplication :: MonadError String Application where
  throwError e = Application (throwError e)
  catchError (Application e) f = Application (catchError e (unApplication <<< f))

runApplication :: forall eff a. Application a -> Eff (trace :: Trace | eff) (Either String a)
runApplication (Application app) = do
  result <- runErrorT app
  case result of
    Left err -> do
      trace err
      return $ Left err
    Right js -> do
      return $ Right js

eitherApplication :: forall a. Either String a -> Application a
eitherApplication e = Application (ErrorT (return e))

effApplication :: forall a. (forall eff. Eff (trace :: Trace | eff) a) -> Application a
effApplication a = Application (lift a)

moduleFromText :: String -> Either String Module
moduleFromText text = do
  tokens <- lex text
  runTokenParser parseModule tokens

readInput :: [String] -> Application [Module]
readInput texts =
  for texts (\text -> do
    case moduleFromText text of
      Left err -> throwError err
      Right mod -> return mod)

compile :: forall eff a. Foreign -> [String] -> Eff (trace :: Trace | eff) {err :: String, result :: String}
compile opt texts = do
  result <- runApplication do
    mods <- readInput texts
    Tuple3 js ext _ <- eitherApplication (_compile _opt mods)
    return js
  case result of
    Left err -> do
      return {err : err, result : ""}
    Right js -> do
      return {err : "", result : js}
  where
  _opt = mkOptions false -- noPrelude
                  false -- noTco
                  false -- performRuntimeTypeChecks
                  false -- noMagicDo
                  (Just "main") -- main
                  false -- noOptimizations
                  (Just "PS")
                  [] -- modules
                  [] -- codeGenModules
                  true -- verboseErrors

_compile :: Options -> [Module] -> Either String (Tuple3 String String Environment)
_compile = compile' initEnvironment

compile' :: Environment -> Options -> [Module] -> Either String (Tuple3 String String Environment)
compile' env opts@(Options optso) ms = do
  Tuple sorted _ <- sortModules $ if optso.noPrelude then ms else (map importPrelude ms)
  Tuple desugared nextVar <- stringifyErrorStack true $ runSupplyT 0 $ desugar sorted
  Tuple elaborated env' <- runCheck' opts env $ for desugared $ typeCheckModule mainModuleIdent
  regrouped <- stringifyErrorStack true $ createBindingGroupsModule <<< collapseBindingGroupsModule $ elaborated
  let
    entryPoints = moduleNameFromString `map` optso.modules
    elim = regrouped -- if null entryPoints then regrouped else eliminateDeadCode entryPoints regrouped
    codeGenModules = moduleNameFromString `map` optso.codeGenModules
    modulesToCodeGen = if null codeGenModules then elim else filter (\(Module mn _ _) -> mn `elem` codeGenModules) elim
    js = evalSupply nextVar $ concat <$> traverse (\m -> moduleToJs Globals opts m env') modulesToCodeGen
    exts = joinWith "\n" <<< map (\m -> moduleToPs m env') $ modulesToCodeGen
  js' <- generateMain env' opts js
  return (Tuple3 (prettyPrintJS js') exts env')
  where
  mainModuleIdent = moduleNameFromString <$> optso.main

typeCheckModule :: Maybe ModuleName -> Module -> Check Module
typeCheckModule mainModuleName (Module mn decls exps) = do
  modify (\(CheckState st) -> CheckState (st { currentModule = Just mn }))
  decls' <- typeCheckAll mainModuleName mn decls
  traverse_ checkTypesAreExported exps'
  return $ Module mn decls' exps
  where

  exps' = Unsafe.fromJust exps

  -- Check that all the type constructors defined in the current module that appear in member types
  -- have also been exported from the module
  checkTypesAreExported :: DeclarationRef -> Check Unit
  checkTypesAreExported (ValueRef name) = do
    ty <- lookupVariable unifyError mn (Qualified (Just mn) name)
    case find isTconHidden (findTcons ty) of
      Just hiddenType -> throwError (strMsg ("Error in module '" ++ show mn ++
                                             "':\nExporting declaration '" ++ show name ++
                                             "' requires type '" ++ show hiddenType ++
                                             "' to be exported as well") :: ErrorStack)
      Nothing -> return unit
  checkTypesAreExported _ = return unit

  -- Find the type constructors exported from the current module used in a type
  findTcons :: Type -> [ProperName]
  findTcons = everythingOnTypes (++) go
    where
    go (TypeConstructor (Qualified (Just mn') name)) | mn' == mn = [name]
    go _ = []

  -- Checks whether a type constructor is not being exported from the current module
  isTconHidden :: ProperName -> Boolean
  isTconHidden tyName = all go exps'
    where
    go (TypeRef tyName' _) = tyName' /= tyName
    go _ = true

generateMain :: Environment -> Options -> [JS] -> Either String [JS]
generateMain env@(Environment envo) opts@(Options optso) js =
  case moduleNameFromString <$> optso.main of
    Just mmi -> do
      unless (Tuple mmi (Ident C.main) `M.member` envo.names) $
        Left $ show mmi ++ "." ++ C.main ++ " is undefined"
      return $ js ++ [JSApp (JSAccessor C.main (JSAccessor (moduleNameToJs mmi) (JSVar (Unsafe.fromJust optso.browserNamespace)))) []]
    _ -> return js

importPrelude :: Module -> Module
importPrelude m@(Module mn decls exps) =
  if any isPreludeImport decls || mn == prelude then m else Module mn (preludeImport : decls) exps
  where
  prelude :: ModuleName
  prelude = ModuleName [ProperName C.prelude]

  isPreludeImport :: Declaration -> Boolean
  isPreludeImport (ImportDeclaration (ModuleName [ProperName mn']) _ _) | mn' == C.prelude = true
  isPreludeImport (PositionedDeclaration _ d) = isPreludeImport d
  isPreludeImport _ = false

  preludeImport :: Declaration
  preludeImport = ImportDeclaration prelude Nothing Nothing

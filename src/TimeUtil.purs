module TimeUtil where

foreign import time
  "function time (s) {\
  \  return function (f) {\
  \      var t = Date.now();\
  \      var result = f({});\
  \      console.log(s + ': ' + (Date.now()-t) + 'ms');\
  \      return result;\
  \  };\
  \}" :: forall a b. String -> (Unit -> a) -> a

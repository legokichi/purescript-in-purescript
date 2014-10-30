(function(global) {
"use strict";

var PureScript = require("Language.PureScriptJS");

if ("process" in global) {
    module["exports"] = PureScript;
}
global["PureScript"] = PureScript;

})((this || 0).self || global);

module.exports = function(grunt) {

    "use strict";

    grunt.initConfig({ 
    
        clean: ["externs", "js"],
    
        purescript: {
            options: {
                tco: true,
                magicDo: true
            },
            all: {
                options: { make: true },
                files: {
                    _: [ "src/**/*.purs.hs"
                       , "bower_components/purescript-*/src/**/*.purs"
                       , "bower_components/purescript-*/src/**/*.purs.hs"
                       ]
                }
            }
        }
        
    });

    grunt.loadNpmTasks("grunt-purescript");
    grunt.loadNpmTasks("grunt-contrib-clean");

    grunt.registerTask("default", ["purescript:all"]);
};
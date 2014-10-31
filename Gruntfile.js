module.exports = function(grunt) {

  "use strict";

  grunt.initConfig({

    libFiles: [
      "src/**/*.purs",
      "bower_components/purescript-*/src/**/*.purs*"
    ],

    watch: {
      lib: {
        files: ["<%=libFiles%>"],
        tasks: ["pscMake"]
      }
    },

    clean: ["output", "dist"],

    pscMake: ["<%=libFiles%>"],
    dotPsci: ["<%=libFiles%>"],

    copy: [
      {
        expand: true,
        cwd: "output",
        src: "**",
        dest: "dist/node_modules/"
      },
      {
        expand: true,
        cwd: "js",
        src: "**",
        dest: "dist/"
      }
    ],

    execute: {
      psc: {
        src: "dist/psc.js"
      }
    },

    browserify: {
      dist : {
        src : 'dist/PureScript.js',
        dest : 'dist/PureScript.browserify.js'
      }
    }

  });

  grunt.loadNpmTasks("grunt-contrib-clean");
  grunt.loadNpmTasks("grunt-contrib-copy");
  grunt.loadNpmTasks('grunt-contrib-watch');
  grunt.loadNpmTasks('grunt-execute');
  grunt.loadNpmTasks("grunt-purescript");
  grunt.loadNpmTasks('grunt-browserify');

  grunt.registerTask("make", ["pscMake", "dotPsci", "copy", "browserify"]);
  grunt.registerTask("psc", ["make", "execute:psc"]);
  grunt.registerTask("default", ["make"]);
};

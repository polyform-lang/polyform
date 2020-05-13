var path = require('path');
const ClosurePlugin = require('closure-webpack-plugin');

module.exports = {
  mode: 'production',
  entry: {
    index: './src/index.js',
    // runtime: '../polyform/bin/js_runtime.js',
  },
  output: {
    path: path.resolve(__dirname, 'dist'),
    filename: '[name].bundle.js'
  },
  optimization: {
    concatenateModules: false,
    minimizer: [
      new ClosurePlugin({mode: 'AGGRESSIVE_BUNDLE'}, {
        // compiler flags here
        //
        // for debugging help, try these:
        //
        // formatting: 'PRETTY_PRINT'
        // debug: true,
        // renaming: false
        warning_level: "QUIET"
      })
    ],
    splitChunks: {
      // include all types of chunks
      chunks: 'all'
    }
  },
};
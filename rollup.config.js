import typescript from "rollup-plugin-typescript2";
import commonjs   from "rollup-plugin-commonjs";
import external   from "rollup-plugin-peer-deps-external";
import resolve    from "rollup-plugin-node-resolve";
import {uglify}     from "rollup-plugin-uglify";
import postcss    from "rollup-plugin-postcss";
import svgr       from '@svgr/rollup';
import url        from 'rollup-plugin-url';
import pkg        from "./package.json";

export default {
  input:     "src/index.tsx",
  output:    [
    {
      file:      pkg.module,
      format:    "esm",
      exports:   "named",
      sourcemap: true
    }
  ],
  external:  [...Object.keys(pkg.dependencies || {}),
    ...Object.keys(pkg.peerDependencies || {})],
  treeshake: true,
  plugins:   [
    external(),
    resolve({browser: true}),
    typescript({
      typescript:                  require("typescript"),
      useTsconfigDeclarationDir:   true,
      objectHashIgnoreUnknownHack: true
    }),
    commonjs({
      include:      ["node_modules/**"],
      namedExports: {
        "node_modules/react/react.js":      [
          "Children",
          "Component",
          "PropTypes",
          "createElement"
        ],
        "node_modules/react-dom/index.js":  ["render"],
        "node_modules/react-is/index.js":   ["ForwardRef"],
        "node_modules/prop-types/index.js": ["shape", "elementType", "bool", "any", "array", "arrayOf", "func", "number", "object", "oneOf", "oneOfType", "string"]
      }
    }),
    postcss({
      extract: true,
      modules: false,
      use:     ['sass'],
      uglify:  true
    }),
    url({
      limit:     10 * 1024, // inline files < 10k, copy files > 10k
      include:   ["src/**/*.svg", "**/*.svg"], // defaults to .svg, .png, .jpg and .gif files
      emitFiles: true // defaults to true
    }),
    svgr(),
    (process.env.NODE_ENV === "production" && uglify({sourcemap: false}))
  ]
};

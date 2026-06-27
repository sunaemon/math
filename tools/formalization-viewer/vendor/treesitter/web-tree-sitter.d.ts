// Hand-written type shim for the vendored tree-sitter runtime
// (web-tree-sitter.js in this directory, refreshed by
// tools/fetch_treesitter_assets.sh). This file is NOT fetched — it is
// committed deliberately.
//
// Its only job is to stop `tsc` from type-checking the bundled runtime: when a
// `.d.ts` sits next to a `.js`, TypeScript resolves imports to the declaration
// and never reads the implementation. The upstream package ships its own
// declarations, but as `declare module 'web-tree-sitter' { ... }` keyed to the
// bare specifier, which does not resolve through the viewer's relative
// `./vendor/treesitter/web-tree-sitter.js` import. We therefore declare just
// the three named exports the viewer uses.
//
// Typed as `any` on purpose: this silences the vendored runtime, it is not a
// place to model its API. If the viewer ever wants real tree-sitter types,
// install web-tree-sitter as a dev dependency and map the import instead.
export const Parser: any;
export const Language: any;
export const Query: any;

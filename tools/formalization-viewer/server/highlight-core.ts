// Tree-sitter syntax highlighting, computed on the Node side.
//
// Highlight spans are a pure function of a source file's text, so they are
// computed here — at static-distribution build time (highlight-cache.ts
// generate) or on demand by the live server — instead of in the browser. The
// browser only fetches the resulting JSON (see src/highlight.ts); it never
// loads the tree-sitter runtime or grammars.
//
// Lean sources are parsed with the Lean grammar; Markdown sources with the
// Markdown block grammar plus the inline grammar over the block grammar's
// inline regions, plus a LaTeX-aware overlay because the .md sources embed
// heavy TeX (macros, environments, math) that the Markdown grammar treats as
// plain prose. The vendored runtime, grammars, and queries live under
// vendor/treesitter/ and are smoke-checked by check_highlights.mjs.
//
// computeHighlightData() returns sorted, non-overlapping {startOffset,
// endOffset, cls} segments in UTF-16 offsets, plus the Lean fold ranges of
// `/-@ … -/` machine-metadata comments — exactly what the browser highlighter
// used to compute locally.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Parser, Language, Query } from "../vendor/treesitter/web-tree-sitter.js";

export interface HighlightSpan {
  startOffset: number;
  endOffset: number;
  cls: string;
}
export interface HighlightFold {
  startOffset: number;
  endOffset: number;
}
export interface HighlightData {
  spans: HighlightSpan[];
  folds: HighlightFold[];
}

type Lang = { parser: any; query: any };
type Highlighter = { lean: Lang; mdBlock: Lang; mdInline: Lang };

const VENDOR_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "vendor", "treesitter");

// Capture name -> CSS class. Lookup tries the full dotted capture name, then
// drops trailing `.segments` (so `keyword.import` falls back to `keyword`,
// `comment.documentation` to `comment`, `number.float` to `number`). A capture
// that resolves to nothing is dropped: this covers @none, @variable (too noisy
// in Lean), @property, and any capture the grammars add later.
const CAPTURE_CLASSES: Record<string, string> = {
  keyword: "tok-keyword",
  comment: "tok-comment",
  string: "tok-string",
  character: "tok-string",
  number: "tok-number",
  boolean: "tok-number",
  constant: "tok-number",
  type: "tok-type",
  constructor: "tok-type",
  function: "tok-function",
  method: "tok-function",
  operator: "tok-operator",
  punctuation: "tok-punctuation",
  attribute: "tok-attribute",
  module: "tok-module",
  namespace: "tok-module",
  label: "tok-label",
  tag: "tok-label",
  // Markdown highlights.scm uses the older nvim `text.*` capture convention.
  "text.title": "tok-heading",
  "text.emphasis": "tok-emph",
  "text.strong": "tok-strong",
  "text.literal": "tok-literal",
  "text.uri": "tok-link",
  "text.reference": "tok-label",
  // Forward-compatible aliases for the `markup.*` convention.
  "markup.heading": "tok-heading",
  "markup.italic": "tok-emph",
  "markup.bold": "tok-strong",
  "markup.raw": "tok-literal",
  "markup.link": "tok-link",
};

function captureClass(name: string): string | null {
  let key = name;
  for (;;) {
    const cls = CAPTURE_CLASSES[key];
    if (cls) return cls;
    const dot = key.lastIndexOf(".");
    if (dot === -1) return null;
    key = key.slice(0, dot);
  }
}

let highlighterPromise: Promise<Highlighter> | null = null;

// Memoized async init of the vendored runtime and grammars. Unlike the old
// browser loader this rejects on failure: a broken grammar or query must fail
// the build (or the request) loudly instead of silently disabling highlights.
export function loadHighlighter(): Promise<Highlighter> {
  if (!highlighterPromise) {
    highlighterPromise = (async () => {
      await Parser.init({ locateFile: (name: string) => path.join(VENDOR_DIR, name) });
      const load = async (file: string) => Language.load(new Uint8Array(fs.readFileSync(path.join(VENDOR_DIR, file))));
      const queryText = (file: string) => fs.readFileSync(path.join(VENDOR_DIR, "queries", file), "utf-8");
      const [lean, markdown, markdownInline] = await Promise.all([
        load("tree-sitter-lean.wasm"),
        load("tree-sitter-markdown.wasm"),
        load("tree-sitter-markdown_inline.wasm"),
      ]);
      return {
        lean: makeLang(lean, queryText("lean.scm")),
        mdBlock: makeLang(markdown, queryText("markdown.scm")),
        mdInline: makeLang(markdownInline, queryText("markdown_inline.scm")),
      };
    })();
  }
  return highlighterPromise;
}

function makeLang(language: any, querySource: string): Lang {
  const parser = new Parser();
  parser.setLanguage(language);
  return { parser, query: new Query(language, querySource) };
}

export function languageForPath(path: string | null | undefined): "lean" | "markdown" | null {
  if (!path) return null;
  if (path.endsWith(".lean")) return "lean";
  if (path.endsWith(".md")) return "markdown";
  return null;
}

// Highlight spans and fold ranges for one source text. Throws on parse/query
// failure; callers that would rather degrade to plain text catch it.
export async function computeHighlightData(text: string, lang: "lean" | "markdown"): Promise<HighlightData> {
  const hl = await loadHighlighter();
  if (!text) return { spans: [], folds: [] };
  return lang === "lean" ? leanData(hl, text) : { spans: flatten(markdownCaptures(hl, text), text.length), folds: [] };
}

function leanData(hl: Highlighter, text: string): HighlightData {
  const tree = hl.lean.parser.parse(text);
  try {
    const spans = flatten(toSpans(hl.lean.query.captures(tree.rootNode)), text.length);
    // Offset ranges of machine-metadata comments `/-@ … -/`. These are ordinary
    // Lean block comments (the `@` sentinel keeps them distinct from `/--` doc
    // comments and `/- … -/` prose), which the viewer folds by default.
    const folds: HighlightFold[] = [];
    for (const node of tree.rootNode.descendantsOfType("block_comment")) {
      if (text.startsWith("/-@", node.startIndex)) {
        folds.push({ startOffset: node.startIndex, endOffset: node.endIndex });
      }
    }
    return { spans, folds };
  } finally {
    tree.delete();
  }
}

function markdownCaptures(hl: Highlighter, text: string): HighlightSpan[] {
  const blockTree = hl.mdBlock.parser.parse(text);
  try {
    const spans = toSpans(hl.mdBlock.query.captures(blockTree.rootNode));
    // The Markdown grammars expose comments as raw HTML, not comment nodes.
    // Only inspect HTML nodes, so fenced/indented code, inline code, and escaped
    // openers keep their literal meaning. A block may end with ordinary text on
    // the closing line; stop the comment span at --> rather than its node end.
    for (const node of blockTree.rootNode.descendantsOfType("html_block")) {
      for (const match of node.text.matchAll(/<!--[\s\S]*?(?:-->|$)|<(?:"[^"]*"|'[^']*'|[^'">])*>/g)) {
        if (!match[0].startsWith("<!--")) continue;
        spans.push({
          startOffset: node.startIndex + match.index,
          endOffset: node.startIndex + match.index + match[0].length,
          cls: "tok-comment",
        });
      }
    }

    const inlineNodes = blockTree.rootNode.descendantsOfType("inline");
    if (inlineNodes.length > 0) {
      const includedRanges = inlineNodes.map((node: any) => ({
        startIndex: node.startIndex,
        endIndex: node.endIndex,
        startPosition: node.startPosition,
        endPosition: node.endPosition,
      }));
      const inlineTree = hl.mdInline.parser.parse(text, null, { includedRanges });
      try {
        spans.push(...toSpans(hl.mdInline.query.captures(inlineTree.rootNode)));
        for (const node of inlineTree.rootNode.descendantsOfType("html_tag")) {
          if (node.text.startsWith("<!--"))
            spans.push({ startOffset: node.startIndex, endOffset: node.endIndex, cls: "tok-comment" });
        }
      } finally {
        inlineTree.delete();
      }
    }

    // The .md sources are Pandoc Markdown with heavy embedded LaTeX. The
    // Markdown grammar treats raw \macros, \begin{}/\end{} environments, and
    // $...$ math as plain prose text, so overlay a LaTeX-aware pass that colors
    // them everywhere (prose included). These spans are shorter than the
    // Markdown block spans, so flatten()'s innermost-wins keeps them on top.
    spans.push(...latexSpans(text));
    return spans;
  } finally {
    blockTree.delete();
  }
}

// LaTeX overlay for Markdown sources: \commands and \begin/\end as keywords,
// environment names as types, $ / $$ as math-delimiter operators, and {} as
// grouping punctuation. Spans may overlap; flatten() resolves them.
function latexSpans(text: string): HighlightSpan[] {
  const spans: HighlightSpan[] = [];
  const push = (start: number, end: number, cls: string) => {
    if (end > start) spans.push({ startOffset: start, endOffset: end, cls });
  };
  let m;

  // \begin{env} / \end{env}: the control word is a keyword, the env name a type.
  const envRe = /(\\(?:begin|end))\s*\{([^}]*)\}/g;
  while ((m = envRe.exec(text)) !== null) {
    push(m.index, m.index + m[1].length, "tok-keyword");
    const nameStart = text.indexOf("{", m.index + m[1].length) + 1;
    push(nameStart, nameStart + m[2].length, "tok-type");
  }

  // Control words (\termdefine, \IncludedIn, …) and control symbols (\\, \{, \,).
  const commandRe = /\\[a-zA-Z@]+\*?|\\[^a-zA-Z@\s]/g;
  while ((m = commandRe.exec(text)) !== null) push(m.index, m.index + m[0].length, "tok-keyword");

  // Math delimiters: $ and $$.
  const mathRe = /\$\$?/g;
  while ((m = mathRe.exec(text)) !== null) push(m.index, m.index + m[0].length, "tok-operator");

  // TeX grouping braces.
  const braceRe = /[{}]/g;
  while ((m = braceRe.exec(text)) !== null) push(m.index, m.index + 1, "tok-punctuation");

  return spans;
}

function toSpans(captures: any): HighlightSpan[] {
  const spans: HighlightSpan[] = [];
  for (const { name, node } of captures) {
    const cls = captureClass(name);
    if (!cls) continue;
    if (node.endIndex <= node.startIndex) continue;
    spans.push({ startOffset: node.startIndex, endOffset: node.endIndex, cls });
  }
  return spans;
}

// Resolve overlapping captures to a flat, non-overlapping coloring. Innermost
// (shortest) capture wins except inside comments: comment syntax takes priority
// over embedded Markdown/TeX. Paint comments last, then coalesce equal-class runs.
function flatten(spans: HighlightSpan[], length: number): HighlightSpan[] {
  if (!spans.length || length <= 0) return [];
  spans.sort(
    (a, b) =>
      Number(a.cls === "tok-comment") - Number(b.cls === "tok-comment") ||
      b.endOffset - b.startOffset - (a.endOffset - a.startOffset),
  );

  const paint: (string | null)[] = Array.from({ length }, () => null);
  for (const span of spans) {
    const start = Math.max(0, span.startOffset);
    const end = Math.min(length, span.endOffset);
    for (let i = start; i < end; i += 1) paint[i] = span.cls;
  }

  const segments: HighlightSpan[] = [];
  let i = 0;
  while (i < length) {
    const cls = paint[i];
    if (cls === null) {
      i += 1;
      continue;
    }
    let j = i + 1;
    while (j < length && paint[j] === cls) j += 1;
    segments.push({ startOffset: i, endOffset: j, cls });
    i = j;
  }
  return segments;
}

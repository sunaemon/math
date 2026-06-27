// Tree-sitter syntax highlighting for the formalization viewer.
//
// Lean panes are parsed with the Lean grammar; .md panes are parsed as
// Markdown (block grammar + inline grammar over the block grammar's inline
// regions), plus a LaTeX-aware overlay because the .md sources embed heavy TeX
// (macros, environments, math) that the Markdown grammar treats as plain prose.
// The TeX pane stays plain. Everything degrades to plain text if the
// vendored runtime, grammars, or queries fail to load: initHighlighter()
// resolves to null instead of rejecting, and callers treat null as "no
// highlights".
//
// computeHighlights() returns sorted, non-overlapping {startOffset, endOffset,
// cls} segments in the same UTF-16 offset space app.js slices source text with.
// The caller composes these token segments with the source-map "mark" overlay.

import { Parser, Language, Query } from "../vendor/treesitter/web-tree-sitter.js";

type Span = { startOffset: number; endOffset: number; cls: string };
type Lang = { parser: any; query: any };
type Highlighter = { lean: Lang; mdBlock: Lang; mdInline: Lang };

const VENDOR = new URL("../vendor/treesitter/", import.meta.url);

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

let highlighterPromise: Promise<Highlighter | null> | null = null;

// Memoized async init. Resolves to a highlighter handle, or null on any
// failure (logged once). Never rejects.
export function initHighlighter(): Promise<Highlighter | null> {
  if (!highlighterPromise) {
    highlighterPromise = loadHighlighter().catch((error) => {
      console.warn("[booklink] syntax highlighting unavailable:", error);
      return null;
    });
  }
  return highlighterPromise;
}

async function loadHighlighter(): Promise<Highlighter> {
  await Parser.init({ locateFile: (name: string) => new URL(name, VENDOR).href });

  const [lean, markdown, markdownInline] = await Promise.all([
    Language.load(new URL("tree-sitter-lean.wasm", VENDOR).href),
    Language.load(new URL("tree-sitter-markdown.wasm", VENDOR).href),
    Language.load(new URL("tree-sitter-markdown_inline.wasm", VENDOR).href),
  ]);

  const [leanScm, markdownScm, markdownInlineScm] = await Promise.all([
    fetchText("queries/lean.scm"),
    fetchText("queries/markdown.scm"),
    fetchText("queries/markdown_inline.scm"),
  ]);

  return {
    lean: makeLang(lean, leanScm),
    mdBlock: makeLang(markdown, markdownScm),
    mdInline: makeLang(markdownInline, markdownInlineScm),
  };
}

function makeLang(language: any, querySource: string): Lang {
  const parser = new Parser();
  parser.setLanguage(language);
  return { parser, query: new Query(language, querySource) };
}

async function fetchText(relative: string): Promise<string> {
  const response = await fetch(new URL(relative, VENDOR).href);
  if (!response.ok) throw new Error(`${relative}: HTTP ${response.status}`);
  return response.text();
}

export function languageForPath(path: string | null | undefined): "lean" | "markdown" | null {
  if (!path) return null;
  if (path.endsWith(".lean")) return "lean";
  if (path.endsWith(".md")) return "markdown";
  return null;
}

// Returns sorted, non-overlapping {startOffset, endOffset, cls} segments.
// Returns [] on any parse/query failure so rendering falls back to plain text.
export function computeHighlights(hl: Highlighter | null, text: string, lang: string | null): Span[] {
  if (!hl || !text) return [];
  try {
    const captures = lang === "lean" ? leanCaptures(hl, text) : markdownCaptures(hl, text);
    return flatten(captures, text.length);
  } catch (error) {
    console.warn("[booklink] computeHighlights failed:", error);
    return [];
  }
}

function leanCaptures(hl: Highlighter, text: string): Span[] {
  const tree = hl.lean.parser.parse(text);
  try {
    return toSpans(hl.lean.query.captures(tree.rootNode));
  } finally {
    tree.delete();
  }
}

// Offset ranges of machine-metadata comments `/-@ … -/` in a Lean source. These
// are ordinary Lean block comments (the `@` sentinel keeps them distinct from
// `/--` doc comments and `/- … -/` prose), which the viewer folds by default.
export function leanFolds(hl: Highlighter | null, text: string): { startOffset: number; endOffset: number }[] {
  if (!hl || !text) return [];
  try {
    const tree = hl.lean.parser.parse(text);
    try {
      const folds = [];
      for (const node of tree.rootNode.descendantsOfType("block_comment")) {
        if (text.startsWith("/-@", node.startIndex)) {
          folds.push({ startOffset: node.startIndex, endOffset: node.endIndex });
        }
      }
      return folds;
    } finally {
      tree.delete();
    }
  } catch (error) {
    console.warn("[booklink] leanFolds failed:", error);
    return [];
  }
}

function markdownCaptures(hl: Highlighter, text: string): Span[] {
  const blockTree = hl.mdBlock.parser.parse(text);
  try {
    const spans = toSpans(hl.mdBlock.query.captures(blockTree.rootNode));

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
function latexSpans(text: string): Span[] {
  const spans: Span[] = [];
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

function toSpans(captures: any): Span[] {
  const spans: Span[] = [];
  for (const { name, node } of captures) {
    const cls = captureClass(name);
    if (!cls) continue;
    if (node.endIndex <= node.startIndex) continue;
    spans.push({ startOffset: node.startIndex, endOffset: node.endIndex, cls });
  }
  return spans;
}

// Resolve overlapping captures to a flat, non-overlapping coloring. Innermost
// (shortest) capture wins, matching the source-map mark logic: paint longer
// captures first so shorter ones overwrite, then coalesce equal-class runs.
function flatten(spans: Span[], length: number): Span[] {
  if (!spans.length || length <= 0) return [];
  spans.sort((a, b) => b.endOffset - b.startOffset - (a.endOffset - a.startOffset));

  const paint: (string | null)[] = Array.from({ length }, () => null);
  for (const span of spans) {
    const start = Math.max(0, span.startOffset);
    const end = Math.min(length, span.endOffset);
    for (let i = start; i < end; i += 1) paint[i] = span.cls;
  }

  const segments = [];
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

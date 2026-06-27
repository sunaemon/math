// Node smoke check for the vendored tree-sitter runtime, grammars, and
// highlight queries. Run with:
//
//   node tools/formalization-viewer/check_highlights.mjs
//
// It loads the three grammars + queries the way the browser highlighter will,
// parses the Lean and Markdown fixtures, and prints capture tallies. This settles
// the web-tree-sitter 0.26 API (Parser.init / Language.load / new Query /
// included-range inline parsing) before the browser module relies on it. A
// nonzero capture count for each fixture and no query-compile error means the
// vendored assets are usable.

import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Parser, Language, Query } from "./vendor/treesitter/web-tree-sitter.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const vendor = path.join(here, "vendor", "treesitter");
const queries = path.join(vendor, "queries");
const fixtures = path.join(here, "fixtures");

const bytes = (file) => new Uint8Array(fs.readFileSync(file));
const text = (file) => fs.readFileSync(file, "utf8");

function tally(captures) {
  const counts = new Map();
  for (const { name } of captures) counts.set(name, (counts.get(name) || 0) + 1);
  return [...counts.entries()].sort((a, b) => b[1] - a[1]);
}

function report(label, captures) {
  console.log(`\n${label}: ${captures.length} captures`);
  for (const [name, count] of tally(captures)) {
    console.log(`  ${String(count).padStart(4)}  @${name}`);
  }
}

async function main() {
  await Parser.init({ locateFile: (name) => path.join(vendor, name) });

  const [lean, markdown, markdownInline] = await Promise.all([
    Language.load(bytes(path.join(vendor, "tree-sitter-lean.wasm"))),
    Language.load(bytes(path.join(vendor, "tree-sitter-markdown.wasm"))),
    Language.load(bytes(path.join(vendor, "tree-sitter-markdown_inline.wasm"))),
  ]);

  const leanQuery = new Query(lean, text(path.join(queries, "lean.scm")));
  const mdQuery = new Query(markdown, text(path.join(queries, "markdown.scm")));
  const mdInlineQuery = new Query(markdownInline, text(path.join(queries, "markdown_inline.scm")));

  // --- Lean -----------------------------------------------------------------
  const leanSrc = text(path.join(fixtures, "simple.lean"));
  const leanParser = new Parser();
  leanParser.setLanguage(lean);
  const leanTree = leanParser.parse(leanSrc);
  const leanCaptures = leanQuery.captures(leanTree.rootNode);
  report("Lean", leanCaptures);
  leanTree.delete();

  // --- Markdown (block + inline via included ranges) ------------------------
  const mdSrc = text(path.join(fixtures, "simple.md"));
  const mdParser = new Parser();
  mdParser.setLanguage(markdown);
  const blockTree = mdParser.parse(mdSrc);
  const blockCaptures = mdQuery.captures(blockTree.rootNode);

  const inlineNodes = blockTree.rootNode.descendantsOfType("inline");
  const includedRanges = inlineNodes.map((node) => ({
    startIndex: node.startIndex,
    endIndex: node.endIndex,
    startPosition: node.startPosition,
    endPosition: node.endPosition,
  }));
  console.log(`\nMarkdown inline regions: ${includedRanges.length}`);

  let inlineCaptures = [];
  if (includedRanges.length > 0) {
    const inlineParser = new Parser();
    inlineParser.setLanguage(markdownInline);
    const inlineTree = inlineParser.parse(mdSrc, null, { includedRanges });
    inlineCaptures = mdInlineQuery.captures(inlineTree.rootNode);
    inlineTree.delete();
  }
  report("Markdown block", blockCaptures);
  report("Markdown inline", inlineCaptures);
  blockTree.delete();

  // Probe whether the prebuilt markdown grammar recognizes $...$ math.
  const mathProbe = mdParser.parse("Inline math $x^2 + y^2$ end.\n");
  const hasMath = mathProbe.rootNode.descendantsOfType("inline").length > 0;
  mathProbe.delete();
  console.log(`\n$...$ math note: inline region present=${hasMath} (math styling is best-effort).`);

  // Gate: loading and compiling without error is not enough — a grammar/query
  // mismatch after a vendored-asset bump can parse cleanly yet capture nothing,
  // which silently disables highlighting in the browser. Require each fixture to
  // produce captures so that regression fails the build instead of printing OK.
  assert(leanCaptures.length > 0, "Lean fixture produced no highlight captures");
  assert(blockCaptures.length > 0, "Markdown block fixture produced no highlight captures");
  assert(inlineCaptures.length > 0, "Markdown inline fixture produced no highlight captures");

  console.log("\nOK: vendored runtime + grammars + queries loaded and parsed.");
}

main().catch((error) => {
  console.error("check_highlights failed:", error);
  process.exit(1);
});

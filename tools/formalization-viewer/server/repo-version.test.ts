import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";
import { cachedRepoVersion, katexMacros, appendVendorComponents, attachLicenseText } from "./repo-version.ts";

test("repository metadata is cached briefly, isolated by root and refreshed after expiry", () => {
  let clock = 0,
    reads = 0;
  const version = cachedRepoVersion(
    () => ({ describe: String(++reads), rev: String(reads), date: "date" }),
    () => clock,
    1000,
  );
  const first = version("repo-a");
  first.rev = "mutated by caller";
  assert.equal(version("repo-a").rev, "1");
  assert.equal(version("repo-b").rev, "2");
  clock = 1000;
  assert.equal(version("repo-a").rev, "3");
  assert.equal(reads, 3);
});

test("KaTeX macro parsing keeps escaped unmatched braces inside a definition", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "katex-braces-"));
  try {
    const file = path.join(root, "macros.tex");
    fs.writeFileSync(
      file,
      String.raw`\newcommand{\LeftOnly}{\left\{}
\newcommand{\RightOnly}{\right\}}
\newcommand{\After}[1]{{#1}}
`,
    );
    const macros = katexMacros(file);
    assert.equal(macros["\\LeftOnly"], String.raw`\left\{`);
    assert.equal(macros["\\RightOnly"], String.raw`\right\}`);
    assert.equal(macros["\\After"], "{#1}");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("viewer licenses include distributed components and omit build-only dependencies", () => {
  const root = path.resolve(import.meta.dirname, "../../..");
  for (const book of ["polish-space", "polish-space-ja", "polish-space-part1-ja"]) {
    const manifest = JSON.parse(fs.readFileSync(path.join(root, book, "manifest.json"), "utf8"));
    appendVendorComponents(root, manifest.license);
    const count = manifest.license.items.length;
    appendVendorComponents(root, manifest.license);
    assert.equal(manifest.license.items.length, count, "repeated expansion must not duplicate licenses");
    attachLicenseText(root, manifest.license);
    const items = manifest.license.items;
    for (const name of [
      "Ackerman–Freer–Knight Vaught conjecture formalization",
      "Book AFK validation adapter",
      "Manthe Borel determinacy",
      "web-tree-sitter",
      "tree-sitter-markdown",
      "tree-sitter-lean",
    ]) {
      assert.equal(
        items.some((item: any) => item.scope === name),
        false,
        `${name} is not shipped as code in the static viewer`,
      );
    }
    assert.match(items.find((item: any) => item.scope === "pdf.js").text, /Apache License/);
    assert.ok(items.some((item: any) => item.scope === "KaTeX"));
  }
});

test("vendor manifests outside the repository are not read", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "vendor-licenses-"));
  try {
    const license = { vendorManifests: ["../manifest.json"], items: [] };
    appendVendorComponents(root, license);
    assert.deepEqual(license.items, []);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("big operators retain inline and display limit placement in KaTeX", async () => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const macros = katexMacros(path.join(root, "polish-space/tex/macros.tex"));
  const katex = (await import(new URL("../vendor/katex/katex.mjs", import.meta.url).href)).default;
  for (const name of ["InternalDisjointUnion", "ExternalDisjointUnion", "DirectedSup"]) {
    const formula = `\\${name}_{i\\in I} A_i`;
    const inline = katex.renderToString(formula, { macros: { ...macros }, displayMode: false, throwOnError: true });
    const display = katex.renderToString(formula, { macros: { ...macros }, displayMode: true, throwOnError: true });
    assert.doesNotMatch(inline, /displaylimits|<munder>/);
    assert.match(inline, /<msub>/);
    assert.match(display, /<munder>/);
  }
});

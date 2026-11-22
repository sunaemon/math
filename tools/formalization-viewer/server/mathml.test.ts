import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fixedMath, renderDefinitions } from "./mathml.ts";
import { emptyDefinitionRegistry } from "../src/definition-registry.ts";

test("fixed math is cached and macro changes regenerate native MathML", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "fixed-math-"));
  try {
    fs.writeFileSync(
      path.join(root, "map.json"),
      JSON.stringify({ entries: [{ booklink: { title: "$\\X$", excerpt: "$x<y$" } }] }),
    );
    const first = fixedMath(root, "map.json", { "\\X": "x" });
    assert.match(first["\\X"], /<math/);
    assert.doesNotMatch(first["\\X"], /katex-html/);
    assert.equal(fixedMath(root, "map.json", { "\\X": "x" }), first);
    assert.notEqual(fixedMath(root, "map.json", { "\\X": "y" })["\\X"], first["\\X"]);
    const registry = emptyDefinitionRegistry();
    registry.entries.example = {
      id: "example",
      key: "example",
      kind: "term",
      label: "Example",
      chapter: "test",
      source: "Let $x<y$. <script>bad</script>",
      location: { file: "test.md", start: 0, end: 1, line: 1 },
    };
    renderDefinitions(registry, {});
    assert.match(registry.entries.example.html!, /<math/);
    assert.doesNotMatch(registry.entries.example.html!, /<script>|katex-html/);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

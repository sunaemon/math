import test from "node:test";
import assert from "node:assert/strict";
import { splitMathSource } from "./math-source.ts";
test("display equations in marker titles retain no surplus dollar delimiters", () => {
  const parts = splitMathSource(String.raw`The equation $$\evalMap\circ(\overline h\times\mathrm{id}_X)=h$$ holds`);
  assert.deepEqual(
    parts.map((p) => p.kind),
    ["text", "math", "text"],
  );
  assert.equal(parts[1].display, true);
  assert.doesNotMatch(parts[1].source, /\$/);
  assert.equal(parts[0].source, "The equation ");
  assert.equal(parts[2].source, " holds");
});
test("inline, display, escaped dollars and bracket math have distinct boundaries", () => {
  const parts = splitMathSource(String.raw`Cost \$5. $x$ and \(y\) and \[z\] and $$w$$.`);
  assert.deepEqual(
    parts.filter((p) => p.kind === "math").map((p) => [p.source, p.display]),
    [
      ["x", false],
      ["y", false],
      ["z", true],
      ["w", true],
    ],
  );
  assert.match(parts[0].source, /\\\$5/);
});

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { katexMacros } from "../server/repo-version.ts";
import { katexRenderMacros } from "./katex-compat.ts";

test("Cantor–Bendixson derivatives render default, indexed, empty and nested arguments", async () => {
  const katex = (await import(new URL("../vendor/katex/katex.mjs", import.meta.url).href)).default;
  const original = katexMacros(fileURLToPath(new URL("../../../polish-space/tex/macros.tex", import.meta.url)));
  const cases = [
    [String.raw`\cbderivative{F}`, String.raw`F'`],
    [String.raw`\cbderivative[\alpha]{F}`, String.raw`F^{(\alpha)}`],
    [String.raw`\cbderivative[]{F}`, String.raw`F'`],
    [String.raw`\cbderivative[\beta]{\cbderivative{F}}`, String.raw`F'^{(\beta)}`],
    [String.raw`\cbderivative[\alpha]{\mathcal F}`, String.raw`\mathcal F^{(\alpha)}`],
  ];
  for (const [source, expected] of cases) {
    const options = { macros: katexRenderMacros(original), throwOnError: true, output: "mathml" };
    const actual = katex.renderToString(source, options).replace(/<annotation[^]*?<\/annotation>/g, "");
    const reference = katex.renderToString(expected, options).replace(/<annotation[^]*?<\/annotation>/g, "");
    assert.equal(actual, reference, source);
  }
  assert.equal(typeof original["\\cbderivative"], "string");
});

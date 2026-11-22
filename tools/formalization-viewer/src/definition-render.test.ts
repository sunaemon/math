import test from "node:test";
import assert from "node:assert/strict";
import { definitionHtml } from "./definition-render.ts";

test("render inline and display math with the book macros, escaping source HTML", async () => {
  const url = new URL("../vendor/katex/katex.mjs", import.meta.url).href;
  const katex = (await import(url)).default;
  const html = definitionHtml(
    String.raw`Let $F\subseteq\R$ be closed. Its \termdefine{indicator function} is
$$u_F(x)=\begin{cases}1&x\in F,\\0&x\notin F.\end{cases}$$
<script>alert(1)</script>`,
    katex,
    { "\\R": "\\mathbb{R}" },
  );
  assert.match(html, /<math/);
  assert.doesNotMatch(html, /katex-html/);
  assert.match(html, /<math[^>]*display="block"/);
  assert.match(html, /<strong>indicator function<\/strong>/);
  assert.match(html, /&lt;script&gt;/);
  assert.doesNotMatch(html, /katex-error|<script>|\\termdefine/);
});

test("aliases retain nested mathematical display text", () => {
  const calls: string[] = [];
  const html = definitionHtml(
    String.raw`\termdefineas{canonical}{a $\mathbf{C}$ value}`,
    {
      renderToString: (s) => {
        calls.push(s);
        return "MATH";
      },
    },
    {},
  );
  assert.equal(html, "<strong>a MATH value</strong>");
  assert.deepEqual(calls, [String.raw`\mathbf{C}`]);
});

test("Japanese notation lists render Markdown strong text, math, and no metadata", async () => {
  const katex = (await import(new URL("../vendor/katex/katex.mjs", import.meta.url).href)).default;
  const html = definitionHtml(
    String.raw`*   **数の集合（$\NN$, $\ZZ$, $\QQ$, $\R$）．** それぞれ自然数，整数，有理数，実数を表す．
    $\NN = \{0, 1, 2, \ldots\}$ とし，$0$ を含める．
\begin{mathmeta}
\define{RestrictedSet}
\end{mathmeta}`,
    katex,
    { "\\NN": "\\mathbb{N}", "\\ZZ": "\\mathbb{Z}", "\\QQ": "\\mathbb{Q}", "\\R": "\\mathbb{R}" },
  );
  assert.match(html, /^<ul><li><strong>数の集合/);
  assert.match(html, /class="katex"/);
  assert.doesNotMatch(html, /\*\*|mathmeta|\\define|RestrictedSet|katex-error/);
});

test("section introductions render Markdown emphasis", () => {
  const html = definitionHtml("A hierarchy of *sets* and **functions**.", { renderToString: () => "" }, {});
  assert.equal(html, "A hierarchy of <em>sets</em> and <strong>functions</strong>.");
});

test("source references render their labels and aliases preserve defined-term emphasis", () => {
  const html = definitionHtml(
    String.raw`\termdefineas{Baire space}{Baire空間}．\BookSectionLink{sec:next}{次章}と§{sec:next}を参照．`,
    { renderToString: () => "" },
    {},
    { "sec:next": "Next chapter" },
  );
  assert.match(html, /<strong>Baire空間<\/strong>/);
  assert.match(html, /次章と§ Next chapter/);
  assert.doesNotMatch(html, /BookSectionLink|sec:next/);
});

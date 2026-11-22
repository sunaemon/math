import test from "node:test";
import assert from "node:assert/strict";
import { stripStatementEnvironments, openingProseClause, markerProseSource } from "./prose.ts";

test("proof labels never leak into marker titles or snippets", () => {
  for (const heading of [
    String.raw`\begin{proof}[Proof]`,
    String.raw`\begin{proof}[証明]`,
    String.raw`\begin{proof}`,
  ]) {
    const source = heading + String.raw` Given Polish spaces $(X_n)_{n\in\omega}$, choose metrics.\end{proof}`;
    assert.equal(
      stripStatementEnvironments(source),
      String.raw` Given Polish spaces $(X_n)_{n\in\omega}$, choose metrics.`,
    );
  }
});

test("statement names remain readable while mathematical environments remain intact", () => {
  const source = String.raw`\begin{lemma*}[Countable products] $\begin{aligned}x&=y\end{aligned}$\end{lemma*}`;
  assert.equal(stripStatementEnvironments(source), String.raw`Countable products.  $\begin{aligned}x&=y\end{aligned}$`);
});

test("marker clauses do not cut through inline mathematics", () => {
  const source = String.raw`Put $L_s:=(p(0),p(s-1))$, with $L_0=[]$, and continue. The next sentence.`;
  const clause = openingProseClause(source);
  assert.equal(clause, String.raw`Put $L_s:=(p(0),p(s-1))$, with $L_0=[]$, and continue`);
  assert.equal((clause.match(/\$/g) ?? []).length, 4);
  assert.equal(openingProseClause(String.raw`Let $x=0.5; y:=x$. Next.`), String.raw`Let $x=0.5; y:=x$`);
  assert.equal(openingProseClause(String.raw`Let \(x:=y\). Next.`), String.raw`Let \(x:=y\)`);
  assert.equal(openingProseClause(String.raw`Use \textbf{a: b}. Next.`), String.raw`Use \textbf{a: b}`);
});

test("marker labels remove Markdown delimiters while preserving mathematical source", () => {
  const source = String.raw`**Open sets are finitely observable properties.** If *directed* $x_i*y_j$ exists.`;
  const cleaned = markerProseSource(source);
  assert.equal(cleaned, String.raw`Open sets are finitely observable properties. If directed $x_i*y_j$ exists.`);
  assert.equal(openingProseClause(cleaned), "Open sets are finitely observable properties");
  assert.equal(markerProseSource("Use `some_identifier` and __bold__ text."), "Use some_identifier and bold text.");
});

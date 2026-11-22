import test from "node:test";
import assert from "node:assert/strict";
import { sourceExcerpt, referencedDefinitions, questionWithContext } from "./chat-context.ts";
import { emptyDefinitionRegistry } from "./definition-registry.ts";

test("selected source context preserves math, line provenance and referenced definitions", () => {
  const source = "Before\nA \\termuse{Polish space} has $x \\in X$.\nSee §{sec:metric}.\nAfter";
  const excerpt = sourceExcerpt(source, 2, 2, 1);
  assert.match(excerpt, /2: A \\termuse\{Polish space\} has \$x \\in X\$\./);
  assert.match(excerpt, /3: See/);
  const registry = emptyDefinitionRegistry();
  for (const [id, kind, key] of [
    ["term-def-polish-space", "term", "Polish space"],
    ["sec:metric", "section", "metric"],
    ["term-def-unused", "term", "unused"],
  ] as const)
    registry.entries[id] = {
      id,
      kind,
      key,
      label: key,
      chapter: "chapter",
      source: `Definition of ${key}`,
      location: { file: "src/chapter.md", start: 0, end: 10, line: 12 },
    };
  const attachments = referencedDefinitions(excerpt, registry);
  assert.equal(attachments.length, 2);
  assert.doesNotMatch(JSON.stringify(attachments), /unused/);
  const prompt = questionWithContext(
    "どういうこと？",
    { text: "選択した文章", pane: "pdf", entries: [] },
    attachments,
    "Book",
  );
  assert.match(prompt, /選択した文章/);
  assert.match(prompt, /src\/chapter.md:12/);
  assert.match(prompt, /どういうこと？/);
});
test("context extraction bounds very long source spans", () => {
  const excerpt = sourceExcerpt(Array.from({ length: 1000 }, (_, i) => String(i + 1)).join("\n"), 500, 900);
  assert.match(excerpt, /^497: /);
  assert.doesNotMatch(excerpt, /900: /);
  assert.equal(referencedDefinitions("plain text").length, 0);
});

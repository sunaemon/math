import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { runInNewContext } from "node:vm";
import { hasTranslation, preferredLanguage, t } from "./i18n.ts";

test("UI language follows the first supported browser preference with English fallback", () => {
  assert.equal(preferredLanguage(["ja-JP", "en-US"]), "ja");
  assert.equal(preferredLanguage(["en-GB", "ja"]), "en");
  assert.equal(preferredLanguage(["fr-FR", "JA_jp"]), "ja");
  assert.equal(preferredLanguage(["de", "fr"]), "en");
  assert.equal(preferredLanguage([]), "en");
});

test("UI interpolation preserves external content", () => {
  const source = "<b>本文 & code</b>";
  assert.ok(t("Definition of {0}", source).includes(source));
  assert.equal(t(source), source);
});

test("literal UI messages are registered in the bilingual catalog", () => {
  const source = new URL("./", import.meta.url);
  const missing: string[] = [];
  function check(message: string, file: string, contents: string, index: number): void {
    if (hasTranslation(message)) return;
    const line = contents.slice(0, index).split("\n").length;
    missing.push(`${file}:${line}: ${JSON.stringify(message)}`);
  }

  // UI literals are passed directly to t(), including inside HTML templates.
  // Translate each branch at its source so conditional labels are checked too.
  // Dynamic inputs such as server errors may intentionally fall back to the original.
  const calls =
    /(?<![\w$.])t\(\s*("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|`(?:\\[\s\S]|\$(?!\{)|[^`\\$])*`)\s*(?=[,)])/g;
  for (const file of readdirSync(source).sort()) {
    if (!file.endsWith(".ts") || file.endsWith(".test.ts")) continue;
    const contents = readFileSync(new URL(file, source), "utf8");
    for (const match of contents.matchAll(calls)) {
      // The capture is a single JS string token, with interpolation excluded.
      check(runInNewContext(match[1]), file, contents, match.index);
    }
  }

  const html = readFileSync(new URL("../index.html", source), "utf8");
  for (const match of html.matchAll(/\bdata-ui-(?:text|title|placeholder|aria-label)="([^"]*)"/g)) {
    const message = match[1].replace(/&amp;/g, "&");
    check(message, "index.html", html, match.index);
  }
  assert.deepEqual(missing, [], `Unregistered UI messages:\n${missing.join("\n")}`);
});

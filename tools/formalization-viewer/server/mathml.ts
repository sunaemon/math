import fs from "node:fs";
import path from "node:path";
import { splitMathSource } from "../src/math-source.ts";
import { katexRenderMacros } from "../src/katex-compat.ts";
import { definitionHtml } from "../src/definition-render.ts";
import type { DefinitionRegistry } from "../src/definition-registry.ts";
import { inputStamp } from "./input-stamp.ts";
const katex = (await import(new URL("../vendor/katex/katex.mjs", import.meta.url).href)).default;

export function previewHtml(source: string, macros: Record<string, string>): string {
  return definitionHtml(source, katex, katexRenderMacros(macros));
}

export function renderDefinitions(registry: DefinitionRegistry, macros: Record<string, string>): void {
  const references = Object.fromEntries(
    Object.values(registry.entries)
      .filter((e) => e.kind === "section")
      .map((e) => [e.id, e.label]),
  );
  for (const entry of Object.values(registry.entries))
    entry.html = definitionHtml(entry.source, katex, katexRenderMacros(macros), references);
}
const cache = new Map<string, { stamp: string; math: Record<string, string> }>();
export function fixedMath(root: string, sourceMap: string, macros: Record<string, string>): Record<string, string> {
  const file = path.join(root, sourceMap);
  const stamp = inputStamp([file]) + JSON.stringify(macros);
  if (cache.get(file)?.stamp === stamp) return cache.get(file)!.math;
  const math: Record<string, string> = Object.create(null);
  if (fs.existsSync(file)) {
    const map = JSON.parse(fs.readFileSync(file, "utf8"));
    for (const entry of map.entries ?? []) {
      for (const source of [entry.booklink?.title, entry.booklink?.excerpt]) {
        for (const part of splitMathSource(String(source ?? ""))) {
          if (part.kind === "math" && !Object.hasOwn(math, part.source))
            math[part.source] = katex.renderToString(part.source, {
              macros: katexRenderMacros(macros),
              output: "mathml",
              displayMode: false,
              throwOnError: false,
              trust: false,
              strict: "ignore",
            });
        }
      }
    }
  }
  cache.set(file, { stamp, math });
  return math;
}

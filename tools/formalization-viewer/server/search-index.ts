import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { bookInputFiles, inputStamp } from "./input-stamp.ts";
import { resolveWithinRoot, macrosTexPath, katexMacros } from "./repo-version.ts";
import { previewHtml } from "./mathml.ts";
import type { Manifest } from "./projects.ts";

const VERSION = "pagefind-1.6.0-v5";
export interface SearchRecord {
  source: string;
  line: number;
  title: string;
  text: string;
  language: string;
}
export function searchText(source: string, macros: Record<string, string> = {}): string {
  return previewHtml(source.replace(/\\(?:begin|end)\{[^}]+\}/g, " "), macros)
    .replace(/<annotation\b[^]*?<\/annotation>/g, "")
    .replace(/<[^>]*>/g, " ")
    .replace(/&#(?:x([0-9a-f]+)|(\d+));/gi, (_, hex, dec) => String.fromCodePoint(parseInt(hex ?? dec, hex ? 16 : 10)))
    .replace(
      /&(amp|lt|gt|quot|apos|nbsp);/g,
      (_, key: string) => ({ amp: "&", lt: "<", gt: ">", quot: '"', apos: "'", nbsp: " " })[key]!,
    )
    .replace(/\s+/g, " ")
    .trim();
}
export function searchRecords(source: string, text: string, macros: Record<string, string> = {}): SearchRecord[] {
  // Retain newlines so results point into committed or generated book sources.
  const visible = text
    .replace(/<!--[^]*?(?:-->|$)/g, (value) => value.replace(/[^\n]/g, " "))
    .replace(/\\begin\{mathmeta\}[^]*?\\end\{mathmeta\}/g, (value) => value.replace(/[^\n]/g, " "));
  const language = /[\u3040-\u30ff]/.test(visible) ? "ja" : "en";
  const headings = [...visible.matchAll(/^#{1,6}\s+(.+)$/gm)];
  const records: SearchRecord[] = [];
  for (const match of visible.matchAll(/\S[^]*?(?=\n[ \t]*\n|$)/g)) {
    const body = match[0];
    const content = searchText(body.replace(/\{#[^}]+\}/g, ""), macros);
    if (content.length < 2 || /^---$/.test(content)) continue;
    const heading = headings.findLast((h) => h.index! <= match.index!)?.[1] ?? path.basename(source, ".md");
    records.push({
      source,
      line: visible.slice(0, match.index).split("\n").length,
      title: searchText(heading.replace(/\{#[^}]+\}/g, ""), macros),
      text: content,
      language,
    });
  }
  return records;
}
const pending = new Map<string, Promise<string | null>>();
export async function ensureSearchIndex(root: string, project: Manifest): Promise<string | null> {
  root = fs.realpathSync(root);
  const inputs = bookInputFiles(root, project);
  if (!inputs) return null;
  // Fail closed for manifests escaping the checkout, including symlinks.
  for (const file of [inputs.manifest, ...inputs.chapters]) {
    if (!resolveWithinRoot(root, path.relative(root, file))) throw new Error("Search source is outside the repository");
  }
  const macrosFile = macrosTexPath(root, project.dir);
  const stamp = createHash("sha256")
    .update(VERSION + inputStamp([inputs.manifest, ...inputs.chapters, macrosFile]))
    .digest("hex");
  const output = path.join(root, project.dir, "build", "search-index", stamp.slice(0, 16));
  if (fs.existsSync(path.join(output, "pagefind.js"))) return output;
  let building = pending.get(output);
  if (!building) {
    building = (async () => {
      const pagefind = await import("pagefind");
      const { index, errors } = await pagefind.createIndex();
      if (!index || errors.length) throw new Error(`Search indexing failed: ${errors.join("; ")}`);
      try {
        const macros = katexMacros(macrosFile);
        for (const file of inputs.chapters) {
          const source = path.relative(root, file).split(path.sep).join("/");
          for (const record of searchRecords(source, fs.readFileSync(file, "utf8"), macros)) {
            const params = new URLSearchParams({ searchSource: record.source, searchLine: String(record.line) });
            const result = await index.addCustomRecord({
              url: `./?${params}`,
              content: record.text,
              language: record.language,
              meta: { title: record.title, source: record.source, line: String(record.line) },
            });
            if (result.errors.length) throw new Error(result.errors.join("; "));
          }
        }
        const stage = `${output}.tmp-${process.pid}`;
        const written = await index.writeFiles({ outputPath: stage });
        if (written.errors.length) throw new Error(written.errors.join("; "));
        // The pinned engine creates one worker. Route that URL through the
        // app's narrowly allowlisted policy; never introduce a default policy.
        const enginePath = path.join(stage, "pagefind.js");
        const engine = fs.readFileSync(enginePath, "utf8");
        const worker = "new Worker(workerUrl)";
        if (engine.split(worker).length !== 2) throw new Error("Pagefind worker adapter needs review");
        fs.writeFileSync(
          enginePath,
          'import { trustedScriptURL } from "../build/safe-script-url.js";\n' +
            engine.replace(worker, "new Worker(trustedScriptURL(workerUrl))"),
        );
        fs.mkdirSync(path.dirname(output), { recursive: true });
        try {
          fs.renameSync(stage, output);
        } catch (error) {
          if (!fs.existsSync(path.join(output, "pagefind.js"))) throw error;
          fs.rmSync(stage, { recursive: true, force: true });
        }
        return output;
      } finally {
        await index.deleteIndex();
      }
    })();
    pending.set(output, building);
    void building.finally(() => pending.delete(output)).catch(() => {});
  }
  return building;
}

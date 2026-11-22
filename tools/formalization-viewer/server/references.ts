import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { referenceUrl, type ReferenceRegistry } from "../src/link-preview.ts";
import { inputStamp } from "./input-stamp.ts";
import { resolveWithinRoot, macrosTexPath, katexMacros } from "./repo-version.ts";
import { previewHtml } from "./mathml.ts";
import type { Manifest } from "./projects.ts";

const cache = new Map<string, { stamp: string; registry: ReferenceRegistry }>();

export function bookReferences(root: string, project: Manifest): ReferenceRegistry {
  const empty = (): ReferenceRegistry => ({ entries: {}, urls: {} });
  try {
    if (typeof project.bookManifest !== "string") return empty();
    const manifest = resolveWithinRoot(root, path.join(project.dir, project.bookManifest));
    if (!manifest) return empty();
    const source = JSON.parse(fs.readFileSync(manifest, "utf8")).source;
    if (typeof source !== "string") return empty();
    const master = resolveWithinRoot(root, source);
    if (!master) return empty();
    const bibliography = /^bibliography:\s*["']?([^\n"']+)["']?\s*$/m
      .exec(fs.readFileSync(master, "utf8"))?.[1]
      ?.trim();
    if (!bibliography) return empty();
    const file = resolveWithinRoot(root, bibliography);
    if (!file) return empty();
    const macrosFile = macrosTexPath(root, project.dir);
    const stamp = inputStamp([file, macrosFile]);
    const key = `${file}\0${macrosFile}`;
    const existing = cache.get(key);
    if (existing?.stamp === stamp) return existing.registry;
    // Pandoc is the book's bibliography parser too: preserve BibTeX braces,
    // Unicode names and math instead of maintaining a second BibTeX grammar.
    const records = JSON.parse(
      execFileSync("pandoc", ["-f", "biblatex", "-t", "csljson", file], {
        encoding: "utf8",
        timeout: 10000,
        maxBuffer: 8 * 1024 * 1024,
      }),
    );
    const registry = empty();
    const macros = katexMacros(macrosFile);
    for (const record of records) {
      if (typeof record.id !== "string") continue;
      const names = (record.author ?? record.editor ?? [])
        .map(
          (person: any) =>
            person.literal ??
            [person.given, person["non-dropping-particle"], person["dropping-particle"], person.family]
              .filter(Boolean)
              .join(" "),
        )
        .join(", ");
      const year = record.issued?.["date-parts"]?.[0]?.[0];
      const publication = record["container-title"] ?? record.publisher ?? "";
      const details = [record.volume, record.issue ? `(${record.issue})` : "", record.page ? `pp. ${record.page}` : ""]
        .filter(Boolean)
        .join(" ");
      const title = String(record.title ?? record.id);
      const text = [names, year ? `(${year})` : "", title, publication, details].filter(Boolean).join(". ");
      registry.entries[record.id] = { key: record.id, title, source: text, html: previewHtml(text, macros) };
      for (const url of [record.URL, record.DOI ? `https://doi.org/${record.DOI}` : null]) {
        if (typeof url !== "string") continue;
        const normalized = referenceUrl(url);
        if (normalized) registry.urls[normalized] = record.id;
      }
    }
    cache.set(key, { stamp, registry });
    return registry;
  } catch {
    // Bibliographic previews are auxiliary; PDF navigation still works when
    // a fresh checkout has no bibliography/toolchain yet.
    return empty();
  }
}

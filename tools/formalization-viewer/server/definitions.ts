import { renderDefinitions } from "./mathml.ts";
import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import type { Manifest } from "./projects.ts";
import { emptyDefinitionRegistry, type DefinitionRegistry } from "../src/definition-registry.ts";
import { katexMacros, macrosTexPath } from "./repo-version.ts";
import { argument, collectDefinitions, collectUses, type BookSource } from "./definition-source.ts";
import { bookInputFiles, inputStamp } from "./input-stamp.ts";

// The aliases translate PDF transport destinations, never redefine source
// identities. Section and term/notation records remain in separate namespaces.
export function sectionAliases(aux: string, registry: DefinitionRegistry): void {
  for (const match of aux.matchAll(/\\newlabel(?=\{)/g)) {
    const label = argument(aux, match.index! + match[0].length);
    if (!label || registry.entries[label.value]?.kind !== "section") continue;
    const payload = argument(aux, label.end);
    if (!payload) continue;
    let offset = 0;
    const fields: string[] = [];
    while (offset < payload.value.length) {
      const field = argument(payload.value, offset);
      if (!field) break;
      fields.push(field.value);
      offset = field.end;
    }
    if (fields[3]) registry.aliases[fields[3]] = label.value;
  }
}

// The registry is a pure function of the book manifest, its chapter
// sources, the KaTeX macros file and the PDF aux files the section aliases
// come from. Manifest requests arrive on every tab load and reconnect, so
// the build is memoized on a stamp of those inputs (see input-stamp.ts)
// instead of re-reading and re-scanning every chapter each time; any input
// changing — a chapter edit, a fresh aux after a PDF build — rebuilds.
const registryCache = new Map<string, { stamp: string; registry: DefinitionRegistry }>();

export function bookDefinitionRegistry(root: string, project: Manifest): DefinitionRegistry {
  const inputs = bookInputFiles(root, project);
  let stamp: string | null = null;
  const key = `${root}\0${project.dir}\0${String(project.bookManifest ?? "")}`;
  if (inputs) {
    const auxFiles = [
      path.join(root, project.dir, "build", path.basename(String(project.pdf ?? ""), ".pdf") + ".aux"),
      ...inputs.chapters.map((chapter) =>
        path.join(root, project.dir, "build", path.basename(chapter, ".md") + ".aux"),
      ),
    ];
    stamp = inputStamp([inputs.manifest, ...inputs.chapters, macrosTexPath(root, project.dir), ...auxFiles]);
    const cached = registryCache.get(key);
    if (cached && cached.stamp === stamp) return cached.registry;
  }
  const registry = buildBookDefinitionRegistry(root, project);
  if (stamp !== null) registryCache.set(key, { stamp, registry });
  return registry;
}

function buildBookDefinitionRegistry(root: string, project: Manifest): DefinitionRegistry {
  const registry = emptyDefinitionRegistry();
  const within = (file: string) => {
    const real = fs.realpathSync(file);
    const rel = path.relative(root, real);
    if (rel.startsWith("..") || path.isAbsolute(rel)) throw new Error("Source outside repository");
    return real;
  };
  if (typeof project.bookManifest !== "string" || !project.bookManifest) return registry;
  const sources: BookSource[] = [];
  try {
    const file = within(path.resolve(root, project.dir, project.bookManifest));
    const chapters: unknown = JSON.parse(fs.readFileSync(file, "utf8")).chapters;
    if (!Array.isArray(chapters)) throw new Error("Book manifest has no chapter list");
    for (const chapter of chapters) {
      if (typeof chapter !== "string" || !chapter.endsWith(".md")) continue;
      try {
        const file = within(path.resolve(root, chapter));
        sources.push({ file: chapter, chapter: path.basename(chapter, ".md"), text: fs.readFileSync(file, "utf8") });
      } catch (error) {
        registry.diagnostics.push({ code: "unreadable-source", message: String(error), file: chapter, line: 1 });
      }
    }
    for (const source of sources)
      registry.sourceHashes[source.file] = createHash("sha256").update(source.text).digest("hex");
    collectDefinitions(sources, registry, katexMacros(macrosTexPath(root, project.dir)));
    // Preview builds keep per-chapter aux files. Full builds use a single aux.
    const auxFiles = [
      path.join(root, project.dir, "build", path.basename(String(project.pdf ?? ""), ".pdf") + ".aux"),
      ...sources.map((source) => path.join(root, project.dir, "build", source.chapter + ".aux")),
    ];
    for (const aux of auxFiles) {
      try {
        sectionAliases(fs.readFileSync(within(aux), "utf8"), registry);
      } catch {
        /* PDF aliases are optional before rendering. */
      }
    }
    collectUses(sources, registry);
  } catch (error) {
    registry.diagnostics.push({
      code: "unreadable-source",
      message: String(error),
      file: String(project.bookManifest),
      line: 1,
    });
  }
  renderDefinitions(registry, katexMacros(macrosTexPath(root, project.dir)));
  return registry;
}

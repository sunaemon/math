import type {
  DefinitionEntry,
  DefinitionLocation,
  DefinitionRegistry,
  DefinitionUse,
} from "../src/definition-registry.ts";

export interface BookSource {
  file: string;
  chapter: string;
  text: string;
}
interface Range {
  start: number;
  end: number;
}
interface ChapterSource extends BookSource {
  active: string;
  prose: string;
  math: Range[];
  metadata: Range[];
  uses: Array<{ name: string; at: number }>;
  types: Array<{ operation: string; type: string; name: string; at: number }>;
  variables: Array<{ names: string[]; type: string; at: number }>;
}

// Mask, rather than delete, non-prose so every recorded offset remains an exact
// location in the committed English or generated Japanese source.
const blank = (s: string) => s.replace(/[^\n]/g, " ");
export function activeSource(text: string): string {
  return text
    .replace(/<!--[^]*?(?:-->|$)/g, blank)
    .replace(/^([ \t]*)(`{3,}|~{3,})[^\n]*\n[^]*?^\1\2[^\n]*(?:\n|$)/gm, blank)
    .replace(/(`+)[^\n]*?\1/g, blank)
    .replace(/(^|[^\\])%[^\n]*/gm, (s, before: string) => before + blank(s.slice(before.length)));
}
export function argument(text: string, start: number): { value: string; end: number } | null {
  while (/\s/.test(text[start] ?? "") && start < text.length) start++;
  if (text[start] !== "{") return null;
  let depth = 1;
  for (let i = start + 1; i < text.length; i++) {
    if (text[i] === "\\") {
      i++;
      continue;
    }
    if (text[i] === "{") depth++;
    if (text[i] === "}" && --depth === 0) return { value: text.slice(start + 1, i), end: i + 1 };
  }
  return null;
}
export function termSlug(key: string): string {
  let base = key.split("!")[0].split("@")[0].trim();
  if (/[$\\]/.test(base)) base = base.replace(/[$\\{}_^]/g, "").trim();
  return [...base.toLowerCase()].map((c) => (/[a-z0-9\p{Nd}]/u.test(c) ? c : "-")).join("");
}
function prepare(source: BookSource): ChapterSource {
  const active = activeSource(source.text);
  const metadata = [...active.matchAll(/\\begin\{mathmeta\}[^]*?\\end\{mathmeta\}/g)].map((m) => ({
    start: m.index!,
    end: m.index! + m[0].length,
  }));
  let prose = active;
  for (const range of metadata)
    prose = prose.slice(0, range.start) + blank(prose.slice(range.start, range.end)) + prose.slice(range.end);
  const math: Range[] = [];
  const delimiters = /\$\$?|\\\[|\\\(/g;
  let m: RegExpExecArray | null;
  while ((m = delimiters.exec(prose))) {
    if (m.index > 0 && prose[m.index - 1] === "\\") continue;
    const close = m[0] === "\\[" ? "\\]" : m[0] === "\\(" ? "\\)" : m[0];
    let end = prose.indexOf(close, delimiters.lastIndex);
    while (end >= 0 && close[0] !== "\\" && prose[end - 1] === "\\") end = prose.indexOf(close, end + close.length);
    if (end < 0) continue;
    math.push({ start: m.index, end: end + close.length });
    delimiters.lastIndex = end + close.length;
  }
  const uses = [...prose.matchAll(/\\([A-Za-z]+)/g)]
    .filter((m) => math.some((r) => m.index! >= r.start && m.index! < r.end))
    .map((m) => ({ name: m[1], at: m.index! }));
  const types = [...active.matchAll(/\\notationtype\{\\([A-Za-z]+)\}\{([^}]+)\}\{\\?([A-Za-z]+)\}/g)].map((m) => ({
    operation: m[1],
    type: m[2],
    name: m[3],
    at: m.index!,
  }));
  const variables = [...active.matchAll(/\\vars\{([^}]+)\}\{([^}]+)\}/g)].map((m) => ({
    names: m[1].split(",").map((s) => s.trim()),
    type: m[2],
    at: m.index!,
  }));
  return { ...source, active, prose, math, metadata, uses, types, variables };
}
function location(source: ChapterSource, range: Range): DefinitionLocation {
  return { file: source.file, ...range, line: source.text.slice(0, range.start).split("\n").length };
}
function clean(text: string): string {
  return text
    .replace(/\\begin\{mathmeta\}[^]*?\\end\{mathmeta\}/g, "")
    .replace(/<!--[^]*?-->/g, "")
    .trim();
}
function blockAt(source: ChapterSource, at: number): Range {
  const { prose } = source;
  const stack: Array<{ name: string; start: number; content: number }> = [];
  const containers: Range[] = [];
  for (const m of prose.matchAll(
    /\\(begin|end)\{((?:definition|example|theorem|lemma|proposition|corollary|remark|construction|claim|fact|recall|statement)\*?)\}/g,
  )) {
    if (source.math.some((r) => m.index! >= r.start && m.index! < r.end)) continue;
    if (m[1] === "begin") {
      let content = m.index! + m[0].length;
      if (prose[content] === "[") {
        let depth = 0;
        for (let i = content; i < prose.length; i++) {
          if (prose[i] === "{") depth++;
          if (prose[i] === "}") depth--;
          if (prose[i] === "]" && depth === 0) {
            content = i + 1;
            break;
          }
        }
      }
      stack.push({ name: m[2], start: m.index!, content });
    } else {
      const opening = stack.at(-1);
      if (!opening || opening.name !== m[2]) continue;
      stack.pop();
      if (at >= opening.start && at < m.index!) containers.push({ start: opening.content, end: m.index! });
    }
  }
  if (containers.length) return containers.sort((a, b) => a.end - a.start - (b.end - b.start))[0];
  // Paragraph/list boundaries inside displayed mathematics are not boundaries.
  const boundaries = [...prose.matchAll(/\n[ \t]*\n|^#{1,6} .*$|^[ \t]*[-*+]\s+/gm)].filter(
    (m) => !source.math.some((r) => m.index! > r.start && m.index! < r.end),
  );
  let start = 0,
    end = prose.length;
  for (const m of boundaries) {
    if (m.index! <= at) start = m[0].includes("\n") || m[0].startsWith("#") ? m.index! + m[0].length : m.index!;
    else {
      end = m.index!;
      break;
    }
  }
  // Include a display separated from its introductory paragraph by a blank line.
  while (end < prose.length) {
    const next = end + (prose.slice(end).match(/^\s*/)?.[0].length ?? 0);
    const display = source.math.find(
      (r) => r.start === next && (prose.startsWith("$$", next) || prose.startsWith("\\[", next)),
    );
    if (!display) break;
    end = boundaries.find((m) => m.index! >= display.end)?.index ?? prose.length;
  }
  return { start, end };
}
function insert(registry: DefinitionRegistry, entry: DefinitionEntry): void {
  const existing = registry.entries[entry.id];
  if (existing) {
    // Repeated definitions of the same canonical term retain the first anchor,
    // matching book-filter. Different identities must never silently collide.
    if (existing.key !== entry.key)
      registry.diagnostics.push({
        code: "identity-collision",
        message: `${existing.key} and ${entry.key} share ${entry.id}`,
        file: entry.location.file,
        line: entry.location.line,
      });
    return;
  }
  registry.entries[entry.id] = entry;
  if (entry.kind !== "section") registry.aliases[entry.id.replace("-def-", "-index-")] = entry.id;
}
function typedUse(source: ChapterSource, operation: string, name: string, at: number): boolean {
  const matching = source.types.filter(
    (binding) => binding.at < at && binding.operation === operation && binding.name === name,
  );
  if (!matching.length) return false;
  const left = source.prose
    .slice(0, at)
    .match(/(\\[A-Za-z]+|[A-Za-z][A-Za-z0-9]*(?:_\{[^}]+\}|_[A-Za-z0-9]+)?)\s*$/)?.[1];
  const right = argument(source.prose, at + operation.length + 1)?.value;
  for (const owner of [left, right]) {
    if (!owner) continue;
    const type = source.variables.filter((binding) => binding.at < at && binding.names.includes(owner)).at(-1)?.type;
    if (matching.some((binding) => binding.type === type)) return true;
  }
  return false;
}

export function collectDefinitions(
  sources: BookSource[],
  registry: DefinitionRegistry,
  macros: Record<string, string> = {},
): void {
  const chapters = sources.map(prepare);
  // Pass one: actual term definitions and headings, with exact provenance.
  for (const chapter of chapters) {
    const headings = [...chapter.prose.matchAll(/^#{1,6}\s+(.+?)\s*\{#([^}\s]+)[^}]*\}[^\n]*$/gm)];
    for (let i = 0; i < headings.length; i++) {
      const h = headings[i];
      let start = h.index! + h[0].length;
      start += chapter.prose.slice(start).match(/^\s*/)?.[0].length ?? 0;
      const limit = headings[i + 1]?.index ?? chapter.prose.length;
      const range = start < limit ? blockAt(chapter, start) : { start, end: start };
      insert(registry, {
        id: h[2],
        key: h[2],
        kind: "section",
        label: h[1],
        chapter: chapter.chapter,
        source: `**${h[1]}**\n\n${clean(chapter.prose.slice(start, Math.min(range.end, limit)))}`,
        location: location(chapter, { start: h.index!, end: Math.min(range.end, limit) }),
      });
    }
    for (const m of chapter.prose.matchAll(/\\termdefine(?:as)?(?=\s*\{)/g)) {
      const key = argument(chapter.prose, m.index! + m[0].length);
      if (!key) continue;
      const display = m[0].endsWith("as") ? (argument(chapter.prose, key.end)?.value ?? key.value) : key.value;
      const range = blockAt(chapter, m.index!);
      insert(registry, {
        id: `term-def-${termSlug(key.value)}`,
        key: key.value,
        kind: "term",
        label: display,
        chapter: chapter.chapter,
        source: clean(chapter.prose.slice(range.start, range.end)),
        location: location(chapter, range),
        declaration: location(chapter, { start: m.index!, end: key.end }),
      });
    }
  }
  // Pass two: \define opens the first-use gate; it is NOT a prose definition.
  // Bind each name independently to its first mathematical use after the gate.
  for (let index = 0; index < chapters.length; index++) {
    const chapter = chapters[index];
    for (const metadata of chapter.metadata) {
      const content = chapter.active.slice(metadata.start, metadata.end);
      for (const m of content.matchAll(/\\define\{([^}]+)\}/g))
        for (const name of m[1].split(",").map((s) => s.trim())) {
          if (registry.entries[`notation-def-${name}`]) continue;
          const declaration = location(chapter, {
            start: metadata.start + m.index!,
            end: metadata.start + m.index! + m[0].length,
          });
          let found = false;
          for (let ci = index; ci < chapters.length && !found; ci++) {
            const target = chapters[ci];
            const offset = ci === index ? metadata.end : 0;
            const use = target.uses.find(
              (use) =>
                use.at >= offset &&
                (use.name === name ||
                  typedUse(target, use.name, name, use.at) ||
                  (m[1]
                    .split(",")
                    .map((s) => s.trim())
                    .includes(use.name) &&
                    (macros[`\\${use.name}`] ?? "").replace(/#[0-9]|[{}\s]/g, "") === `\\${name}`)),
            );
            if (!use) continue;
            const range = blockAt(target, use.at);
            const terms = Object.values(registry.entries).filter(
              (e) =>
                e.kind === "term" &&
                e.location.file === target.file &&
                e.location.start === range.start &&
                e.location.end === range.end,
            );
            const term =
              terms.length === 1
                ? terms[0]
                : terms
                    .filter((entry) => (entry.declaration?.start ?? Infinity) <= use.at)
                    .sort((a, b) => (b.declaration?.start ?? 0) - (a.declaration?.start ?? 0))[0];
            insert(registry, {
              id: `notation-def-${name}`,
              key: name,
              kind: "notation",
              label: `$\\${name}$`,
              chapter: target.chapter,
              source: clean(target.prose.slice(range.start, range.end)),
              location: location(target, range),
              declaration,
              ...(term ? { canonicalDefinition: term.id } : {}),
            });
            found = true;
          }
          if (!found)
            registry.diagnostics.push({
              code: "missing-notation-target",
              message: `No mathematical use after \\define{${name}}`,
              file: chapter.file,
              line: declaration.line,
            });
        }
    }
  }
}

// Invert \termuse / \termforward and §{...} references into per-entry usedBy
// lists, so a definition or section preview can show where the book uses the
// entry. Runs after collectDefinitions (and, in definitions.ts, after the aux
// section aliases are merged) because § references resolve through the same
// aliases as resolveDefinition. A use inside the entry's own defining block
// is not a self-reference worth listing, and repeated uses inside one block
// collapse into a single item, in reading order.
export function collectUses(sources: BookSource[], registry: DefinitionRegistry): void {
  const chapters = sources.map(prepare);
  const seen = new Map<string, Set<string>>();
  const addUse = (entry: DefinitionEntry, chapter: ChapterSource, at: number, section?: string): void => {
    if (entry.location.file === chapter.file && at >= entry.location.start && at < entry.location.end) return;
    const range = blockAt(chapter, at);
    const key = `${chapter.file}:${range.start}`;
    let blocks = seen.get(entry.id);
    if (!blocks) seen.set(entry.id, (blocks = new Set()));
    if (blocks.has(key)) return;
    blocks.add(key);
    const uses = (entry.usedBy ??= []);
    if (uses.length >= 100) return;
    const use: DefinitionUse = {
      file: chapter.file,
      line: location(chapter, { start: at, end: at }).line,
      chapter: chapter.chapter,
      ...(section ? { section } : {}),
      excerpt: clean(chapter.prose.slice(range.start, range.end)).replace(/\s+/g, " ").slice(0, 160),
    };
    uses.push(use);
  };
  for (const chapter of chapters) {
    const headings = [...chapter.prose.matchAll(/^#{1,6}\s+(.+?)\s*\{#([^}\s]+)[^}]*\}[^\n]*$/gm)];
    const enclosing = (at: number): string | undefined => {
      let label: string | undefined;
      for (const h of headings) {
        if (h.index! > at) break;
        label = h[1];
      }
      return label;
    };
    for (const m of chapter.prose.matchAll(/\\term(?:use|forward)(?:as)?(?=\s*\{)/g)) {
      const key = argument(chapter.prose, m.index! + m[0].length);
      if (!key) continue;
      const entry = registry.entries[`term-def-${termSlug(key.value)}`];
      if (entry) addUse(entry, chapter, m.index!, enclosing(m.index!));
    }
    for (const m of chapter.prose.matchAll(/§\{([^}]+)\}/g)) {
      const entry = registry.entries[registry.aliases[m[1]] ?? m[1]];
      if (entry?.kind === "section") addUse(entry, chapter, m.index!, enclosing(m.index!));
    }
  }
}

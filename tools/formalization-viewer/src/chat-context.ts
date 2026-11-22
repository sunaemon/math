import type { DefinitionRegistry } from "./definition-registry.js";
export interface ChatAttachment {
  label: string;
  text: string;
}
export interface ChatSelection {
  text: string;
  pane: string;
  entries: number[];
  file?: string;
  startLine?: number;
  endLine?: number;
}
export function sourceExcerpt(text: string, startLine: number, endLine: number, padding = 3): string {
  const lines = text.split("\n");
  const start = Math.max(1, startLine - padding);
  const end = Math.min(lines.length, Math.max(startLine, Math.min(endLine, startLine + 100)) + padding);
  return lines
    .slice(start - 1, end)
    .map((line, index) => `${start + index}: ${line}`)
    .join("\n")
    .slice(0, 10000);
}
// Resolve only references actually present in the excerpt. No book-wide scan or
// unrelated active marker is attached to a selection in an unlinked passage.
export function referencedDefinitions(text: string, registry?: DefinitionRegistry): ChatAttachment[] {
  if (!registry) return [];
  const terms = new Set([...text.matchAll(/\\term(?:use|forward|define)(?:as)?\{([^}]+)\}/g)].map((m) => m[1]));
  const sections = new Set([...text.matchAll(/§\{([^}]+)\}/g)].map((m) => m[1]));
  const macros = new Set([...text.matchAll(/\\([A-Za-z]+)/g)].map((m) => m[1]));
  const found: ChatAttachment[] = [];
  let budget = 10000;
  for (const entry of Object.values(registry.entries)) {
    if (
      !(entry.kind === "term" && terms.has(entry.key)) &&
      !(entry.kind === "section" && sections.has(entry.id)) &&
      !(entry.kind === "notation" && macros.has(entry.key.replace(/^\\/, "")))
    )
      continue;
    const body = entry.source.slice(0, Math.min(2500, budget));
    if (!body) break;
    found.push({ label: `${entry.label} — ${entry.location.file}:${entry.location.line}`, text: body });
    budget -= body.length;
    if (budget <= 0 || found.length >= 8) break;
  }
  return found;
}
export function questionWithContext(
  question: string,
  selection: ChatSelection,
  attachments: ChatAttachment[],
  book: string,
): string {
  return `Book: ${book}\nSelected in: ${selection.pane}\n\n<selected_passage>\n${selection.text}\n</selected_passage>\n\n${attachments.map((item) => `<source_context label=${JSON.stringify(item.label)}>\n${item.text}\n</source_context>`).join("\n\n")}\n\nQuestion:\n${question}`;
}

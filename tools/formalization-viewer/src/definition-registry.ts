// Canonical definition identities and source locations shared by live/static
// manifests, PDF hover/navigation, and source links. Offsets use JS UTF-16.
export type DefinitionKind = "term" | "notation" | "section";
export interface DefinitionLocation {
  file: string;
  start: number;
  end: number;
  line: number;
}
// One place a term or section is used: the block containing a \termuse or a
// §{...} reference, collected by the server build (collectUses). The excerpt
// is the block's plain source text, whitespace-collapsed and truncated.
export interface DefinitionUse {
  file: string;
  line: number;
  chapter: string;
  section?: string;
  excerpt: string;
}
export interface DefinitionEntry {
  id: string;
  key: string;
  kind: DefinitionKind;
  label: string;
  chapter: string;
  source: string;
  html?: string;
  location: DefinitionLocation;
  declaration?: DefinitionLocation;
  canonicalDefinition?: string;
  usedBy?: DefinitionUse[];
}
export interface DefinitionDiagnostic {
  code: "missing-notation-target" | "identity-collision" | "unreadable-source";
  message: string;
  file: string;
  line: number;
}
export interface DefinitionRegistry {
  version: 1;
  offsetSpace: "utf16";
  sourceHashes: Record<string, string>;
  entries: Record<string, DefinitionEntry>;
  aliases: Record<string, string>;
  diagnostics: DefinitionDiagnostic[];
}
export function emptyDefinitionRegistry(): DefinitionRegistry {
  return { version: 1, offsetSpace: "utf16", sourceHashes: {}, entries: {}, aliases: {}, diagnostics: [] };
}
export function resolveDefinition(
  registry: DefinitionRegistry | undefined,
  destination: unknown,
): DefinitionEntry | null {
  if (!registry || typeof destination !== "string") return null;
  const id = registry.aliases[destination] ?? destination;
  return registry.entries[id] ?? null;
}

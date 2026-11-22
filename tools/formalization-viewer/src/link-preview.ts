export interface ReferencePreview {
  key: string;
  title: string;
  source: string;
  html?: string;
}
export interface ReferenceRegistry {
  entries: Record<string, ReferencePreview>;
  urls: Record<string, string>;
}

export function referenceKey(destination: unknown): string | null {
  if (typeof destination !== "string") return null;
  return /^(?:cite\.[^@]*@)?ref-(.+)$/.exec(destination)?.[1] ?? null;
}

export function referenceUrl(value: string): string {
  try {
    const url = new URL(value);
    if (!/^https?:$/.test(url.protocol)) return "";
    url.hash = "";
    if (url.hostname === "dx.doi.org") url.hostname = "doi.org";
    if (url.hostname === "doi.org") url.pathname = url.pathname.toLowerCase();
    return url.href.replace(/\/$/, "");
  } catch {
    return "";
  }
}

export function resolveReference(
  registry: ReferenceRegistry | undefined,
  destination: unknown,
): ReferencePreview | null {
  if (!registry || typeof destination !== "string") return null;
  const key = referenceKey(destination) ?? registry.urls[referenceUrl(destination)] ?? destination;
  return registry.entries[key] ?? null;
}

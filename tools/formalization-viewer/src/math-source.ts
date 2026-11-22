export interface MathSourcePart {
  kind: "text" | "math";
  source: string;
  display: boolean;
}
// Treat paired delimiters as a unit; $$ is never parsed as two $ delimiters.
export function splitMathSource(source: string): MathSourcePart[] {
  const parts: MathSourcePart[] = [];
  let start = 0,
    i = 0;
  while (i < source.length) {
    let open: string | null = null;
    if (source[i] === "$") open = source[i + 1] === "$" ? "$$" : "$";
    else if (source[i] === "\\" && /[([]/.test(source[i + 1] ?? "")) open = source.slice(i, i + 2);
    if (!open) {
      i += source[i] === "\\" ? 2 : 1;
      continue;
    }
    const close = open === "\\(" ? "\\)" : open === "\\[" ? "\\]" : open;
    let end = i + open.length;
    while (end < source.length) {
      if (source.startsWith(close, end)) break;
      end += source[end] === "\\" ? 2 : 1;
    }
    if (end >= source.length) {
      i += open.length;
      continue;
    }
    if (i > start) parts.push({ kind: "text", source: source.slice(start, i), display: false });
    parts.push({ kind: "math", source: source.slice(i + open.length, end), display: open === "$$" || open === "\\[" });
    i = end + close.length;
    start = i;
  }
  if (start < source.length) parts.push({ kind: "text", source: source.slice(start), display: false });
  return parts;
}

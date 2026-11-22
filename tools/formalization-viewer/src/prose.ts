// Structural theorem/proof wrappers are not prose. Preserve named statement
// titles, but proof labels already have a dedicated marker-kind chip.
export function stripStatementEnvironments(source: string): string {
  return source
    .replace(
      /\\begin\{(proof|(?:theorem|lemma|proposition|corollary|claim|fact|recall|definition|example|construction|remark|statement)\*?)\}(?:\s*\[([^\]]*)\])?/g,
      (_match, environment: string, title: string | undefined) =>
        environment === "proof" || !title ? "" : `${title}. `,
    )
    .replace(
      /\\end\{(?:proof|(?:theorem|lemma|proposition|corollary|claim|fact|recall|definition|example|construction|remark|statement)\*?)\}/g,
      "",
    );
}

// A clause boundary must be outside math and command arguments. In particular,
// :=, decimal points, and punctuation inside \text{} are not title boundaries.
export function openingProseClause(source: string): string {
  let math: string | null = null;
  let depth = 0;
  for (let i = 0; i < source.length; i++) {
    if (source[i] === "\\") {
      const pair = source.slice(i, i + 2);
      if (!math && (pair === "\\(" || pair === "\\[")) {
        math = pair === "\\(" ? "\\)" : "\\]";
        i++;
        continue;
      }
      if (math === pair) {
        math = null;
        i++;
        continue;
      }
      if (/[\\$%{}]/.test(source[i + 1] ?? "")) {
        i++;
        continue;
      }
    }
    if (source[i] === "$") {
      const delimiter = source[i + 1] === "$" ? "$$" : "$";
      if (!math) math = delimiter;
      else if (math === delimiter) math = null;
      if (delimiter === "$$") i++;
      continue;
    }
    if (math) continue;
    if (source[i] === "{") depth++;
    if (source[i] === "}") depth = Math.max(0, depth - 1);
    if (!depth && /[.;:]/.test(source[i])) {
      if (source[i] === "." && /[0-9]/.test(source[i - 1] ?? "") && /[0-9]/.test(source[i + 1] ?? "")) continue;
      return source.slice(0, i).trim();
    }
  }
  return source.trim();
}

// Marker labels are plain prose plus separately rendered math. Remove prose
// formatting delimiters without changing multiplication/subscripts in math.
export function markerProseSource(source: string): string {
  source = stripStatementEnvironments(source);
  const math = /\$\$[^]*?\$\$|\$(?:\\.|[^$\\])*\$|\\\([^]*?\\\)|\\\[[^]*?\\\]/g;
  let result = "",
    start = 0;
  const strip = (text: string) => text.replace(/\*|`|__|(?<!\w)_(?=\S)|(?<=\S)_(?!\w)/g, "");
  for (const match of source.matchAll(math)) {
    result += strip(source.slice(start, match.index!)) + match[0];
    start = match.index! + match[0].length;
  }
  return result + strip(source.slice(start));
}

export interface MathRenderer {
  renderToString(source: string, options: Record<string, unknown>): string;
}
const escape = (text: string) =>
  text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

// Render only the book's prose subset. Source HTML stays escaped; only KaTeX
// produces HTML, with trust disabled. Balanced arguments retain nested math.
export function definitionHtml(
  source: string,
  katex: MathRenderer,
  macros: Record<string, unknown>,
  references: Record<string, string> = {},
): string {
  source = source.replace(/\\begin\{mathmeta\}[^]*?\\end\{mathmeta\}/g, "").trim();
  if (/^[-*+]\s+/.test(source)) {
    const items = source.split(/\n(?=[-*+]\s+)/);
    return `<ul>${items.map((item) => `<li>${definitionHtml(item.replace(/^[-*+]\s+/, ""), katex, macros, references)}</li>`).join("")}</ul>`;
  }
  let i = 0;
  const group = (): string => {
    if (source[i] !== "{") return "";
    i++;
    return render(true);
  };
  const render = (braced = false): string => {
    let html = "";
    while (i < source.length) {
      if (braced && source[i] === "}") {
        i++;
        break;
      }
      const remaining = source.slice(i);
      const reference = /^§\{([^}]+)\}/.exec(remaining);
      if (reference) {
        html += `§ ${escape(references[reference[1]] ?? reference[1])}`;
        i += reference[0].length;
        continue;
      }
      const markdown = ["**", "__", "`", "*", "_"].find((delimiter) => remaining.startsWith(delimiter));
      if (markdown) {
        const end = source.indexOf(markdown, i + markdown.length);
        if (end >= 0) {
          const content = source.slice(i + markdown.length, end);
          html +=
            markdown === "`"
              ? `<code>${escape(content)}</code>`
              : markdown.length === 1
                ? `<em>${definitionHtml(content, katex, macros, references)}</em>`
                : `<strong>${definitionHtml(content, katex, macros, references)}</strong>`;
          i = end + markdown.length;
          continue;
        }
      }
      const delimiter = remaining.startsWith("$$")
        ? "$$"
        : remaining.startsWith("\\[")
          ? "\\["
          : remaining.startsWith("\\(")
            ? "\\("
            : remaining[0] === "$"
              ? "$"
              : null;
      if (delimiter) {
        const close = delimiter === "\\[" ? "\\]" : delimiter === "\\(" ? "\\)" : delimiter;
        let end = source.indexOf(close, i + delimiter.length);
        while (end >= 0 && source[end - 1] === "\\" && close[0] !== "\\")
          end = source.indexOf(close, end + close.length);
        if (end >= 0) {
          const math = source.slice(i + delimiter.length, end);
          html += katex.renderToString(math, {
            output: "mathml",
            macros: { ...macros },
            displayMode: delimiter === "$$" || delimiter === "\\[",
            throwOnError: false,
            trust: false,
            strict: "ignore",
          });
          i = end + close.length;
          continue;
        }
      }
      const command =
        /^\\(term(?:define|use|forward)(?:as)?|BookSectionLink|textbf|emph|textit|texttt|begin|end|index|cite|label)\*?/.exec(
          remaining,
        );
      if (command) {
        i += command[0].length;
        const first = group();
        const name = command[1];
        if (name === "BookSectionLink") html += group();
        else if (name.endsWith("as")) {
          const display = group();
          html += name === "termdefineas" ? `<strong>${display}</strong>` : display;
        } else if (name.startsWith("termdefine") || name === "textbf") html += `<strong>${first}</strong>`;
        else if (name.startsWith("term")) html += first;
        else if (name === "emph" || name === "textit") html += `<em>${first}</em>`;
        else if (name === "texttt") html += `<code>${first}</code>`;
        else if (name === "cite") html += `[${first}]`;
        continue;
      }
      if (
        remaining.startsWith("\\{") ||
        remaining.startsWith("\\}") ||
        remaining.startsWith("\\$") ||
        remaining.startsWith("\\%") ||
        remaining.startsWith("\\&")
      ) {
        html += escape(source[i + 1]);
        i += 2;
        continue;
      }
      if (source[i] === "{") {
        html += group();
        continue;
      }
      if (remaining.startsWith("\n\n")) {
        html += "<br><br>";
        i += 2;
        continue;
      }
      html += escape(source[i] === "\n" || source[i] === "~" ? " " : source[i]);
      i++;
    }
    return html;
  };
  return render();
}

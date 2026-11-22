interface Token {
  text: string;
}
interface MacroContext {
  consumeSpaces: () => void;
  future: () => Token;
  popToken: () => Token;
  consumeArg: (delimiters?: string[]) => { tokens: Token[] };
}
function sourceOf(tokens: Token[]): string {
  let result = "",
    previous = "";
  for (const { text } of [...tokens].reverse()) {
    if (/^\\[A-Za-z@]+$/.test(previous) && /^[A-Za-z@]/.test(text)) result += " ";
    result += text;
    previous = text;
  }
  return result;
}
const cache = new WeakMap<Record<string, string>, Record<string, unknown>>();
// JSON manifests retain the canonical TeX bodies. Adapt the book's optional
// argument/empty-test pattern using the pinned KaTeX macro-expansion API.
export function katexRenderMacros(macros: Record<string, string>): Record<string, unknown> {
  let converted = cache.get(macros);
  if (!converted) {
    converted = { ...macros };
    for (const [name, body] of Object.entries(macros)) {
      const conditional = /^\\if\\relax\\detokenize\{#1\}\\relax([^]*?)\\else([^]*?)\\fi$/.exec(body);
      if (!conditional) continue;
      converted[name] = (context: MacroContext) => {
        context.consumeSpaces();
        let optional = "";
        if (context.future().text === "[") {
          context.popToken();
          optional = sourceOf(context.consumeArg(["]"]).tokens);
        }
        const argument = sourceOf(context.consumeArg().tokens);
        const branch = optional.trim() ? conditional[2] : conditional[1];
        return branch.replace(/#([12])/g, (_match, index: string) => (index === "1" ? optional : argument));
      };
    }
    cache.set(macros, converted);
  }
  // KaTeX may define macros while rendering; each expression owns its changes.
  return { ...converted };
}

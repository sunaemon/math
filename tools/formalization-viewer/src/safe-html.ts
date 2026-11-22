import DOMPurify from "../vendor/dompurify/purify.mjs";

// No default policy: an accidental raw innerHTML assignment must fail under CSP.
// DOMPurify's private policy is used only for its inert parsing, not application sinks.
const clean = (value: string): string => {
  if (!DOMPurify.isSupported) throw new Error("HTML sanitization is unavailable.");
  return DOMPurify.sanitize(value, {
    RETURN_TRUSTED_TYPE: false,
    FORBID_TAGS: ["script", "iframe", "object", "embed", "base", "style"],
    FORBID_ATTR: ["srcdoc"],
    ALLOW_DATA_ATTR: true,
  });
};
const factory = (
  globalThis as typeof globalThis & {
    trustedTypes?: {
      createPolicy(name: string, rules: { createHTML(value: string): string }): { createHTML(value: string): unknown };
    };
  }
).trustedTypes;
const policy = factory?.createPolicy("viewer-html", { createHTML: clean });

export function setHTML(element: Element, value: string): void {
  // DOM's TypeScript declarations still accept string, while the browser checks
  // the actual TrustedHTML object. Keep the one compatibility cast at this sink.
  element.innerHTML = (policy ? policy.createHTML(value) : clean(value)) as string;
}

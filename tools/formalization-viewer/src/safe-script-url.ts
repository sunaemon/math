// Only these three app-owned worker scripts may enter TrustedScriptURL sinks.
const allowed = new Set([
  new URL("../offline-worker.js", import.meta.url).href,
  new URL("../vendor/pdfjs/pdf.worker.mjs", import.meta.url).href,
  new URL("../pagefind/pagefind-worker.js", import.meta.url).href,
]);
const check = (value: string): string => {
  const url = new URL(value, location.href);
  if (!allowed.has(url.href)) throw new TypeError("Worker script URL is not allowlisted.");
  return url.href;
};
const factory = (
  globalThis as typeof globalThis & {
    trustedTypes?: {
      createPolicy(
        name: string,
        rules: { createScriptURL(value: string): string },
      ): { createScriptURL(value: string): unknown };
    };
  }
).trustedTypes;
const policy = factory?.createPolicy("viewer-script-url", { createScriptURL: check });
export function trustedScriptURL(value: string | URL): string {
  return (policy ? policy.createScriptURL(String(value)) : check(String(value))) as string;
}

// Blocking pre-paint setup only. Full localization and preference migration
// belong to the shared application graph, not a second bundled copy here.
const languages = navigator.languages?.length ? navigator.languages : [navigator.language];
let uiLanguage =
  languages.map((tag) => tag.toLowerCase().split(/[-_]/)[0]).find((tag) => tag === "ja" || tag === "en") ?? "en";
const root = document.documentElement;
root.dataset.viewStarting = "1";
let mode = "light";
let scheme = "solarized";
try {
  const language = localStorage.getItem("formalization-viewer-ui-language");
  if (language === "en" || language === "ja") uiLanguage = language;
  mode = localStorage.getItem("formalization-viewer-appearance-mode") || mode;
  scheme = localStorage.getItem("formalization-viewer-color-scheme") || scheme;
} catch {
  /* Storage can be disabled. */
}
root.lang = uiLanguage;
root.dataset.theme =
  mode === "dark" || (mode === "system" && matchMedia("(prefers-color-scheme: dark)").matches) ? "dark" : "light";
root.dataset.colorScheme = scheme === "classic" ? "classic" : "solarized";

// This runs before the application module graph is downloaded. Keep its
// progress visible even on connections where loading that graph takes seconds.
let modulesLoaded = 0;
let moduleBytes = 0;
let lastModule = "";
const moduleStarted = performance.now();
const showModuleProgress = () => {
  if (root.dataset.startupPhase || !root.dataset.viewStarting) return;
  const label = document.getElementById("startup-detail");
  const progress = document.getElementById("startup-progress");
  if (!label) return;
  const elapsed = Math.floor((performance.now() - moduleStarted) / 1000);
  label.textContent = modulesLoaded
    ? `${uiLanguage === "ja" ? "アプリケーションを読み込み中" : "Loading application modules"} · ${modulesLoaded} ${uiLanguage === "ja" ? "ファイル" : "files"} · ${(moduleBytes / 1048576).toFixed(1)} MB · ${elapsed}s${lastModule ? ` — ${lastModule}` : ""}`
    : `${uiLanguage === "ja" ? "アプリケーションを読み込み中…" : "Loading application modules…"} ${elapsed}s`;
  // No percentage is available until the module graph has been discovered.
  progress?.removeAttribute("value");
};
const moduleObserver = new PerformanceObserver((list) => {
  for (const entry of list.getEntries() as PerformanceResourceTiming[]) {
    const url = new URL(entry.name);
    if (url.origin !== location.origin || !/\/build\/[^/]+\.js$/.test(url.pathname)) continue;
    modulesLoaded++;
    moduleBytes += entry.decodedBodySize;
    lastModule = url.pathname.split("/").pop() || "";
  }
  showModuleProgress();
});
moduleObserver.observe({ type: "resource", buffered: true });
const moduleTimer = window.setInterval(() => {
  if (root.dataset.startupPhase || !root.dataset.viewStarting) {
    clearInterval(moduleTimer);
    moduleObserver.disconnect();
  } else showModuleProgress();
}, 250);
document.addEventListener("DOMContentLoaded", showModuleProgress, { once: true });

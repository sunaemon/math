import { readPreference, writePreference, CODE_FONTS, PDF_PAPER_KEY, PDF_FONT_SIZE_KEY } from "./session-store.js";
import { themedPdfPath } from "./pdf-theme.js";
import { layoutPdfPath } from "./pdf-layout.js";
import { project } from "./state.js";

const MODE = "formalization-viewer-appearance-mode";
const SCHEME = "formalization-viewer-color-scheme";
const FONT = "formalization-viewer-code-font";

export function renderedPdfPath(path: string): string {
  const layout = project.static
    ? path
    : layoutPdfPath(path, readPreference(PDF_PAPER_KEY) ?? "default", readPreference(PDF_FONT_SIZE_KEY) ?? "default");
  return themedPdfPath(layout, document.documentElement.dataset.theme === "dark");
}

export function initPdfLayout(changed: () => void): void {
  for (const [id, key] of [
    ["pdf-paper", PDF_PAPER_KEY],
    ["pdf-font-size", PDF_FONT_SIZE_KEY],
  ]) {
    const control = document.getElementById(id) as HTMLSelectElement;
    control.value = project.static ? "default" : (readPreference(key) ?? "default");
    control.disabled = !!project.static;
    control.addEventListener("change", () => {
      writePreference(key, control.value);
      changed();
    });
  }
}

export function initAppearance(changed: (modeChanged: boolean) => void): void {
  const mode = document.getElementById("appearance-mode")!;
  const scheme = document.getElementById("color-scheme") as HTMLSelectElement;
  const font = document.getElementById("code-font") as HTMLSelectElement;
  const storedMode = readPreference(MODE);
  let selectedMode = storedMode && ["system", "light", "dark"].includes(storedMode) ? storedMode : "light";
  scheme.value = readPreference(SCHEME) === "classic" ? "classic" : "solarized";
  const storedFont = readPreference(FONT);
  font.value = storedFont && Object.hasOwn(CODE_FONTS, storedFont) ? storedFont : "system";
  const system = window.matchMedia("(prefers-color-scheme: dark)");
  const apply = () => {
    const root = document.documentElement;
    const theme = selectedMode === "system" ? (system.matches ? "dark" : "light") : selectedMode;
    const modeChanged = !!root.dataset.theme && root.dataset.theme !== theme;
    root.dataset.theme = theme;
    root.dataset.colorScheme = scheme.value;
    root.style.setProperty("--code-font", CODE_FONTS[font.value]);
    for (const button of mode.querySelectorAll<HTMLButtonElement>("button[data-value]"))
      button.setAttribute("aria-pressed", String(button.dataset.value === selectedMode));
    return modeChanged;
  };
  apply();
  for (const button of mode.querySelectorAll<HTMLButtonElement>("button[data-value]")) {
    button.addEventListener("click", () => {
      selectedMode = button.dataset.value!;
      writePreference(MODE, selectedMode);
      changed(apply());
    });
  }
  for (const [control, key] of [
    [scheme, SCHEME],
    [font, FONT],
  ] as const) {
    control.addEventListener("change", () => {
      writePreference(key, control.value);
      changed(apply());
    });
  }
  system.addEventListener("change", () => {
    if (selectedMode === "system") changed(apply());
  });
}

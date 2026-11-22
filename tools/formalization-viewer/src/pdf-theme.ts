// Keep document selection independent of appearance: chapters and permalinks
// name the light artifact; only the fetched/built PDF changes with the theme.
export function lightPdfPath(path: string): string {
  return path.replace(/-dark(?=\.pdf(?:[?#]|$))/, "");
}

export function themedPdfPath(path: string, dark: boolean): string {
  const light = lightPdfPath(path);
  return dark ? light.replace(/(-debug|-preview-[A-Za-z0-9_-]+)(?=\.pdf(?:[?#]|$))/, "$1-dark") : light;
}

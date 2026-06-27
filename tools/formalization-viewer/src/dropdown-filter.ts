// Pure option-filtering and highlight-index clamping for the custom dropdown,
// extracted from select-dropdown.ts so the search/clamp logic is dependency-free
// and unit testable apart from the DOM widget.

export interface FilterableOption {
  label: string;
  value: string;
}

// Indices of options whose label (or, when the label is blank, value) contains
// the query, case-insensitively. A blank query keeps every option, in order.
export function filterOptionIndices(options: FilterableOption[], query: string): number[] {
  const q = query.trim().toLowerCase();
  const indices = options.map((_, i) => i);
  if (!q) return indices;
  return indices.filter((i) => (options[i].label || options[i].value).toLowerCase().includes(q));
}

// Clamp a highlight position into [0, length - 1], collapsing to 0 for an empty list.
export function clampIndex(length: number, index: number): number {
  if (length <= 0) return 0;
  return Math.max(0, Math.min(length - 1, index));
}

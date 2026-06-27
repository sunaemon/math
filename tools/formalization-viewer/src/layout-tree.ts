// The viewer's pane layout as a nested split tree, and the pure operations over
// it. A node is either a leaf `{ pane }` or a split
// `{ dir: "row"|"col", children: [node...], ratios: [num...] }`. "row" lays
// children out side by side; "col" stacks them top to bottom.
//
// Everything here is a pure data transform over LayoutNode (no DOM, no module
// state), split out of app.ts so the layout algebra can be read and tested on
// its own. The stateful glue (persisting the tree, rendering it to DOM, drag
// and drop) stays in app.ts and imports these.

export const PANE_NAMES = ["pdf", "md", "lean", "tex", "infoview"];

export interface LayoutNode {
  pane?: string;
  dir?: "row" | "col";
  children?: LayoutNode[];
  ratios?: number[];
}

export function defaultTree(): LayoutNode | null {
  return makeSplit(
    "row",
    PANE_NAMES.filter((name) => name !== "tex"),
  );
}

export function makeSplit(dir: "row" | "col", panes: string[]): LayoutNode | null {
  const leaves = panes.map((pane) => ({ pane }));
  if (leaves.length === 0) return null;
  if (leaves.length === 1) return leaves[0];
  return { dir, children: leaves, ratios: leaves.map(() => 1) };
}

export function eachLeaf(node: LayoutNode | null, fn: (leaf: LayoutNode) => void): void {
  if (!node) return;
  if (node.pane) fn(node);
  else (node.children ?? []).forEach((child) => eachLeaf(child, fn));
}

export function treeLeaves(node: LayoutNode | null): string[] {
  const out: string[] = [];
  eachLeaf(node, (leaf) => {
    if (leaf.pane) out.push(leaf.pane);
  });
  return out;
}

export function treeKind(node: LayoutNode | null): string {
  if (!node || node.pane) return "columns";
  const allLeaves = (node.children ?? []).every((child) => child.pane);
  if (allLeaves && node.dir === "row") return "columns";
  if (allLeaves && node.dir === "col") return "rows";
  return "others";
}

export function validateTree(node: any, seen: Set<string> = new Set()): LayoutNode | null {
  if (!node || typeof node !== "object") return null;
  if (typeof node.pane === "string") {
    if (!PANE_NAMES.includes(node.pane) || seen.has(node.pane)) return null;
    seen.add(node.pane);
    return { pane: node.pane };
  }
  if ((node.dir !== "row" && node.dir !== "col") || !Array.isArray(node.children)) return null;
  const kids: LayoutNode[] = [];
  for (const child of node.children) {
    const clean = validateTree(child, seen);
    if (clean) kids.push(clean);
  }
  if (kids.length === 0) return null;
  if (kids.length === 1) return kids[0];
  const ratios =
    Array.isArray(node.ratios) && node.ratios.length === kids.length
      ? node.ratios.map((r: any) => (Number(r) > 0 ? Number(r) : 1))
      : kids.map(() => 1);
  return { dir: node.dir, children: kids, ratios };
}

// Drop a leaf, collapsing splits that fall to a single child.
export function removeLeaf(node: LayoutNode | null, pane: string): LayoutNode | null {
  if (!node) return null;
  if (node.pane) return node.pane === pane ? null : node;
  const kids: LayoutNode[] = [];
  const ratios: number[] = [];
  (node.children ?? []).forEach((child, i) => {
    const kept = removeLeaf(child, pane);
    if (kept) {
      kids.push(kept);
      ratios.push((node.ratios ?? [])[i]);
    }
  });
  if (kids.length === 0) return null;
  if (kids.length === 1) return kids[0];
  return { dir: node.dir, children: kids, ratios };
}

export function replaceLeaf(node: LayoutNode | null, pane: string, replacement: LayoutNode): LayoutNode | null {
  if (!node) return null;
  if (node.pane) return node.pane === pane ? replacement : node;
  return {
    dir: node.dir,
    ratios: node.ratios,
    children: (node.children ?? []).map((c) => replaceLeaf(c, pane, replacement)) as LayoutNode[],
  };
}

// Merge nested splits that share their parent's direction, so a row of leaves
// stays a flat "horizontal" layout after edge drops along its axis.
export function flattenSameDir(node: LayoutNode | null): LayoutNode | null {
  if (!node || node.pane) return node;
  const kids: LayoutNode[] = [];
  const ratios: number[] = [];
  (node.children ?? []).forEach((child, i) => {
    const f = flattenSameDir(child);
    if (f && f.dir === node.dir) {
      (f.children ?? []).forEach((k, j) => {
        kids.push(k);
        ratios.push((f.ratios ?? [])[j]);
      });
    } else if (f) {
      kids.push(f);
      ratios.push((node.ratios ?? [])[i]);
    }
  });
  return { dir: node.dir, children: kids, ratios };
}

export function addLeaf(node: LayoutNode | null, pane: string): LayoutNode {
  if (!node) return { pane };
  if (node.pane) return { dir: "row", children: [node, { pane }], ratios: [1, 1] };
  return { dir: node.dir, children: [...(node.children ?? []), { pane }], ratios: [...(node.ratios ?? []), 1] };
}

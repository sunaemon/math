// Keep original PDF page indices for destinations and source maps. Chapter
// previews can prepend a part divider and openright parity padding; their
// first chapter bookmark identifies where the chapter itself starts.
export async function previewStartPage(doc: any, path: string, current: () => boolean = () => true): Promise<number> {
  if (!/-preview-[^/]+\.pdf$/i.test(path.split(/[?#]/, 1)[0])) return 1;
  try {
    const outline = await doc.getOutline();
    if (!current()) return 1;
    const chapters: string[] = [];
    const visit = (items: any[]) => {
      for (const item of items) {
        if (typeof item.dest === "string" && /^chapter[.*]/.test(item.dest)) chapters.push(item.dest);
        visit(item.items ?? []);
      }
    };
    visit(outline ?? []);
    // Contents has no outline entry. pdf.js may also omit its name tree from
    // getDestinations(), while direct lookup of the first heading still works.
    if (/-preview-_contents(?:-dark)?\.pdf$/i.test(path.split(/[?#]/, 1)[0])) {
      const destinations = await doc.getDestinations();
      if (!current()) return 1;
      chapters.unshift("chapter*.1", ...Object.keys(destinations ?? {}).filter((name) => /^chapter[.*]/.test(name)));
    }
    for (const name of chapters) {
      const destination = await doc.getDestination(name);
      if (!current()) return 1;
      if (!Array.isArray(destination) || destination[0] == null) continue;
      const index = typeof destination[0] === "number" ? destination[0] : await doc.getPageIndex(destination[0]);
      if (!current()) return 1;
      if (Number.isInteger(index) && index >= 0 && index < doc.numPages) return index + 1;
    }
  } catch {
    // Unknown or damaged outlines must never hide possibly meaningful content.
  }
  return 1;
}

// A chapter PDF has no anchors from other chapters. Avoid asking the worker
// thousands of times about passages that cannot belong to this document.
export function pdfIncludesSource(pdf: string, source: unknown): boolean {
  const chapter = /-preview-(.+?)(?:-dark)?\.pdf$/i.exec(pdf.split(/[?#]/, 1)[0])?.[1];
  if (!chapter || typeof source !== "string" || !source) return true;
  return source.split(/[\\/]/).pop()?.replace(/\.md$/i, "") === chapter;
}

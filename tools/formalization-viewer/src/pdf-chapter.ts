// The printed PDF links terms/notation to their index entries. Companion
// anchors identify their definitions; keep the two destinations distinct.
export function termTarget(dest: unknown): { definition: string; references: string; label: string } | null {
  if (typeof dest !== "string") return null;
  const match = /^(term|notation)-(?:index|def)-(.+)$/.exec(dest);
  if (!match) return null;
  return {
    definition: `${match[1]}-def-${match[2]}`,
    references: `${match[1]}-index-${match[2]}`,
    label: match[1] === "term" ? match[2].replace(/-/g, " ") : match[2],
  };
}

export function preferredDestination(dest: string, preferDefinition: boolean): string {
  return preferDefinition ? (termTarget(dest)?.definition ?? dest) : dest;
}

// Find the owning chapter in the complete PDF without displaying that PDF.
export async function destinationChapter(
  doc: any,
  dest: string,
  anchors: Record<string, string>,
  sections: Record<string, string> = {},
  preferDefinition = true,
): Promise<string | null> {
  const definition = preferredDestination(dest, preferDefinition);
  const target = (await doc.getDestination(definition)) ?? (await doc.getDestination(dest));
  if (!target) return null;
  const position = async (d: any): Promise<number> => {
    const page = typeof d[0] === "number" ? d[0] : await doc.getPageIndex(d[0]);
    // PDF coordinates increase upwards; higher anchors precede lower ones.
    return page * 100000 - (typeof d[3] === "number" ? d[3] : 100000);
  };
  const end = await position(target);
  let best = -Infinity;
  let chapter: string | null = null;
  const chapters: any[] = [];
  const matter: Array<{ name: string; dest: string }> = [];
  const visit = (items: any[]) => {
    for (const item of items) {
      if (typeof item.dest === "string" && /^chapter[.*]/.test(item.dest)) chapters.push(item.dest);
      for (const [name, title] of Object.entries(sections)) {
        if (item.title === title && typeof item.dest === "string") matter.push({ name, dest: item.dest });
      }
      visit(item.items ?? []);
    }
  };
  visit((await doc.getOutline()) ?? []);
  for (const [index, name] of Object.keys(anchors).entries()) {
    const d = chapters[index] ? await doc.getDestination(chapters[index]) : null;
    if (!d) continue;
    const start = await position(d);
    if (start <= end && start > best) {
      best = start;
      chapter = name;
    }
  }
  for (const { name, dest } of matter) {
    const d = await doc.getDestination(dest);
    if (!d) continue;
    const start = await position(d);
    if (start <= end && start > best) {
      best = start;
      chapter = name;
    }
  }
  return chapter;
}

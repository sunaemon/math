export interface PaneHit {
  title: string;
  excerpt: string;
  line?: number;
  page?: number;
  fraction?: number;
}
const normalize = (value: string) => value.normalize("NFKC").toLocaleLowerCase();
export function findInLines(text: string, query: string, limit = 200): PaneHit[] {
  const hits: PaneHit[] = [];
  for (const hit of lineHits(text, query)) {
    hits.push(hit);
    if (hits.length >= limit) break;
  }
  return hits;
}
export async function* pdfHits(
  doc: any,
  query: string,
  current: () => boolean,
  textOf: (page: any) => Promise<any>,
): AsyncGenerator<PaneHit> {
  const compact = /[\u3040-\u9fff]/.test(query);
  const key = (value: string) => {
    const s = normalize(value);
    return compact ? s.replace(/\s+/g, "") : s;
  };
  const needle = key(query.trim());
  if (!needle) return;
  for (let number = 1; number <= doc.numPages && current(); number++) {
    const page = await doc.getPage(number);
    if (!current()) return;
    const content = await textOf(page);
    if (!current()) return;
    const items = content.items.filter((item: any) => typeof item.str === "string");
    const pieces: string[] = items.map((item: any) => key(item.str) + (compact ? "" : " "));
    const text = pieces.join("");
    let at = text.indexOf(needle);
    while (at >= 0) {
      let index = 0,
        offset = 0;
      while (index < pieces.length - 1 && offset + pieces[index].length <= at) offset += pieces[index++].length;
      const y = items[index]?.transform?.[5];
      const height = page.view?.[3] ?? page.getViewport({ scale: 1 }).height;
      if (!current()) return;
      yield {
        title: `ページ ${number}`,
        page: number,
        fraction: typeof y === "number" ? Math.max(0, Math.min(1, 1 - y / height)) : 0,
        excerpt: items
          .slice(Math.max(0, index - 2), index + 12)
          .map((item: any) => item.str)
          .join(" "),
      };
      at = text.indexOf(needle, at + Math.max(1, needle.length));
    }
  }
}

// Prepare distinct neighboring result pages, rather than every page or every
// occurrence on the same page. Two ahead and one behind keep navigation warm.
export function nearbyHitPages(hits: readonly PaneHit[], index: number): number[] {
  const current = hits[index]?.page;
  if (!current) return [];
  const pages: number[] = [];
  const seen = new Set([current]);
  for (const [direction, limit] of [
    [1, 2],
    [-1, 1],
  ]) {
    let found = 0;
    for (let at = index + direction; at >= 0 && at < hits.length && found < limit; at += direction) {
      const page = hits[at].page;
      if (!page || seen.has(page)) continue;
      seen.add(page);
      pages.push(page);
      found++;
    }
  }
  return pages;
}

export async function findInPdf(
  doc: any,
  query: string,
  current: () => boolean,
  textOf: (page: any) => Promise<any>,
  limit = 200,
): Promise<PaneHit[]> {
  const hits: PaneHit[] = [];
  for await (const hit of pdfHits(doc, query, current, textOf)) {
    hits.push(hit);
    if (hits.length >= limit) break;
  }
  return current() ? hits : [];
}

export function* lineHits(text: string, query: string): Generator<PaneHit> {
  const needle = normalize(query.trim());
  if (!needle) return;
  for (const [index, line] of text.split("\n").entries()) {
    const at = normalize(line).indexOf(needle);
    if (at >= 0)
      yield {
        title: `行 ${index + 1}`,
        line: index + 1,
        excerpt: line.slice(Math.max(0, at - 70), at + needle.length + 150),
      };
  }
}

export class PaneSearchSession {
  readonly hits: PaneHit[] = [];
  hasMore = true;
  private buffered: PaneHit | undefined;
  private pending: Promise<void> | undefined;
  private iterator: AsyncIterator<PaneHit> | Iterator<PaneHit>;
  private current: () => boolean;
  constructor(iterator: AsyncIterator<PaneHit> | Iterator<PaneHit>, current: () => boolean) {
    this.iterator = iterator;
    this.current = current;
  }
  loadMore(): Promise<void> {
    if (this.pending) return this.pending;
    const pending = this.readBatch();
    this.pending = pending;
    void pending
      .finally(() => {
        if (this.pending === pending) this.pending = undefined;
      })
      .catch(() => {});
    return pending;
  }
  private async readBatch(): Promise<void> {
    if (!this.hasMore || !this.current()) return;
    const batch: PaneHit[] = [];
    if (this.buffered) {
      batch.push(this.buffered);
      this.buffered = undefined;
    }
    while (batch.length < 200 && this.current()) {
      const next = await this.iterator.next();
      if (!this.current()) return;
      if (next.done) {
        this.hasMore = false;
        break;
      }
      batch.push(next.value);
    }
    if (this.hasMore && this.current()) {
      const next = await this.iterator.next();
      if (!this.current()) return;
      this.hasMore = !next.done;
      this.buffered = next.done ? undefined : next.value;
    }
    if (this.current()) this.hits.push(...batch);
  }
}

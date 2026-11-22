// Reading the PDF name tree once avoids thousands of worker round trips and
// repeated tree walks when resolving booklink and skip-region anchors.
const lookups = new WeakMap<object, Map<string, Promise<any>>>();
const destinations = new WeakMap<object, Promise<Record<string, any>>>();

export async function pdfDestination(doc: any, name: string): Promise<any> {
  let pending = destinations.get(doc);
  if (!pending) {
    pending = Promise.resolve().then(() => doc.getDestinations());
    destinations.set(doc, pending);
    const request = pending;
    void pending.catch(() => {
      if (destinations.get(doc) === request) destinations.delete(doc);
    });
  }
  const names = await pending;
  if (Object.hasOwn(names, name)) return names[name];
  // Some PDFs expose directly searchable destinations that are absent from
  // the enumerated name tree. Preserve those anchors and deduplicate fallbacks.
  let cache = lookups.get(doc);
  if (!cache) lookups.set(doc, (cache = new Map()));
  let result = cache.get(name);
  if (!result) {
    result = Promise.resolve().then(() => doc.getDestination(name));
    cache.set(name, result);
    const request = result;
    void result.catch(() => {
      if (cache.get(name) === request) cache.delete(name);
    });
  }
  return result;
}

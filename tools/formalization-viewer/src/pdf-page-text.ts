// Layout sampling, marker bands and the selectable text layer consume the
// same page text. Share its extraction without retaining destroyed documents.
const content = new WeakMap<object, Promise<any>>();

export function pdfPageText(page: any): Promise<any> {
  let result = content.get(page);
  if (!result) {
    result = Promise.resolve().then(() => page.getTextContent({ includeMarkedContent: true }));
    content.set(page, result);
    const request = result;
    void result.catch(() => {
      if (content.get(page) === request) content.delete(page);
    });
  }
  return result;
}

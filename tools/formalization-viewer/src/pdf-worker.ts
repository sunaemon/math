// A loading task owns its worker. A global workerPort lets pdf.js cache one
// PDFWorker across documents; destroying an old task then breaks its siblings.
// Inject the native worker factory so production can apply Trusted Types and
// tests can verify ownership without starting browser workers.
export function documentWorkerApi(pdfjs: any, createPort: () => Worker): any {
  return {
    ...pdfjs,
    getDocument(source: any) {
      const params =
        typeof source === "string" || source instanceof URL
          ? { url: source }
          : source instanceof ArrayBuffer || ArrayBuffer.isView(source)
            ? { data: source }
            : source;
      if (params?.worker) return pdfjs.getDocument(params);
      const port = createPort();
      let worker: any;
      try {
        worker = new pdfjs.PDFWorker({ port });
        const task = pdfjs.getDocument({ ...params, worker });
        const destroy = task.destroy.bind(task);
        let destroying: Promise<void> | undefined;
        task.destroy = () =>
          (destroying ??= (async () => {
            try {
              await destroy();
            } finally {
              worker.destroy();
              port.terminate();
            }
          })());
        void task.promise.catch(() => {
          void task.destroy().catch(() => {});
        });
        return task;
      } catch (error) {
        worker?.destroy();
        port.terminate();
        throw error;
      }
    },
  };
}

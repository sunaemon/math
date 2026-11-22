import test from "node:test";
import assert from "node:assert/strict";
import { documentWorkerApi } from "./pdf-worker.ts";

function fixture() {
  const ports: Array<{ terminated: number }> = [];
  const workers: Array<{ destroyed: number; port: unknown }> = [];
  const tasks: any[] = [];
  const library = {
    PDFWorker: class {
      destroyed = 0;
      port: unknown;
      constructor({ port }: { port: unknown }) {
        this.port = port;
        workers.push(this);
      }
      destroy() {
        this.destroyed++;
      }
    },
    getDocument(params: any) {
      const task = {
        params,
        promise: Promise.resolve({}),
        destroyed: 0,
        async destroy() {
          this.destroyed++;
        },
      };
      tasks.push(task);
      return task;
    },
  };
  const createPort = () => {
    const port = {
      terminated: 0,
      terminate() {
        this.terminated++;
      },
    };
    ports.push(port);
    return port as unknown as Worker;
  };
  return { api: documentWorkerApi(library, createPort), library, ports, workers, tasks, createPort };
}

test("replacing one PDF cannot destroy the worker of a simultaneous primary or peer document", async () => {
  const { api, ports, workers, tasks } = fixture();
  const old = api.getDocument({ url: "old.pdf" });
  const peer = api.getDocument({ url: "peer.pdf" });
  const next = api.getDocument({ url: "new.pdf" });
  assert.notEqual(old.params.worker, peer.params.worker);
  assert.notEqual(peer.params.worker, next.params.worker);
  await Promise.all([old.destroy(), old.destroy()]);
  assert.deepEqual(
    workers.map((worker) => worker.destroyed),
    [1, 0, 0],
  );
  assert.deepEqual(
    ports.map((port) => port.terminated),
    [1, 0, 0],
  );
  assert.equal(tasks[0].destroyed, 1);
  await Promise.all([peer.destroy(), next.destroy()]);
  assert.deepEqual(
    ports.map((port) => port.terminated),
    [1, 1, 1],
  );
});

test("failed PDF loading releases its worker", async () => {
  const { library, createPort, ports, workers } = fixture();
  const getDocument = library.getDocument;
  library.getDocument = (params: any) => ({
    ...getDocument(params),
    promise: Promise.reject(new Error("load failed")),
  });
  const api = documentWorkerApi(library, createPort);
  const failed = api.getDocument("missing.pdf");
  await assert.rejects(failed.promise, /load failed/);
  await failed.destroy();
  assert.equal(workers[0].destroyed, 1);
  assert.equal(ports[0].terminated, 1);
});

test("synchronous setup failures release workers and caller-owned workers remain caller-owned", async () => {
  const { library, createPort, ports, workers } = fixture();
  const api = documentWorkerApi(library, createPort);
  const owned = { marker: true };
  const task = api.getDocument({ url: "caller.pdf", worker: owned });
  await task.destroy();
  assert.equal(ports.length, 0);
  library.getDocument = () => {
    throw new Error("invalid source");
  };
  const failing = documentWorkerApi(library, createPort);
  assert.throws(() => failing.getDocument({}), /invalid source/);
  assert.equal(workers[0].destroyed, 1);
  assert.equal(ports[0].terminated, 1);
});

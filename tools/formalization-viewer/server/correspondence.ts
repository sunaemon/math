// Read-only report/AST adapter. Only registered Markdown sources can reach the
// Python/Haskell projection. The lazy source index elaborates original Lean
// syntax; neither route builds dependencies or approves meaning.
import fs from "node:fs";
import path from "node:path";
import { execFile } from "node:child_process";
import { inputStamp } from "./input-stamp.ts";

interface CachedInspection {
  stamp: string;
  inputs: string[];
  value: Promise<unknown>;
}

export class CorrespondenceService {
  private cache = new Map<string, CachedInspection>();
  private root: string;

  constructor(root: string) {
    this.root = root;
  }

  invalidate(changed?: string): void {
    if (changed === undefined) return this.cache.clear();
    const file = path.resolve(this.root, changed);
    for (const [source, entry] of this.cache) {
      if (entry.inputs.includes(file)) this.cache.delete(source);
    }
  }

  private inputs(source: string): string[] {
    const inputs = [path.join(this.root, source), path.join(this.root, "build/book-filter")];
    for (const [relative, extension] of [
      ["tools/book-filter", ".hs"],
      ["tools/chapter-correspondence", ".py"],
      ["tools/chapter-correspondence", ".json"],
      ["tools/chapter-correspondence/chapters", ".json"],
    ]) {
      const directory = path.join(this.root, relative);
      inputs.push(directory);
      if (fs.existsSync(directory))
        inputs.push(
          ...fs
            .readdirSync(directory)
            .filter((name) => name.endsWith(extension))
            .sort()
            .map((name) => path.join(directory, name)),
        );
    }
    for (const name of ["lean_export.py", "lean_probe_cache.py", "lean_source_ranges.lean"])
      inputs.push(path.join(this.root, "tools", name));
    const validation = path.join(this.root, "build/validation");
    if (fs.existsSync(validation))
      for (const directory of fs
        .readdirSync(validation)
        .filter((name) => name.startsWith("correspondence-"))
        .sort())
        for (const name of ["report.json", "formulas.json", "operators.json", "dependencies.json"])
          inputs.push(path.join(validation, directory, name));
    return inputs;
  }

  read(source: string, leanSource = false): Promise<unknown> {
    if (!source.endsWith(".md") || path.isAbsolute(source) || source.split(/[\\/]/).includes(".."))
      return Promise.reject(new Error("Invalid correspondence source"));
    const key = `${leanSource ? "lean:" : "ast:"}${source}`;
    const previous = this.cache.get(key);
    const baseInputs = this.inputs(source);
    const inputs = [...new Set([...baseInputs, ...(previous?.inputs ?? [])])];
    const stamp = inputStamp(inputs);
    if (previous && previous.stamp === stamp) return previous.value;
    const script = path.join(this.root, "tools/chapter-correspondence/viewer.py");
    if (!fs.existsSync(script)) return Promise.resolve({ status: "unavailable", formulas: [] });
    const value = new Promise<unknown>((resolve, reject) => {
      execFile(
        "python3",
        [script, "--source", source, ...(leanSource ? ["--lean-source"] : [])],
        { cwd: this.root, timeout: leanSource ? 420000 : 90000, maxBuffer: 32 * 1024 * 1024 },
        (error, stdout, stderr) => {
          if (error) return reject(new Error(stderr.trim() || error.message));
          try {
            const result = JSON.parse(stdout);
            const dependencies = result._cacheInputs;
            delete result._cacheInputs;
            entry.inputs = [
              ...new Set([
                ...inputs,
                ...(Array.isArray(dependencies)
                  ? dependencies.filter((file): file is string => typeof file === "string")
                  : []),
              ]),
            ];
            // Never attach an inspection to a source/rule/report changed while
            // the worker was running. Python independently checks Lean inputs.
            if (inputStamp(inputs) !== stamp) {
              if (this.cache.get(key) === entry) this.cache.delete(key);
            } else entry.stamp = inputStamp(entry.inputs);
            resolve(result);
          } catch (error) {
            reject(error);
          }
        },
      );
    });
    if (this.cache.size >= 16) this.cache.clear();
    const entry = { stamp, inputs, value };
    this.cache.set(key, entry);
    void value.then(
      () => {},
      () => {
        if (this.cache.get(key) === entry) this.cache.delete(key);
      },
    );
    return value;
  }
}

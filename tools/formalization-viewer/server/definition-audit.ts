#!/usr/bin/env node
// Deterministic inventory/validation; no PDF builds or source edits.
import fs from "node:fs";
import path from "node:path";
import { bookDefinitionRegistry } from "./definitions.ts";
import type { Manifest } from "./projects.ts";

const root = process.cwd();
fs.mkdirSync(path.join(root, "build/validation"), { recursive: true });
const directory = fs.mkdtempSync(path.join(root, "build/validation/definitions-"));
const reports = [];
for (const dir of fs.readdirSync(root).sort()) {
  const file = path.join(root, dir, "manifest.json");
  if (!fs.existsSync(file)) continue;
  const project = JSON.parse(fs.readFileSync(file, "utf8")) as Manifest;
  if (typeof project.bookManifest !== "string") continue;
  const registry = bookDefinitionRegistry(root, project);
  const records = Object.values(registry.entries);
  const report = {
    book: dir,
    counts: Object.fromEntries(
      ["term", "notation", "section"].map((kind) => [kind, records.filter((e) => e.kind === kind).length]),
    ),
    diagnostics: registry.diagnostics,
  };
  fs.writeFileSync(path.join(directory, dir + ".json"), JSON.stringify(registry, null, 2) + "\n");
  reports.push(report);
  console.log(
    `${registry.diagnostics.length ? "FAIL" : "PASS"}: ${dir}; ${registry.diagnostics.length} definition diagnostic(s)`,
  );
}
const report = { passed: reports.length > 0 && reports.every((r) => !r.diagnostics.length), books: reports };
fs.writeFileSync(path.join(directory, "report.json"), JSON.stringify(report, null, 2) + "\n");
console.log(`Report: ${path.join(directory, "report.json")}`);
if (!report.passed) process.exitCode = 1;

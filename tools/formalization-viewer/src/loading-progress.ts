import { t } from "./i18n.js";
let startupPhase = "";

export function startupStep(phase: string, detail: string): void {
  startupPhase = phase;
  document.documentElement.dataset.startupPhase = phase;
  const steps = [...document.querySelectorAll<HTMLElement>("[data-startup-step]")];
  const index = steps.findIndex((step) => step.dataset.startupStep === phase);
  steps.forEach((step, i) => {
    step.dataset.state = i < index ? "done" : i === index ? "working" : "pending";
  });
  const progress = document.getElementById("startup-progress") as HTMLProgressElement | null;
  if (progress) {
    progress.max = steps.length;
    progress.value = Math.max(0, index);
  }
  startupDetail(phase, detail);
}

export function startupDetail(phase: string, detail: string): void {
  if (phase !== startupPhase) return;
  const label = document.getElementById("startup-detail");
  if (label) label.textContent = detail;
}

export function finishStartup(): void {
  startupPhase = "";
  delete document.documentElement.dataset.startupPhase;
  delete document.documentElement.dataset.viewStarting;
}

export function paneLoadStatus(viewer: HTMLElement, text: string | null): void {
  let status = viewer.parentElement!.querySelector<HTMLElement>(":scope > .pdf-load-status");
  if (!status) {
    status = document.createElement("div");
    status.className = "pdf-load-status";
    status.setAttribute("role", "status");
    status.setAttribute("aria-live", "polite");
    viewer.parentElement!.append(status);
  }
  status.hidden = !text;
  status.textContent = text ?? "";
}

export function pdfLoadStatus(viewer: HTMLElement, text: string | null): void {
  paneLoadStatus(viewer, text);
  if (text) startupDetail("pdf", text);
}

export function pdfByteProgress(progress: { loaded: number; total?: number }): string {
  const mb = (n: number) => `${(n / 1048576).toFixed(1)} MB`;
  return progress.total
    ? t("Loading PDF · {0} / {1}", mb(progress.loaded), mb(progress.total))
    : t("Loading PDF · {0}", mb(progress.loaded));
}

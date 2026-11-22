import { t } from "./i18n.js";
import { state, project } from "./state.js";
import { mountPrefix, repoPath } from "./util.js";
import { nearestFormula, sourcePieces, type CorrespondenceReport } from "./correspondence-model.js";

let refresh: ((force: boolean) => void) | undefined;
let openFormula: ((index: number) => void) | undefined;
export function openCorrespondenceFormula(index: number): void {
  openFormula?.(index);
}
export function refreshCorrespondence(force = false): void {
  refresh?.(force);
}

function element<K extends keyof HTMLElementTagNameMap>(tag: K, text?: string): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  return node;
}

function disclosure(title: string, content: HTMLElement): HTMLDetailsElement {
  const details = element("details");
  details.append(element("summary", title), content);
  return details;
}

// Expand lazily, so opening a formula does not create thousands of DOM nodes.
function tree(value: unknown, highlight: (start: number, end: number) => void, base = 0): HTMLElement {
  if (value === null || typeof value !== "object") return element("code", JSON.stringify(value));
  const object = value as Record<string, any>;
  if (Number.isInteger(object.start) && Number.isInteger(object.end) && Object.keys(object).length === 2) {
    const button = element("button", `[${object.start}, ${object.end})`);
    button.type = "button";
    button.addEventListener("click", () => highlight(base + object.start, base + object.end));
    return button;
  }
  const contents = element("div");
  contents.className = "correspondence-tree";
  const details = disclosure(
    Array.isArray(value) ? `[${value.length}]` : String(object.node ?? object.kind ?? "{}"),
    contents,
  );
  if (Number.isInteger(object.start) && Number.isInteger(object.end)) {
    const locate = element("button", `[${object.start}, ${object.end})`);
    locate.type = "button";
    locate.addEventListener("click", (event) => {
      event.preventDefault();
      highlight(base + object.start, base + object.end);
    });
    details.querySelector("summary")!.append(" ", locate);
  }
  details.addEventListener("toggle", () => {
    if (!details.open || contents.childNodes.length) return;
    for (const [key, child] of Object.entries(value)) {
      if (key === "node" || key === "kind") continue;
      const row = element("div");
      row.append(element("span", `${key}: `), tree(child, highlight, base));
      contents.append(row);
    }
  });
  return details;
}

export function initCorrespondence(navigate: (source: string, line: number) => Promise<void>): void {
  const dialog = document.getElementById("correspondence-dialog") as HTMLDialogElement;
  const select = document.getElementById("correspondence-formula") as HTMLSelectElement;
  const status = document.getElementById("correspondence-status")!;
  const body = document.getElementById("correspondence-body")!;
  const reload = document.getElementById("correspondence-refresh") as HTMLButtonElement;
  let report: CorrespondenceReport | null = null;
  let loadedSource = "";
  let token = 0;
  let controller: AbortController | undefined;
  let preferredFormula: number | null = null;
  const currentSource = () => `${project.dir}/${state.selectedSources.md ?? ""}`;

  function render(): void {
    body.replaceChildren();
    const row = report?.formulas[Number(select.value)];
    if (!row || !report) return;
    const source = element("pre");
    source.id = "correspondence-source";
    source.textContent = row.book;
    const position = element(
      "p",
      `MD [${row.bodyStart}, ${row.bodyStart + Array.from(row.book).length}) · L${row.line}`,
    );
    const highlight = (start: number, end: number) => {
      const [before, selected, after] = sourcePieces(row, start, end);
      source.replaceChildren(
        document.createTextNode(before),
        element("mark", selected),
        document.createTextNode(after),
      );
      position.textContent = `MD [${start}, ${end}) · L${row.line}`;
    };
    const openSource = element("button", t("Open source"));
    openSource.type = "button";
    openSource.disabled = report.status !== "current";
    openSource.addEventListener("click", () => {
      dialog.close();
      void navigate(repoPath(report!.source), row.line);
    });
    body.append(position, source, openSource);
    body.append(element("h3", t("Lean interpretation")));
    const interpretations = row.expressionFragments ?? [row];
    for (const interpretation of interpretations) {
      body.append(element("p", `${interpretation.typeStatus} · ${interpretation.context ?? ""}`));
      body.append(element("pre", interpretation.lean ?? interpretation.typeReason ?? ""));
      if (interpretation.inferredType) body.append(element("code", interpretation.inferredType));
    }
    body.append(disclosure(t("Resolved variables"), tree(row.variables, highlight)));
    body.append(disclosure(t("Syntax AST"), tree(row.syntax, highlight, row.bodyStart)));
    const semantic = element("div");
    for (const expression of row.semanticExpressions ?? []) {
      semantic.append(tree(expression.ast ?? expression.reason, highlight, row.bodyStart));
    }
    if (!semantic.childNodes.length) semantic.textContent = t("A current validation is required for the semantic AST.");
    body.append(disclosure(t("Semantic AST"), semantic));
    body.append(element("h3", t("Operator correspondence")));
    for (const operator of row.operators) {
      const card = element("article");
      card.className = "correspondence-operator";
      const locate = element(
        "button",
        `${operator.sourceOperator} · [${operator.operatorStart}, ${operator.operatorEnd})`,
      );
      locate.type = "button";
      locate.addEventListener("click", () => highlight(operator.operatorStart, operator.operatorEnd));
      card.append(locate, element("p", `${operator.rule} → ${operator.expectedHead ?? ""}`));
      card.append(
        element(
          "p",
          `${t("Function")}: ${operator.targetStatus} · ${t("Arguments")}: ${operator.operandStatus} · ${t("Implicit arguments")}: ${operator.implicitArgumentStatus} · ${t("Premises")}: ${operator.requirementStatus}`,
        ),
      );
      for (const call of operator.calls ?? []) {
        card.append(element("code", call.head ?? ""), element("pre", call.expression ?? ""));
        const table = element("table");
        const header = element("tr");
        for (const text of [t("Parameter"), t("Value"), t("Type"), t("Implicit arguments")])
          header.append(element("th", text));
        const head = element("thead");
        head.append(header);
        table.append(head);
        const rows = element("tbody");
        for (const argument of call.arguments ?? []) {
          const cells = element("tr");
          for (const text of [
            argument.parameter,
            argument.value,
            argument.type,
            argument.instance ? "instance" : argument.implicit ? "implicit" : "explicit",
          ])
            cells.append(element("td", String(text ?? "")));
          rows.append(cells);
        }
        table.append(rows);
        card.append(table);
      }
      card.append(disclosure(t("Source evidence and checks"), tree(operator, highlight)));
      body.append(card);
    }
    if (!row.operators.length) body.append(element("p", t("No operators in this formula.")));
  }

  async function load(force = false): Promise<void> {
    if (!dialog.open) return;
    const source = currentSource();
    if (!force && source === loadedSource) return;
    const retained = report !== null && source === loadedSource;
    const selected = retained ? select.value : null;
    const generation = ++token;
    controller?.abort();
    controller = new AbortController();
    status.textContent = retained ? t("Checking correspondence updates…") : t("Loading correspondence…");
    if (!retained) {
      body.replaceChildren();
      select.replaceChildren();
      select.disabled = true;
    }
    try {
      if (project.static) throw new Error(t("Correspondence inspection is available in the live viewer."));
      const url = `${mountPrefix()}${project.mount}/correspondence.json?source=${encodeURIComponent(source)}`;
      const response = await fetch(url, { cache: "no-cache", signal: controller.signal });
      if (!response.ok) throw new Error(t("Correspondence could not be loaded. Retry after validation."));
      const data = (await response.json()) as CorrespondenceReport;
      if (generation !== token) return;
      report = data;
      loadedSource = source;
      select.replaceChildren();
      if (data.status === "unavailable") {
        status.textContent = t("No correspondence report is available for this chapter.");
        return;
      }
      status.textContent =
        data.status === "current"
          ? t("Current validation")
          : t("Historical evidence: source, rules or Lean dependencies have changed.");
      if (data.reasons?.length) status.append(document.createTextNode(` ${data.reasons.join(", ")}`));
      for (const [index, row] of data.formulas.entries()) {
        const option = element(
          "option",
          `#${row.index} · L${row.line} · ${row.book.replace(/\s+/g, " ").slice(0, 90)}`,
        );
        option.value = String(index);
        select.append(option);
      }
      select.disabled = !data.formulas.length;
      const active = state.entries[state.activeIndex];
      select.value =
        preferredFormula !== null
          ? String(data.formulas.findIndex((row) => row.index === preferredFormula))
          : selected !== null && Number(selected) < data.formulas.length
            ? selected
            : String(nearestFormula(data.formulas, active?.match?.startOffset ?? 0));
      preferredFormula = null;
      render();
    } catch (error) {
      if (generation !== token || controller?.signal.aborted) return;
      loadedSource = "";
      status.textContent = String((error as Error).message);
    }
  }
  select.addEventListener("change", render);
  reload.addEventListener("click", () => void load(true));
  document.getElementById("correspondence-open")!.addEventListener("click", () => {
    dialog.showModal();
    void load(true);
  });
  document.getElementById("correspondence-close")!.addEventListener("click", () => dialog.close());
  dialog.addEventListener("close", () => {
    ++token;
    controller?.abort();
  });
  refresh = (force) => {
    if (force && !dialog.open) loadedSource = "";
    void load(force);
  };
  openFormula = (index) => {
    preferredFormula = index;
    if (!dialog.open) dialog.showModal();
    void load(true);
  };
}

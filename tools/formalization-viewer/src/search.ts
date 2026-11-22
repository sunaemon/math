import { repoPath } from "./util.js";
import { t, matchCount, searchScopeLabel } from "./i18n.js";
import { setHTML } from "./safe-html.js";
import { project, state, els } from "./state.js";
import { lineHits, pdfHits, PaneSearchSession, nearbyHitPages, type PaneHit } from "./pane-search.js";
import { pdfPageText } from "./pdf-page-text.js";
import { parallelPdfSearchState, renderVisibleParallelPdfPages, prefetchParallelPdfPage } from "./parallel-pdf.js";
import { renderVisiblePdfPages, renderPdfPage } from "./pdf.js";
import { scrollPane, paneViewportHeight } from "./pane-scroll.js";
const SEARCH_ICON =
  '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true" focusable="false"><circle cx="10.5" cy="10.5" r="6.5"/><path d="m16 16 5 5"/></svg>';
interface Hit {
  url: string;
  meta: { title?: string; source?: string; line?: string };
  excerpt: string;
}
interface Engine {
  destroy?(): Promise<void>;
  options(options: Record<string, unknown>): Promise<unknown>;
  search(query: string): Promise<{ results: Array<{ data(): Promise<Hit> }> }>;
}
type Scope = "book" | "md" | "lean" | "tex" | "pdf" | "pdf-peer";

export function initSearch(
  navigateBook: (source: string, line: number) => Promise<void>,
  ensurePdfLoaded: (name: "pdf" | "pdf-peer") => Promise<void> = async () => {},
): { searchBook(query: string, limit: number, signal?: AbortSignal): Promise<unknown> } {
  const labels: Record<Scope, string> = {
    book: t("本文（全章）"),
    md: "Markdown",
    lean: "Lean",
    tex: "TeX",
    pdf: "PDF",
    "pdf-peer": project.parallelPdf?.label ? t(project.parallelPdf?.label) : t("Parallel PDF"),
  };
  const button = document.createElement("button");
  button.id = "book-search-toggle";
  button.type = "button";
  button.className = "vo-link book-search-menu-action";
  button.title = `${t("Full-text search")} (⌘/Ctrl+K)`;
  button.setAttribute("aria-label", t("全文検索"));
  setHTML(button, SEARCH_ICON);
  button.append(document.createTextNode(t("Full-text search")));
  button.setAttribute("aria-haspopup", "dialog");
  const dialog = document.createElement("dialog");
  dialog.id = "book-search";
  dialog.setAttribute("aria-label", t("全文検索"));
  const header = document.createElement("header");
  const label = document.createElement("label");
  setHTML(label, SEARCH_ICON);
  label.title = t("全文検索");
  label.htmlFor = "book-search-input";
  const close = document.createElement("button");
  close.type = "button";
  close.className = "icon-button";
  close.title = t("Close");
  close.setAttribute("aria-label", t("Close"));
  setHTML(
    close,
    '<svg width="16" height="16" viewBox="0 0 16 16" aria-hidden="true"><path d="m4 4 8 8M12 4l-8 8" stroke="currentColor" stroke-width="1.5"/></svg>',
  );
  close.onclick = () => (paneOpen ? closePaneSearch() : dialog.close());

  const scopes = (Object.keys(labels) as Scope[]).filter((name) => name !== "pdf-peer" || !!project.parallelPdf);
  const caption = document.createElement("span");
  caption.className = "search-caption";
  caption.textContent = labels.book;
  header.append(label, caption, close);
  const input = document.createElement("input");
  input.id = "book-search-input";
  input.type = "search";
  input.setAttribute("aria-label", t("Full-text search"));
  input.placeholder = t("検索語を入力");
  input.autocomplete = "off";
  const status = document.createElement("p");
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  const nav = document.createElement("div");
  nav.className = "search-navigation";
  const previous = document.createElement("button"),
    next = document.createElement("button");
  previous.type = next.type = "button";
  for (const [control, title, path] of [
    [previous, t("Previous match"), "m4 10 4-4 4 4"],
    [next, t("Next match"), "m4 6 4 4 4-4"],
  ] as const) {
    control.className = "icon-button";
    control.title = title;
    control.setAttribute("aria-label", title);
    setHTML(
      control,
      `<svg width="16" height="16" viewBox="0 0 16 16" aria-hidden="true"><path d="${path}" fill="none" stroke="currentColor" stroke-width="1.5"/></svg>`,
    );
  }
  previous.disabled = next.disabled = true;
  nav.append(previous, next);
  const list = document.createElement("ol");
  list.id = "book-search-results";
  const more = document.createElement("button");
  more.id = "book-search-more";
  more.type = "button";
  more.textContent = t("Show more results");
  more.hidden = true;
  const queryRow = document.createElement("div");
  queryRow.className = "search-query-row";
  queryRow.append(input, nav);
  dialog.append(header, queryRow, status, list, more);
  document.body.append(dialog);
  const menu = document.getElementById("settings-menu");
  (menu?.querySelector(".vo-section") ?? menu ?? document.body).append(button);
  const paneBar = document.createElement("section");
  paneBar.id = "pane-search";
  paneBar.className = "pane-search-bar";
  paneBar.setAttribute("role", "search");
  paneBar.hidden = true;
  document.body.append(paneBar);
  let paneOpen = false,
    currentScope: Scope = "book",
    returnFocus: HTMLElement | null = null;
  const isOpen = () => dialog.open || paneOpen;
  const clearMarks = () => {
    document.querySelectorAll(".line.search-hit").forEach((mark) => mark.classList.remove("search-hit"));
    document.querySelectorAll(".pdf-search-hit").forEach((mark) => mark.remove());
  };
  const syncSearchButtons = () => {
    for (const control of document.querySelectorAll<HTMLElement>(".pane-search[data-search-pane]"))
      control.setAttribute("aria-expanded", String(paneOpen && control.dataset.searchPane === currentScope));
  };
  const closePaneSearch = (restoreFocus = true) => {
    if (!paneOpen) return;
    queries.set(currentScope, input.value);
    paneOpen = false;
    session = undefined;
    extending = undefined;
    advanceAfterLoad = false;
    paneHits = [];
    actions = [];
    addPaneActions = () => {};
    clearTimeout(prefetchTimer);
    prefetchRevision++;
    paneBar.hidden = true;
    document.body.classList.remove("pane-search-active");
    syncSearchButtons();
    sequence++;
    clearTimeout(timer);
    clearMarks();
    if (restoreFocus && returnFocus?.isConnected) returnFocus.focus({ preventScroll: true });
  };
  let engine: Promise<Engine> | undefined,
    sequence = 0,
    sourceVersion = 0,
    timer: ReturnType<typeof setTimeout> | undefined,
    activeScope: Scope = "md",
    selected = -1;
  const queries = new Map<Scope, string>();
  let actions: Array<() => void> = [];
  let session: PaneSearchSession | undefined;
  let extending: Promise<void> | undefined;
  let advanceAfterLoad = false;
  let addPaneActions = () => {};
  let paneHits: PaneHit[] = [],
    prefetchRevision = 0;
  let prefetchTimer: ReturnType<typeof setTimeout> | undefined;
  const scope = () => currentScope;
  const identity = (name: Scope): unknown =>
    name === "pdf"
      ? state.pdf.document
      : name === "pdf-peer"
        ? parallelPdfSearchState().document
        : name === "book"
          ? project.dir
          : state.selectedSources[name];
  const load = (announce = true) =>
    (engine ??= (async () => {
      if (announce) status.textContent = t("検索索引を読み込み中…");
      const base = new URL("./pagefind/", location.href);
      const entry = new URL("pagefind.js", base);
      entry.searchParams.set("v", String(sourceVersion));
      const module = (await import(entry.href)) as Engine;
      await module.options({ bundlePath: base.href });
      return module;
    })().catch((error) => {
      engine = undefined;
      throw error;
    }));
  const jump = (name: Scope, hit: PaneHit) => {
    if (name === "md" || name === "lean" || name === "tex") {
      const pane = state.panes[name],
        node = pane?.querySelector<HTMLElement>(`.line[data-line="${hit.line}"]`);
      document.querySelectorAll(".line.search-hit").forEach((mark) => mark.classList.remove("search-hit"));
      if (node) {
        for (let parent = node.parentElement; parent && pane.contains(parent); parent = parent.parentElement)
          if (parent instanceof HTMLDetailsElement) parent.open = true;
        node.classList.add("search-hit");
        node.scrollIntoView({ block: "center" });
      }
    } else if (name === "pdf" || name === "pdf-peer") {
      const peer = name === "pdf-peer",
        snapshot = peer ? parallelPdfSearchState() : { pages: state.pdf.pageStates };
      const page = snapshot.pages.get(hit.page!);
      const pane = peer ? els.pdfPeerViewer : els.pdfViewer;
      if (page && pane) {
        document.querySelectorAll(".pdf-search-hit").forEach((mark) => mark.remove());
        const mark = document.createElement("span");
        mark.className = "pdf-search-hit";
        mark.setAttribute("aria-hidden", "true");
        mark.style.top = `${(hit.fraction ?? 0) * 100}%`;
        page.el.append(mark);
        scrollPane(pane, {
          top: Math.max(
            0,
            page.el.offsetTop + (hit.fraction ?? 0) * page.el.offsetHeight - paneViewportHeight(pane) * 0.35,
          ),
          left: pane.scrollLeft,
          behavior: "auto",
        });
        if (peer) renderVisibleParallelPdfPages();
        else renderVisiblePdfPages();
      }
    }
  };
  const prefetchAround = () => {
    clearTimeout(prefetchTimer);
    const revision = ++prefetchRevision,
      queryRevision = sequence,
      name = currentScope;
    if (name !== "pdf" && name !== "pdf-peer") return;
    const doc = identity(name),
      token = state.pdf.renderToken;
    const pages = nearbyHitPages(paneHits, selected);
    prefetchTimer = setTimeout(() => {
      void (async () => {
        for (const page of pages) {
          if (!paneOpen || revision !== prefetchRevision || queryRevision !== sequence || doc !== identity(name))
            return;
          if (name === "pdf") await renderPdfPage(page, token);
          else await prefetchParallelPdfPage(page);
        }
      })().catch(() => {});
    }, 120);
  };
  const run = async () => {
    const current = ++sequence,
      name = scope(),
      query = input.value.trim();
    let key = identity(name);
    queries.set(name, input.value);
    list.replaceChildren();
    more.hidden = true;
    more.onclick = null;
    clearMarks();
    actions = [];
    session = undefined;
    extending = undefined;
    advanceAfterLoad = false;
    paneHits = [];
    selected = -1;
    previous.disabled = next.disabled = true;
    if (!query) {
      status.textContent = paneOpen ? "- / -" : "";
      return;
    }
    status.textContent = t("検索中…");
    const valid = () => current === sequence && isOpen() && currentScope === name && identity(name) === key;
    try {
      if (name === "book") {
        const result = await (await load()).search(query);
        if (!valid()) return;
        const appendBatch = async () => {
          more.disabled = true;
          try {
            const hits = await Promise.all(
              result.results.slice(actions.length, actions.length + 30).map((hit) => hit.data()),
            );
            if (!valid()) return;
            for (const hit of hits) {
              const item = document.createElement("li"),
                link = document.createElement("a"),
                excerpt = document.createElement("p"),
                path = document.createElement("small");
              const source = String(hit.meta.source ?? ""),
                line = Number(hit.meta.line);
              const target = new URL(location.href);
              target.searchParams.delete("marker");
              target.searchParams.delete("skip");
              target.searchParams.set("searchSource", source);
              target.searchParams.set("searchLine", String(line));
              link.href = target.href;
              link.textContent = hit.meta.title || source;
              const go = () => {
                dialog.close();
                void navigateBook(source, line);
              };
              actions.push(go);
              link.onclick = (event) => {
                if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
                event.preventDefault();
                go();
              };
              setHTML(excerpt, hit.excerpt);
              path.textContent = `${source.split("/").pop()}:${line}`;
              item.append(link, excerpt, path);
              list.append(item);
            }
            status.textContent = matchCount(result.results.length, actions.length);
            previous.disabled = next.disabled = !actions.length;
            if (actions.length === result.results.length && document.activeElement === more)
              list.querySelector<HTMLAnchorElement>("li:last-child a")?.focus();
            more.hidden = actions.length >= result.results.length;
          } catch {
            if (valid())
              status.textContent = t("検索に失敗しました。接続または読み込み状態を確認して再検索してください。");
          } finally {
            if (valid()) more.disabled = false;
          }
        };
        more.onclick = () => {
          if (valid()) void appendBatch();
        };
        await appendBatch();
        if (!valid()) return;
      } else {
        if (name === "pdf" || name === "pdf-peer") {
          status.textContent = t("PDF を読み込み中…");
          const path = state.pdf.path;
          await ensurePdfLoaded(name);
          if (current !== sequence || !isOpen() || state.pdf.path !== path) return;
          key = identity(name);
          status.textContent = t("検索中…");
        }
        const doc =
          name === "pdf" ? state.pdf.document : name === "pdf-peer" ? parallelPdfSearchState().document : null;
        if (!doc && (name === "pdf" || name === "pdf-peer")) {
          status.textContent = t("PDF を読み込めませんでした。再検索すると読み込みを再試行します。");
          return;
        }
        const batch = new PaneSearchSession(
          doc ? pdfHits(doc, query, valid, pdfPageText) : lineHits(state.sources?.[name] ?? "", query),
          valid,
        );
        session = batch;
        await batch.loadMore();
        if (!valid()) return;
        paneHits = batch.hits;
        addPaneActions = () => {
          actions.push(
            ...batch.hits.slice(actions.length).map((hit) => () => {
              if (identity(name) !== key) {
                void run();
                return;
              }
              jump(name, hit);
            }),
          );
        };
        addPaneActions();
        selected = actions.length ? 0 : -1;
        if (selected >= 0) actions[selected]();
        updatePaneCount();
        prefetchAround();
      }
      previous.disabled = next.disabled = !actions.length;
    } catch {
      if (valid()) status.textContent = t("検索に失敗しました。接続または読み込み状態を確認して再検索してください。");
    }
  };
  const updatePaneCount = () => {
    if (!paneOpen) return;
    status.textContent = `${selected < 0 ? 0 : selected + 1} / ${actions.length}${session?.hasMore ? "+" : ""}`;
  };
  const extendResults = (advance = false) => {
    advanceAfterLoad ||= advance;
    if (extending || !session?.hasMore) return;
    const batch = session,
      revision = sequence,
      previousEnd = actions.length - 1;
    const pending = (async () => {
      await batch.loadMore();
      if (!paneOpen || revision !== sequence || session !== batch) return;
      addPaneActions();
      updatePaneCount();
      prefetchAround();
      if (advanceAfterLoad) {
        advanceAfterLoad = false;
        if (selected === previousEnd && selected + 1 < actions.length) step(1);
      }
    })();
    extending = pending;
    void pending
      .catch(() => {
        if (paneOpen && revision === sequence && session === batch)
          status.textContent = t("検索に失敗しました。接続または読み込み状態を確認して再検索してください。");
      })
      .finally(() => {
        if (extending === pending) extending = undefined;
      });
  };
  const step = (direction: number) => {
    if (!actions.length) return;
    if (direction < 0) advanceAfterLoad = false;
    if (direction > 0 && selected === actions.length - 1 && session?.hasMore) {
      extendResults(true);
      return;
    }
    selected =
      selected < 0
        ? direction > 0
          ? 0
          : actions.length - 1
        : (selected + direction + actions.length) % actions.length;
    list.querySelectorAll(".is-selected").forEach((item) => item.classList.remove("is-selected"));
    list.children[selected]?.classList.add("is-selected");
    actions[selected]();
    updatePaneCount();
    prefetchAround();
    if (direction > 0 && paneOpen && session?.hasMore && actions.length - selected - 1 <= 100) extendResults();
  };
  previous.onclick = () => step(-1);
  next.onclick = () => step(1);
  input.oninput = () => {
    sequence++;
    clearTimeout(prefetchTimer);
    prefetchRevision++;
    clearTimeout(timer);
    queries.set(scope(), input.value);
    timer = setTimeout(() => void run(), 180);
  };
  input.onkeydown = (event) => {
    if (event.key === "Enter") {
      event.preventDefault();
      step(event.shiftKey ? -1 : 1);
    }
  };
  dialog.addEventListener("close", () => {
    if (dialog.open || paneOpen) return;
    queries.set("book", input.value);
    sequence++;
    clearTimeout(timer);
  });
  const open = (name: Scope) => {
    if (!scopes.includes(name)) return;
    const wasPaneOpen = paneOpen;
    closePaneSearch(false);
    if (dialog.open) dialog.close();
    if (!wasPaneOpen) returnFocus = document.activeElement as HTMLElement;
    currentScope = name;
    input.value = queries.get(name) ?? "";
    input.setAttribute("aria-label", searchScopeLabel(labels[name]));
    if (name === "book") {
      header.append(close);
      queryRow.replaceChildren(input, nav);
      dialog.append(queryRow, status, list, more);
      const settings = document.getElementById("settings-menu");
      if (settings?.matches(":popover-open")) settings.hidePopover();
      dialog.showModal();
    } else {
      const host = state.paneSections?.[name];
      if (!host || host.hidden) return;
      paneOpen = true;
      paneBar.dataset.searchScope = name;
      paneBar.setAttribute("aria-label", searchScopeLabel(labels[name]));
      queryRow.replaceChildren(input, status, nav, close);
      paneBar.replaceChildren(queryRow);
      host.append(paneBar);
      paneBar.hidden = false;
      document.body.classList.add("pane-search-active");
      syncSearchButtons();
    }
    input.focus();
    input.select();
    void run();
  };
  document.addEventListener("pane-layout-changed", () => {
    if (!paneOpen) return;
    const host = state.paneSections?.[currentScope];
    if (host?.hidden || (state.layout.maximized && state.layout.maximized !== currentScope)) closePaneSearch(false);
  });
  document.addEventListener("book-search-invalidated", () => {
    sourceVersion++;
    sequence++;
    void engine?.then((module) => module.destroy?.()).catch(() => {});
    engine = undefined;
    if (dialog.open && scope() === "book") {
      list.replaceChildren();
      more.hidden = true;
      more.onclick = null;
      actions = [];
      previous.disabled = next.disabled = true;
      status.textContent = t("本文が更新されました。再検索してください。");
    }
  });
  button.onclick = () => open("book");
  const focusedSearch = document.createElement("button");
  focusedSearch.id = "pane-search-focused";
  focusedSearch.type = "button";
  focusedSearch.className = "icon-button pane-search";
  focusedSearch.title = t("Full-text search");
  focusedSearch.setAttribute("aria-label", t("Full-text search"));
  focusedSearch.setAttribute("aria-controls", "pane-search");
  setHTML(focusedSearch, SEARCH_ICON);
  focusedSearch.hidden = !scopes.includes(state.layout.maximized as Scope);
  focusedSearch.onclick = () => open(state.layout.maximized as Scope);
  els.paneTools?.prepend(focusedSearch);

  for (const name of scopes.filter((name) => name !== "book")) {
    const section = state.paneSections?.[name];
    const host = section?.querySelector(".pane-actions") ?? section?.querySelector(".pane-header");
    if (!host) continue;
    const find = document.createElement("button");
    find.type = "button";
    find.className = "icon-button pane-search";
    setHTML(find, SEARCH_ICON);
    find.title = `${searchScopeLabel(labels[name])} (⌘/Ctrl+F)`;
    find.setAttribute("aria-controls", "pane-search");
    find.dataset.searchPane = name;
    find.setAttribute("aria-expanded", "false");
    find.setAttribute("aria-label", searchScopeLabel(labels[name]));
    find.onclick = () => {
      activeScope = name;
      if (paneOpen && currentScope === name) closePaneSearch();
      else open(name);
    };
    host.append(find);
  }
  // Keep DOM and keyboard order aligned: content operations, document tools,
  // then pane layout. Metadata stays before the controls.
  const actionOrder = [
    ".pane-search",
    '[data-overlay="highlights"]',
    '[data-overlay="links"]',
    ".build-status",
    ".pane-open",
    ".pane-maximize",
    ".pane-close",
  ];
  for (const host of document.querySelectorAll(".pane-header > .pane-actions")) {
    const rank = (node: Element) => actionOrder.findIndex((selector) => node.matches(selector));
    host.append(...[...host.children].sort((a, b) => rank(a) - rank(b)));
  }
  const remember = (event: Event) => {
    const pane = (event.target as Element)?.closest?.<HTMLElement>(".pane[data-pane]")?.dataset.pane;
    if (pane && pane !== "book" && scopes.includes(pane as Scope)) activeScope = pane as Scope;
  };
  document.addEventListener("pointerdown", remember, true);
  document.addEventListener("focusin", remember, true);
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && paneOpen) {
      event.preventDefault();
      closePaneSearch();
      return;
    }
    if (
      (event.ctrlKey || event.metaKey) &&
      !event.altKey &&
      (event.key.toLowerCase() === "f" || event.key.toLowerCase() === "k")
    ) {
      event.preventDefault();
      const visibleScope =
        state.paneSections?.[activeScope]?.hidden === false
          ? activeScope
          : (scopes.find((name) => name !== "book" && state.paneSections?.[name]?.hidden === false) ?? activeScope);
      open(
        event.key.toLowerCase() === "k"
          ? "book"
          : isOpen()
            ? scope()
            : (state.layout.maximized as Scope) || visibleScope,
      );
    }
  });
  return {
    searchBook: async (query, limit, signal) => {
      signal?.throwIfAborted();
      const result = await (await load(false)).search(query);
      const hits = await Promise.all(result.results.slice(0, limit).map((hit) => hit.data()));
      signal?.throwIfAborted();
      return {
        total: result.results.length,
        hits: hits.map((hit) => ({
          title: hit.meta.title,
          source: repoPath(String(hit.meta.source ?? "")),
          line: Number(hit.meta.line),
          excerpt: hit.excerpt.replace(/<[^>]*>/g, ""),
          url: hit.url,
        })),
      };
    },
  };
}

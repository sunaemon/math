import { t } from "./i18n.js";
import { setHTML } from "./safe-html.js";
import { pdfDestination } from "./pdf-destinations.js";
import { resolveReference, type ReferenceRegistry } from "./link-preview.js";
import { pdfPageText } from "./pdf-page-text.js";
import {
  resolveDefinition,
  type DefinitionEntry,
  type DefinitionRegistry,
  type DefinitionUse,
} from "./definition-registry.js";
import { termTarget } from "./pdf-chapter.js";
import { project } from "./state.js";

export type FollowPdfLink = (dest: any, preferDefinition?: boolean) => Promise<void>;
export interface TermLinkContext {
  document: (definition?: unknown) => Promise<any>;
  current: () => boolean;
  references?: () => ReferenceRegistry | undefined;
  definitions?: () => DefinitionRegistry | undefined;
  macros?: () => Record<string, string>;
  chapterTitles?: () => Record<string, string>;
}

let popup: HTMLElement | null = null;
// Registered by the app shell: open the source pane at a use's file and line.
// Without a registration (tests, static embeds) previews list uses as text.
let openUseHandler: ((use: DefinitionUse) => void) | null = null;
export function setOpenDefinitionUse(handler: ((use: DefinitionUse) => void) | null): void {
  openUseHandler = handler;
}
let owner: HTMLElement | null = null;
let timer: ReturnType<typeof setTimeout> | undefined;
let generation = 0;
let listening = false;
let restoringFocus = false;
let pinned = false;
let contextPoint: HTMLElement | null = null;

export function dismissTermPopup(restoreFocus = false): void {
  clearTimeout(timer);
  generation += 1;
  if (popup) hidePopup(popup);
  popup?.remove();
  popup = null;
  contextPoint?.remove();
  contextPoint = null;
  owner?.classList.remove("term-popup-anchor");
  pinned = false;
  owner?.removeAttribute("aria-describedby");
  owner?.removeAttribute("aria-controls");
  owner?.setAttribute("aria-expanded", "false");
  if (owner?.classList.contains("pdf-term-link")) owner.setAttribute("aria-haspopup", "menu");
  if (restoreFocus && owner?.isConnected) {
    restoringFocus = true;
    owner.focus({ preventScroll: true });
    restoringFocus = false;
  }
  owner = null;
}

// The popup is a real (manual) popover: the top layer keeps it above the PDF
// panes' stacking contexts without a z-index arms race. Dismissal stays
// hand-rolled (hover intent, scroll, pinning), so only the layer changes.
function showPopup(element: HTMLElement): void {
  const el = element as any;
  if (typeof el.showPopover === "function" && !element.matches(":popover-open")) el.showPopover();
}
function hidePopup(element: HTMLElement): void {
  const el = element as any;
  if (typeof el.showPopover === "function" && element.matches(":popover-open")) el.hidePopover();
}

function keyboardOwnerIsVisible(): boolean {
  if (!owner?.isConnected || document.activeElement !== owner || !owner.matches(":focus-visible")) return false;
  const rect = owner.getBoundingClientRect();
  const pane = owner.closest<HTMLElement>(".pdf-viewer, .source")?.getBoundingClientRect();
  return (
    rect.width > 0 &&
    rect.height > 0 &&
    rect.bottom > Math.max(0, pane?.top ?? 0) &&
    rect.top < Math.min(innerHeight, pane?.bottom ?? innerHeight) &&
    rect.right > Math.max(0, pane?.left ?? 0) &&
    rect.left < Math.min(innerWidth, pane?.right ?? innerWidth)
  );
}

function listenForDismissal(): void {
  if (listening) return;
  listening = true;
  document.addEventListener(
    "pointerdown",
    (event) => {
      if (popup && !popup.contains(event.target as Node) && !owner?.contains(event.target as Node)) dismissTermPopup();
    },
    true,
  );
  document.addEventListener(
    "keydown",
    (event) => {
      if (event.key === "Escape" && popup) {
        event.preventDefault();
        event.stopPropagation();
        dismissTermPopup(true);
      }
    },
    true,
  );
  document.addEventListener(
    "scroll",
    (event) => {
      // Tab focuses first, then the browser scrolls the link into view.
      // CSS anchors follow that scroll; dismissing here loses the new preview.
      if (!popup?.contains(event.target as Node) && !keyboardOwnerIsVisible()) dismissTermPopup();
    },
    true,
  );
  window.addEventListener("resize", () => {
    if (!keyboardOwnerIsVisible()) dismissTermPopup();
  });
}

function createPopup(anchor: HTMLElement, menu: boolean, point?: { x: number; y: number }): HTMLElement {
  dismissTermPopup();
  owner = anchor;
  if (point) {
    contextPoint = document.createElement("span");
    contextPoint.className = "term-context-position";
    contextPoint.setAttribute("aria-hidden", "true");
    contextPoint.style.setProperty("--context-x", `${point.x}px`);
    contextPoint.style.setProperty("--context-y", `${point.y}px`);
    document.body.append(contextPoint);
  } else anchor.classList.add("term-popup-anchor");
  const element = document.createElement("div");
  element.className = menu ? "term-context-menu" : "term-definition-preview";
  element.classList.toggle("is-positioned-at-pointer", !!point);
  element.setAttribute("popover", "manual");
  element.id = "term-link-popup";
  element.setAttribute("role", menu ? "menu" : "tooltip");
  element.setAttribute("aria-label", menu ? t("Term navigation") : t("Definition excerpt"));
  document.body.append(element);
  showPopup(element);
  popup = element;
  if (menu) {
    anchor.setAttribute("aria-expanded", "true");
    anchor.setAttribute("aria-controls", element.id);
  } else anchor.setAttribute("aria-describedby", element.id);
  return element;
}

function renderUses(definition: DefinitionEntry, context: TermLinkContext, interactive: boolean): HTMLElement | null {
  const uses = definition.usedBy;
  if (!uses?.length) return null;
  const section = document.createElement("div");
  section.className = "term-preview-uses";
  const title = document.createElement("div");
  title.className = "term-preview-uses-title";
  title.textContent = t("Used in");
  section.append(title);
  const titles = context.chapterTitles?.() ?? project.chapterTitles;
  const shown = uses.slice(0, 20);
  for (const use of shown) {
    const where = document.createElement("span");
    where.className = "term-preview-use-where";
    where.textContent = `${titles?.[use.chapter] ?? use.chapter}${use.section ? ` — ${use.section}` : ""}`;
    const excerpt = document.createElement("span");
    excerpt.className = "term-preview-use-excerpt";
    excerpt.textContent = use.excerpt;
    if (interactive && openUseHandler) {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "term-preview-use";
      button.append(where, excerpt);
      button.addEventListener("click", () => {
        const handler = openUseHandler;
        dismissTermPopup();
        handler?.(use);
      });
      section.append(button);
    } else {
      const row = document.createElement("div");
      row.className = "term-preview-use";
      row.append(where, excerpt);
      section.append(row);
    }
  }
  if (uses.length > shown.length) {
    const more = document.createElement("div");
    more.className = "term-preview-uses-more";
    more.textContent = t("and {0} more", uses.length - shown.length);
    section.append(more);
  }
  return section;
}

async function renderDefinition(
  name: string,
  body: HTMLElement,
  current: () => boolean,
  context: TermLinkContext,
  interactive = false,
): Promise<void> {
  const registry = context.definitions ? context.definitions() : project.definitionRegistry;
  const definition = resolveDefinition(registry, name);
  if (!definition) {
    body.textContent = t("The definition is not included in this book.");
    return;
  }
  if (!current()) return;
  const label = document.createElement("div");
  label.className = "term-preview-page";
  label.textContent = (context.chapterTitles?.() ?? project.chapterTitles)?.[definition.chapter] ?? definition.chapter;
  const excerpt = document.createElement("div");
  excerpt.className = "term-preview-source";
  if (definition.html !== undefined) setHTML(excerpt, definition.html);
  else excerpt.textContent = definition.source;
  const uses = renderUses(definition, context, interactive);
  body.replaceChildren(...(uses ? [label, excerpt, uses] : [label, excerpt]));
}

export function attachTermLink(
  anchor: HTMLAnchorElement,
  dest: unknown,
  context: TermLinkContext,
  follow: FollowPdfLink,
): void {
  const registry = () => (context.definitions ? context.definitions() : project.definitionRegistry);
  const record = resolveDefinition(registry(), dest);
  const section = record?.kind === "section";
  const target =
    termTarget(dest) ??
    (section ? { definition: dest as string, references: dest as string, label: t("Section preview") } : null);
  const reference = resolveReference(context.references?.() ?? project.references, dest);
  const external = typeof dest === "string" && /^(?:https?:|mailto:)/i.test(dest) ? dest : null;
  const term = !!target && !section;
  const destination = target ?? {
    definition: typeof dest === "string" ? dest : "",
    references: "",
    label: t("Linked passage"),
  };
  if (record?.canonicalDefinition) destination.definition = record.canonicalDefinition;
  listenForDismissal();
  anchor.classList.add(
    "pdf-link-preview",
    section
      ? "pdf-section-link"
      : term
        ? "pdf-term-link"
        : reference
          ? "pdf-reference-link"
          : external
            ? "pdf-external-link"
            : "pdf-passage-link",
  );
  anchor.dataset.definition = destination.definition;
  anchor.dataset.references = destination.references;
  const visibleLabel = anchor.textContent?.trim();
  const linkLabel = reference ? reference.source : external ? String(dest) : t("Linked passage");
  anchor.setAttribute("aria-label", visibleLabel ? `${visibleLabel}: ${linkLabel}` : linkLabel);
  anchor.removeAttribute("title");
  if (target)
    anchor.setAttribute("aria-label", section ? t("Section preview") : t("Definition of {0}", destination.label));
  if (term) anchor.setAttribute("aria-haspopup", "menu");
  let touchInput = false;
  const choices = [
    { label: t("Go to definition"), dest: destination.definition, preferDefinition: true },
    { label: t("Show references in index"), dest: destination.references, preferDefinition: false },
  ];
  const showPreview = (interactive = false) => {
    const element = createPopup(anchor, false);
    if (section) element.setAttribute("aria-label", t("Section excerpt"));
    pinned = interactive;
    const token = generation;
    const current = () => token === generation && anchor.isConnected && context.current();
    const header = document.createElement("strong");
    header.textContent = reference
      ? t("Reference")
      : external
        ? t("External link")
        : !target
          ? t("Linked passage")
          : section
            ? t("Section")
            : resolveDefinition(registry(), destination.definition)?.kind === "notation" &&
                !resolveDefinition(registry(), destination.definition)?.canonicalDefinition
              ? t("Notation")
              : t("Definition");
    const body = document.createElement("div");
    body.className = "term-preview-body";
    body.textContent = section ? t("Loading section…") : t("Loading definition…");
    element.append(header, body);
    if (interactive) {
      element.setAttribute("role", "dialog");
      anchor.setAttribute("aria-haspopup", "dialog");
      anchor.removeAttribute("aria-describedby");
      anchor.setAttribute("aria-expanded", "true");
      anchor.setAttribute("aria-controls", element.id);
      const actions = document.createElement("div");
      actions.className = "term-preview-actions";
      const buttons = choices.map((choice) => {
        const button = document.createElement("button");
        button.type = "button";
        button.textContent = choice.label;
        button.disabled = true;
        button.addEventListener("click", () => {
          dismissTermPopup();
          void follow(choice.dest, choice.preferDefinition).catch((error) =>
            console.error("[booklink] term navigation", error),
          );
        });
        actions.append(button);
        return button;
      });
      const close = document.createElement("button");
      close.type = "button";
      close.textContent = t("Close");
      close.addEventListener("click", () => dismissTermPopup(true));
      actions.append(close);
      element.append(actions);
      void context
        .document()
        .then(async (doc) => {
          const available = await Promise.all(choices.map((choice) => doc.getDestination(choice.dest)));
          if (!current()) return;
          buttons.forEach((button, index) => {
            button.disabled = !available[index];
            if (!available[index]) button.title = t("Not included in this book");
          });
        })
        .catch(() => {
          if (current())
            buttons.forEach((button) => {
              button.title = t("PDF unavailable");
            });
        });
    }
    element.addEventListener("mouseenter", () => clearTimeout(timer));
    element.addEventListener("mouseleave", () => {
      if (!pinned && !keyboardOwnerIsVisible()) dismissTermPopup();
    });
    void (async () => {
      if (reference) {
        if (reference.html !== undefined) setHTML(body, reference.html);
        else body.textContent = reference.source;
      } else if (external) body.textContent = String(dest);
      else if (target) await renderDefinition(destination.definition, body, current, context, interactive);
      else {
        const doc = await context.document(dest);
        const location = typeof dest === "string" ? await pdfDestination(doc, dest) : dest;
        if (!Array.isArray(location)) throw new Error("Missing PDF destination");
        const pageNumber =
          typeof location[0] === "number" ? location[0] + 1 : (await doc.getPageIndex(location[0])) + 1;
        const page = await doc.getPage(pageNumber);
        const text = await pdfPageText(page);
        const y = location[1]?.name === "FitH" || location[1]?.name === "FitBH" ? location[2] : location[3];
        const top = typeof y === "number" ? y : (page.view?.[3] ?? 1000);
        const excerpt = text.items
          .filter(
            (item: any) =>
              typeof item.str === "string" &&
              (item.transform?.[5] ?? 0) <= top + 12 &&
              (item.transform?.[5] ?? 0) >= top - 160,
          )
          .map((item: any) => item.str)
          .join(" ")
          .slice(0, 1200);
        if (current())
          body.textContent = `${t("Page")} ${pageNumber} — ${excerpt || t("Follow the link to view this passage.")}`;
      }
    })().catch((error) => {
      console.error("[booklink] definition preview", error);
      if (current()) body.textContent = t("Definition preview unavailable.");
    });
  };
  const schedulePreview = (immediate = false) => {
    if (window.getSelection()?.isCollapsed === false) return;
    if (!immediate && owner === anchor && keyboardOwnerIsVisible()) return;
    if (restoringFocus || touchInput || pinned || popup?.getAttribute("role") === "menu") return;
    dismissTermPopup();
    if (immediate && anchor.isConnected && context.current()) {
      showPreview();
      return;
    }
    const scheduled = generation;
    timer = setTimeout(() => {
      if (
        scheduled !== generation ||
        !anchor.isConnected ||
        !context.current() ||
        window.getSelection()?.isCollapsed === false
      )
        return;
      showPreview();
    }, 250);
  };
  const leave = () => {
    if (pinned || popup?.getAttribute("role") === "menu" || keyboardOwnerIsVisible()) return;
    clearTimeout(timer);
    timer = setTimeout(() => dismissTermPopup(), 180);
  };
  anchor.addEventListener("mouseenter", () => schedulePreview());
  anchor.addEventListener("focus", () => schedulePreview(anchor.matches(":focus-visible")));
  anchor.addEventListener("mouseleave", leave);
  anchor.addEventListener("blur", leave);
  if (!term) {
    anchor.addEventListener("click", () => dismissTermPopup());
    return;
  }
  anchor.addEventListener("pointerdown", (event) => {
    touchInput = event.pointerType === "touch" || event.pointerType === "pen";
  });
  anchor.addEventListener("keydown", () => {
    touchInput = false;
  });
  // Capture before appendPageLinks' navigation listener. Touch-generated clicks
  // can be MouseEvents in Safari, so retain the initiating pointer type as well.
  anchor.addEventListener(
    "click",
    (event) => {
      const pointerType = (event as PointerEvent).pointerType;
      const tapped = touchInput || pointerType === "touch" || pointerType === "pen";
      touchInput = false;
      if (tapped && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey) {
        event.preventDefault();
        event.stopImmediatePropagation();
        if (context.current()) showPreview(true);
      } else dismissTermPopup();
    },
    true,
  );
  const openMenu = (x?: number, y?: number) => {
    const point = x !== undefined && y !== undefined && (x !== 0 || y !== 0) ? { x, y } : undefined;
    const element = createPopup(anchor, true, point);
    const token = generation;
    const buttons = choices.map((choice) => {
      const button = document.createElement("button");
      button.type = "button";
      button.setAttribute("role", "menuitem");
      button.textContent = choice.label;
      button.disabled = true;
      button.addEventListener("click", () => {
        dismissTermPopup();
        void follow(choice.dest, choice.preferDefinition).catch((error) =>
          console.error("[booklink] term navigation", error),
        );
      });
      element.append(button);
      return button;
    });
    element.tabIndex = -1;
    element.focus({ preventScroll: true });
    element.addEventListener("keydown", (event) => {
      const enabled = buttons.filter((button) => !button.disabled);
      if (!["ArrowDown", "ArrowUp", "Home", "End"].includes(event.key) || !enabled.length) return;
      event.preventDefault();
      const at = enabled.indexOf(document.activeElement as HTMLButtonElement);
      const next =
        event.key === "Home"
          ? 0
          : event.key === "End"
            ? enabled.length - 1
            : (at + (event.key === "ArrowUp" ? -1 : 1) + enabled.length) % enabled.length;
      enabled[next].focus();
    });
    const known = choices.map((choice) => !!resolveDefinition(registry(), choice.dest));
    if (known.every(Boolean)) {
      buttons.forEach((button) => (button.disabled = false));
      buttons[0].focus({ preventScroll: true });
    } else {
      void context
        .document()
        .then(async (doc) => {
          const available = await Promise.all(choices.map((choice) => doc.getDestination(choice.dest)));
          if (token !== generation || !context.current()) return;
          buttons.forEach((button, index) => {
            button.disabled = !available[index];
            if (!available[index]) button.title = t("Not included in this book");
          });
          buttons.find((button) => !button.disabled)?.focus({ preventScroll: true });
        })
        .catch(() => {
          if (token === generation)
            buttons.forEach((button) => {
              button.title = t("PDF unavailable");
            });
        });
    }
  };
  anchor.addEventListener("contextmenu", (event) => {
    if (window.getSelection()?.isCollapsed === false) return;
    event.preventDefault();
    event.stopPropagation();
    openMenu(event.clientX, event.clientY);
  });
  anchor.addEventListener("keydown", (event) => {
    if (event.key !== "ContextMenu" && !(event.shiftKey && event.key === "F10")) return;
    event.preventDefault();
    openMenu();
  });
}

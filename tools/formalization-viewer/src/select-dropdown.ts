import { t } from "./i18n.js";
import { setHTML } from "./safe-html.js";
// A custom dropdown that visually replaces a native <select> (the native
// element stays in the DOM as the source of truth and for change events; this
// renders a styled field + listbox over it; the listbox is a real popover
// (top layer). It mirrors the marker
// palette's interaction model: the popover carries a search box and a keyboard-
// hints footer, options filter as you type, and ↑/↓/↵/esc drive the list.
// Self-contained DOM widget: its only non-DOM dependency is escapeHtml, and it
// never calls back into app.

import { escapeHtml } from "./util.js";
import { filterOptionIndices, clampIndex } from "./dropdown-filter.js";

let dropdownSerial = 0;

// Browsing a list must not summon a touch keyboard. Tab or an actual typed
// character explicitly enters search; tapping the input works natively too.
export function enterSearchFromList(event: KeyboardEvent, list: HTMLElement, search: HTMLInputElement): boolean {
  if (event.currentTarget !== list) return false;
  const typed = event.key.length === 1 && event.key !== " " && !event.ctrlKey && !event.metaKey && !event.altKey;
  if (!(event.key === "Tab" && !event.shiftKey) && !typed) return false;
  event.preventDefault();
  search.focus({ preventScroll: true });
  if (typed) {
    search.value += event.key;
    search.dispatchEvent(new Event("input", { bubbles: true }));
  }
  return true;
}

export function enhanceSelect(select: HTMLSelectElement | null): void {
  if (!select || (select as any)._enhanced) return;
  (select as any)._enhanced = true;
  const wrap = document.createElement("div");
  wrap.className = "cselect";
  select.parentNode!.insertBefore(wrap, select);
  wrap.appendChild(select);
  select.classList.add("cselect-native");
  select.tabIndex = -1;

  const field = document.createElement("button");
  field.type = "button";
  field.className = "cselect-field select-field";
  field.setAttribute("aria-haspopup", "listbox");
  field.setAttribute("aria-expanded", "false");
  const aria = t(
    select.getAttribute("aria-label") || select.labels?.[0]?.querySelector(".vo-row-label")?.textContent || "",
  );
  const labelEl = document.createElement("span");
  labelEl.className = "cselect-label select-field-label";
  const caret = document.createElement("span");
  caret.className = "select-caret";
  caret.setAttribute("aria-hidden", "true");
  field.append(labelEl, caret);

  const pop = document.createElement("div");
  pop.className = "cselect-popover";
  pop.setAttribute("popover", "manual");
  pop.hidden = true;
  // A real popover puts the list in the top layer, so it escapes pane
  // overflow and stacking contexts structurally instead of by z-index. The
  // `hidden` flag stays in sync around the show/hide calls (synchronously,
  // so no frame paints the wrong state) for the existing visibility checks.
  const popoverSupported = typeof (pop as any).showPopover === "function";
  const showPop = () => {
    if (popoverSupported && !pop.matches(":popover-open")) (pop as any).showPopover();
  };
  const hidePop = () => {
    if (popoverSupported && pop.matches(":popover-open")) (pop as any).hidePopover();
  };
  const search = document.createElement("input");
  search.type = "search";
  search.className = "cselect-search";
  search.autocomplete = "off";
  search.spellcheck = false;
  if (aria) search.setAttribute("aria-label", t("Search {0}", t(aria)));
  search.placeholder = aria ? t("Search {0}…", t(aria)) : t("Search…");
  const list = document.createElement("ul");
  list.tabIndex = -1;
  list.id = `select-list-${++dropdownSerial}`;
  search.setAttribute("role", "combobox");
  search.setAttribute("aria-controls", list.id);
  field.setAttribute("aria-controls", list.id);
  search.setAttribute("aria-expanded", "true");
  list.className = "cselect-list";
  list.setAttribute("role", "listbox");
  if (aria) list.setAttribute("aria-label", aria);
  const hints = document.createElement("div");
  hints.className = "cselect-hints";
  setHTML(hints, `<kbd>↑</kbd><kbd>↓</kbd> ${t("move")} · <kbd>↵</kbd> ${t("select")} · <kbd>esc</kbd> ${t("close")}`);
  pop.append(search, list, hints);
  wrap.append(field, pop);

  let highlight = 0; // position within the currently filtered list
  let filter = "";
  const options = () => Array.from(select.options);
  const filteredOptions = (): { opt: HTMLOptionElement; i: number }[] => {
    const opts = options();
    const labels = opts.map((opt) => ({ label: opt.textContent || "", value: opt.value }));
    return filterOptionIndices(labels, filter)
      .filter((i) => !opts[i].disabled)
      .map((i) => ({ opt: opts[i], i }));
  };
  const refresh = () => {
    const sel = select.selectedOptions[0];
    labelEl.textContent = sel ? sel.textContent || sel.value : "";
    labelEl.title = labelEl.textContent || "";
    if (aria) field.setAttribute("aria-label", t("{0}: {1}", t(aria), labelEl.textContent || ""));
  };
  const rows = () => Array.from(list.querySelectorAll(".cselect-option")) as HTMLElement[];
  const updateActive = () => {
    const active = rows()[highlight];
    for (const control of [search, list]) {
      if (active) control.setAttribute("aria-activedescendant", active.id);
      else control.removeAttribute("aria-activedescendant");
    }
  };
  const buildList = () => {
    const items = filteredOptions();
    highlight = clampIndex(items.length, highlight);
    setHTML(
      list,
      items.length
        ? items
            .map(
              ({ opt, i }, pos) =>
                `<li class="cselect-option${opt.selected ? " is-selected" : ""}${pos === highlight ? " is-highlight" : ""}" id="${list.id}-option-${i}" role="option" aria-selected="${opt.selected}" data-i="${i}" title="${escapeHtml(opt.textContent || "")}">${escapeHtml(opt.textContent || opt.value)}</li>`,
            )
            .join("")
        : `<li class="cselect-empty">${escapeHtml(t("No matches for “{0}”.", filter.trim()))}</li>`,
    );
    updateActive();
  };
  const close = () => {
    if (pop.hidden) return;
    hidePop();
    pop.hidden = true;
    field.setAttribute("aria-expanded", "false");
  };
  const open = (keyboard = false) => {
    filter = "";
    search.value = "";
    // Start on the selected option so ↑/↓ move relative to the current value.
    highlight = Math.max(
      0,
      filteredOptions().findIndex(({ opt }) => opt.selected),
    );
    buildList();
    pop.hidden = false;
    showPop();
    field.setAttribute("aria-expanded", "true");
    (keyboard ? search : list).focus({ preventScroll: true });
    (list.querySelector(".is-highlight") as HTMLElement | null)?.scrollIntoView({ block: "nearest" });
  };
  const setHighlight = (i: number) => {
    const items = rows();
    if (!items.length) return;
    highlight = clampIndex(items.length, i);
    items.forEach((el, idx) => el.classList.toggle("is-highlight", idx === highlight));
    updateActive();
    items[highlight]?.scrollIntoView({ block: "nearest" });
  };
  const choose = (i: number) => {
    const opt = options()[i];
    close();
    field.focus();
    if (opt && select.value !== opt.value) {
      select.value = opt.value;
      select.dispatchEvent(new Event("change", { bubbles: true }));
    }
  };
  const chooseHighlighted = () => {
    const li = rows()[highlight];
    if (li) choose(Number(li.dataset.i));
  };

  field.addEventListener("click", (event) => (pop.hidden ? open(event.isTrusted && event.detail === 0) : close()));
  field.addEventListener("keydown", (event) => {
    // Once open, the non-editable list owns keyboard navigation.
    if (pop.hidden && (event.key === "ArrowDown" || event.key === "Enter" || event.key === " ")) {
      event.preventDefault();
      open(true);
    }
  });
  search.addEventListener("input", () => {
    filter = search.value;
    highlight = 0;
    buildList();
  });
  const navigate = (event: KeyboardEvent) => {
    if (enterSearchFromList(event, list, search)) return;
    if (event.key === "ArrowDown") {
      event.preventDefault();
      setHighlight(highlight + 1);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      setHighlight(highlight - 1);
    } else if (event.key === "Enter" || (event.currentTarget === list && event.key === " ")) {
      event.preventDefault();
      chooseHighlighted();
    } else if (event.key === "Escape") {
      event.preventDefault();
      close();
      field.focus();
    }
  };
  search.addEventListener("keydown", navigate);
  list.addEventListener("keydown", navigate);
  list.addEventListener("click", (event) => {
    const li = (event.target as Element | null)?.closest(".cselect-option") as HTMLElement | null;
    if (li) choose(Number(li.dataset.i));
  });
  list.addEventListener("mousemove", (event) => {
    const li = (event.target as Element | null)?.closest(".cselect-option") as HTMLElement | null;
    if (!li) return;
    const pos = rows().indexOf(li);
    if (pos >= 0 && pos !== highlight) setHighlight(pos);
  });
  document.addEventListener("mousedown", (event) => {
    if (!wrap.contains(event.target as Node)) close();
  });

  // Keep the custom field synced with the native select on user change,
  // programmatic value sets, and option repopulation.
  select.addEventListener("change", refresh);
  const desc = Object.getOwnPropertyDescriptor(HTMLSelectElement.prototype, "value");
  if (desc && desc.get && desc.set) {
    Object.defineProperty(select, "value", {
      configurable: true,
      get() {
        return desc.get!.call(this);
      },
      set(v) {
        desc.set!.call(this, v);
        refresh();
        if (!pop.hidden) buildList();
      },
    });
  }
  new MutationObserver(() => {
    refresh();
    if (!pop.hidden) buildList();
  }).observe(select, { childList: true });
  refresh();
}

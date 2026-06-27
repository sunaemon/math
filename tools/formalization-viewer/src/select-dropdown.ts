// A custom dropdown that visually replaces a native <select> (the native
// element stays in the DOM as the source of truth and for change events; this
// renders a styled field + popover listbox over it). It mirrors the marker
// palette's interaction model: the popover carries a search box and a keyboard-
// hints footer, options filter as you type, and ↑/↓/↵/esc drive the list.
// Self-contained DOM widget: its only non-DOM dependency is escapeHtml, and it
// never calls back into app.

import { escapeHtml } from "./util.js";
import { filterOptionIndices, clampIndex } from "./dropdown-filter.js";

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
  field.className = "cselect-field";
  field.setAttribute("aria-haspopup", "listbox");
  field.setAttribute("aria-expanded", "false");
  const aria = select.getAttribute("aria-label");
  if (aria) field.setAttribute("aria-label", aria);
  const labelEl = document.createElement("span");
  labelEl.className = "cselect-label";
  const caret = document.createElement("span");
  caret.className = "cselect-caret";
  caret.setAttribute("aria-hidden", "true");
  caret.textContent = "▾";
  field.append(labelEl, caret);

  const pop = document.createElement("div");
  pop.className = "cselect-popover";
  pop.hidden = true;
  const search = document.createElement("input");
  search.type = "search";
  search.className = "cselect-search";
  search.autocomplete = "off";
  search.spellcheck = false;
  if (aria) search.setAttribute("aria-label", `Search ${aria}`);
  search.placeholder = aria ? `Search ${aria}…` : "Search…";
  const list = document.createElement("ul");
  list.className = "cselect-list";
  list.setAttribute("role", "listbox");
  if (aria) list.setAttribute("aria-label", aria);
  const hints = document.createElement("div");
  hints.className = "cselect-hints";
  hints.innerHTML = "<kbd>↑</kbd><kbd>↓</kbd> move · <kbd>↵</kbd> select · <kbd>esc</kbd> close";
  pop.append(search, list, hints);
  wrap.append(field, pop);

  let highlight = 0; // position within the currently filtered list
  let filter = "";
  const options = () => Array.from(select.options);
  const filteredOptions = (): { opt: HTMLOptionElement; i: number }[] => {
    const opts = options();
    const labels = opts.map((opt) => ({ label: opt.textContent || "", value: opt.value }));
    return filterOptionIndices(labels, filter).map((i) => ({ opt: opts[i], i }));
  };
  const refresh = () => {
    const sel = select.selectedOptions[0];
    labelEl.textContent = sel ? sel.textContent || sel.value : "";
    labelEl.title = labelEl.textContent || "";
  };
  const rows = () => Array.from(list.querySelectorAll(".cselect-option")) as HTMLElement[];
  const buildList = () => {
    const items = filteredOptions();
    highlight = clampIndex(items.length, highlight);
    list.innerHTML = items.length
      ? items
          .map(
            ({ opt, i }, pos) =>
              `<li class="cselect-option${opt.selected ? " is-selected" : ""}${pos === highlight ? " is-highlight" : ""}" role="option" aria-selected="${opt.selected}" data-i="${i}" title="${escapeHtml(opt.textContent || "")}">${escapeHtml(opt.textContent || opt.value)}</li>`,
          )
          .join("")
      : `<li class="cselect-empty">No matches for “${escapeHtml(filter.trim())}”.</li>`;
  };
  // The popover is position:fixed (so it escapes the pane's overflow:hidden);
  // anchor it under the field using the field's viewport rect.
  const place = () => {
    const r = field.getBoundingClientRect();
    pop.style.left = `${Math.round(r.left)}px`;
    pop.style.top = `${Math.round(r.bottom + 6)}px`;
    pop.style.minWidth = `${Math.round(r.width)}px`;
  };
  const onReflow = () => {
    if (pop.hidden) return;
    place();
  };
  const close = () => {
    if (pop.hidden) return;
    pop.hidden = true;
    field.setAttribute("aria-expanded", "false");
    window.removeEventListener("resize", onReflow);
    window.removeEventListener("scroll", onReflow, true);
  };
  const open = () => {
    filter = "";
    search.value = "";
    // Start on the selected option so ↑/↓ move relative to the current value.
    highlight = Math.max(
      0,
      filteredOptions().findIndex(({ opt }) => opt.selected),
    );
    buildList();
    place();
    pop.hidden = false;
    field.setAttribute("aria-expanded", "true");
    window.addEventListener("resize", onReflow);
    window.addEventListener("scroll", onReflow, true);
    search.focus();
    (list.querySelector(".is-highlight") as HTMLElement | null)?.scrollIntoView({ block: "nearest" });
  };
  const setHighlight = (i: number) => {
    const items = rows();
    if (!items.length) return;
    highlight = clampIndex(items.length, i);
    items.forEach((el, idx) => el.classList.toggle("is-highlight", idx === highlight));
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

  field.addEventListener("click", () => (pop.hidden ? open() : close()));
  field.addEventListener("keydown", (event) => {
    // The field only fields keys while closed; once open, focus is in the
    // search box, which owns navigation.
    if (pop.hidden && (event.key === "ArrowDown" || event.key === "Enter" || event.key === " ")) {
      event.preventDefault();
      open();
    }
  });
  search.addEventListener("input", () => {
    filter = search.value;
    highlight = 0;
    buildList();
  });
  search.addEventListener("keydown", (event) => {
    if (event.key === "ArrowDown") {
      event.preventDefault();
      setHighlight(highlight + 1);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      setHighlight(highlight - 1);
    } else if (event.key === "Enter") {
      event.preventDefault();
      chooseHighlighted();
    } else if (event.key === "Escape") {
      event.preventDefault();
      close();
      field.focus();
    }
  });
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

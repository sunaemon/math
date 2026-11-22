// Split panes scroll independently. A maximized pane uses the document scroller
// so mobile Safari receives a normal page pan and can collapse its browser bars.
let documentPane: HTMLElement | null = null;
let listening = false;

// Safari versions that ignore root overscroll-behavior still need a cancelable
// edge pan. Leave ordinary page/nested scrolling and pinch zoom native so the
// browser bars continue to collapse while reading. Chapter pull handlers still
// receive the event and can navigate without invoking browser refresh.
function canScrollUp(target: EventTarget | null): boolean {
  if (window.scrollY > 0) return true;
  for (let el = target instanceof Element ? target : null; el; el = el.parentElement) {
    if (el.scrollTop > 0 && el.scrollHeight > el.clientHeight && /auto|scroll/.test(getComputedStyle(el).overflowY))
      return true;
  }
  return false;
}

function preventPullToRefresh(): void {
  let touch: { x: number; y: number } | null = null;
  document.addEventListener(
    "touchstart",
    (event) => {
      touch = event.touches.length === 1 ? { x: event.touches[0].clientX, y: event.touches[0].clientY } : null;
    },
    { passive: true, capture: true },
  );
  document.addEventListener(
    "touchmove",
    (event) => {
      if (!touch || event.touches.length !== 1) {
        touch = null;
        return;
      }
      const next = { x: event.touches[0].clientX, y: event.touches[0].clientY };
      const dy = next.y - touch.y;
      const dx = next.x - touch.x;
      touch = next;
      if (event.cancelable && dy > 0 && dy > Math.abs(dx) && !canScrollUp(event.target)) event.preventDefault();
    },
    { passive: false, capture: true },
  );
  const end = () => {
    touch = null;
  };
  document.addEventListener("touchend", end, { passive: true });
  document.addEventListener("touchcancel", end, { passive: true });
}

export function setDocumentPane(pane: HTMLElement | null): void {
  if (!listening) {
    preventPullToRefresh();
    window.addEventListener("scroll", () => documentPane?.dispatchEvent(new Event("scroll")), { passive: true });
    listening = true;
  }
  if (pane === documentPane) return;
  documentPane?.classList.remove("document-scroller");
  documentPane = pane;
  documentPane?.classList.add("document-scroller");
  window.scrollTo({ top: 0, left: 0, behavior: "instant" });
}

function documentTop(pane: HTMLElement): number {
  return pane.getBoundingClientRect().top + window.scrollY;
}

export function paneScrollTop(pane: HTMLElement): number {
  return pane === documentPane ? Math.max(0, window.scrollY - documentTop(pane)) : pane.scrollTop;
}

export function paneViewportTop(pane: HTMLElement): number {
  return pane === documentPane ? Math.max(0, pane.getBoundingClientRect().top) : pane.getBoundingClientRect().top;
}

export function paneViewportHeight(pane: HTMLElement): number {
  return pane === documentPane ? Math.max(0, window.innerHeight - paneViewportTop(pane)) : pane.clientHeight;
}

export function paneScrollHeight(pane: HTMLElement): number {
  return pane === documentPane
    ? Math.max(pane.scrollHeight, document.documentElement.scrollHeight - documentTop(pane))
    : pane.scrollHeight;
}

export function scrollPane(pane: HTMLElement, options: ScrollToOptions): void {
  if (pane === documentPane) {
    window.scrollTo({
      ...options,
      top: options.top === undefined ? window.scrollY : Math.max(0, options.top + documentTop(pane)),
    });
  } else pane.scrollTo(options);
}

import { t } from "./i18n.js";
import { paneScrollTop, paneViewportHeight, paneScrollHeight } from "./pane-scroll.js";
import { WheelChapterPull, CHAPTER_PULL_DISTANCE, type ChapterDirection } from "./chapter-pull-gesture.js";
export type { ChapterDirection } from "./chapter-pull-gesture.js";

interface ChapterPullOptions {
  target: (direction: ChapterDirection) => { label: string } | null;
  navigate: (direction: ChapterDirection) => Promise<void>;
  enabled: () => boolean;
  onError: (error: unknown) => void;
}

export function installChapterPull(viewer: HTMLElement, options: ChapterPullOptions): void {
  const gesture = new WheelChapterPull();
  const cue = document.createElement("div");
  cue.className = "chapter-pull";
  cue.hidden = true;
  cue.setAttribute("role", "status");
  viewer.parentElement!.append(cue);
  let busy = false;
  let hideTimer: ReturnType<typeof setTimeout> | undefined;
  const hide = () => {
    clearTimeout(hideTimer);
    cue.hidden = true;
  };
  const edge = (direction: ChapterDirection): ChapterDirection | null => {
    if (!options.enabled() || busy || !viewer.querySelector(".pdf-page") || !options.target(direction)) return null;
    const atEdge =
      direction < 0
        ? paneScrollTop(viewer) <= 2
        : paneScrollTop(viewer) + paneViewportHeight(viewer) >= paneScrollHeight(viewer) - 2;
    return atEdge ? direction : null;
  };
  const show = (direction: ChapterDirection, progress: number, touch = false) => {
    const target = options.target(direction);
    if (!target || progress <= 0) return hide();
    cue.dataset.direction = direction < 0 ? "previous" : "next";
    cue.style.setProperty("--pull-progress", String(progress));
    const action =
      touch && progress >= 1
        ? direction < 0
          ? t("Release for previous chapter")
          : t("Release for next chapter")
        : direction < 0
          ? t("Pull for previous chapter")
          : t("Pull for next chapter");
    cue.textContent = `${direction < 0 ? "↑" : "↓"} ${action} · ${target.label}`;
    cue.hidden = false;
    clearTimeout(hideTimer);
    hideTimer = setTimeout(hide, 800);
  };
  const turn = async (direction: ChapterDirection) => {
    hide();
    busy = true;
    gesture.block(performance.now());
    try {
      await options.navigate(direction);
    } catch (error) {
      options.onError(error);
    } finally {
      busy = false;
      gesture.block(performance.now());
    }
  };
  viewer.addEventListener(
    "wheel",
    (event) => {
      // Pinch zoom and horizontal gestures retain their native behavior.
      if (event.ctrlKey || event.metaKey || Math.abs(event.deltaX) >= Math.abs(event.deltaY)) {
        gesture.block(performance.now());
        hide();
        return;
      }
      const delta =
        event.deltaY * (event.deltaMode === 1 ? 16 : event.deltaMode === 2 ? paneViewportHeight(viewer) : 1);
      const direction = Math.sign(delta) as ChapterDirection;
      const boundary = edge(direction);
      const result = gesture.push(delta, boundary, performance.now());
      if (boundary) event.preventDefault();
      show(direction, result.progress);
      if (result.turn) void turn(direction);
    },
    { passive: false },
  );

  let touch: {
    x: number;
    y: number;
    top: boolean;
    bottom: boolean;
    direction: ChapterDirection | null;
    distance: number;
  } | null = null;
  viewer.addEventListener(
    "touchstart",
    (event) => {
      hide();
      touch =
        event.touches.length === 1
          ? {
              x: event.touches[0].clientX,
              y: event.touches[0].clientY,
              top: edge(-1) !== null,
              bottom: edge(1) !== null,
              direction: null,
              distance: 0,
            }
          : null;
    },
    { passive: true },
  );
  viewer.addEventListener(
    "touchmove",
    (event) => {
      if (!touch || event.touches.length !== 1) {
        touch = null;
        hide();
        return;
      }
      const delta = touch.y - event.touches[0].clientY;
      const direction = Math.sign(delta) as ChapterDirection;
      if (
        Math.abs(delta) <= Math.abs(touch.x - event.touches[0].clientX) ||
        !(direction < 0 ? touch.top : touch.bottom) ||
        !edge(direction)
      ) {
        touch.direction = null;
        touch.distance = 0;
        hide();
        return;
      }
      event.preventDefault();
      touch.direction = direction;
      touch.distance = Math.abs(delta);
      show(direction, Math.min(1, touch.distance / CHAPTER_PULL_DISTANCE), true);
    },
    { passive: false },
  );
  viewer.addEventListener("touchend", () => {
    const finished = touch;
    touch = null;
    hide();
    if (finished?.direction && finished.distance >= CHAPTER_PULL_DISTANCE && edge(finished.direction))
      void turn(finished.direction);
  });
  viewer.addEventListener("touchcancel", () => {
    touch = null;
    hide();
  });
}

export type ChapterDirection = -1 | 1;
export const CHAPTER_PULL_DISTANCE = 110;
export const WHEEL_GESTURE_GAP = 220;

// A gesture that reaches an edge is still ordinary scrolling. Only a new
// gesture starting there can turn the chapter; its momentum cannot turn twice.
export class WheelChapterPull {
  private lastTime = -Infinity;
  private direction = 0;
  private distance = 0;
  private allowed = false;
  private locked = false;

  block(now: number): void {
    this.lastTime = now;
    this.allowed = false;
    this.locked = true;
  }

  push(delta: number, edge: ChapterDirection | null, now: number): { progress: number; turn: boolean } {
    const direction = Math.sign(delta);
    if (!direction) return { progress: 0, turn: false };
    if (now - this.lastTime > WHEEL_GESTURE_GAP) {
      this.direction = direction;
      this.distance = 0;
      this.allowed = edge === direction;
      this.locked = false;
    }
    this.lastTime = now;
    if (edge !== direction || direction !== this.direction) this.allowed = false;
    if (!this.allowed || this.locked) return { progress: 0, turn: false };
    this.distance += Math.abs(delta);
    const progress = Math.min(1, this.distance / CHAPTER_PULL_DISTANCE);
    if (progress === 1) this.locked = true;
    return { progress, turn: progress === 1 };
  }
}

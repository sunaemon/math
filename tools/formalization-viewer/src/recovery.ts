// A retry stays single-flight across both its timer and the asynchronous attempt.
// Injecting the timer and attempt keeps recovery tests independent of Lean/HTTP.
export class Recovery {
  private pending = false;
  private running = false;
  private attempts = 0;
  private readonly attempt: () => Promise<boolean>;
  private readonly later: (run: () => Promise<void>, ms: number) => void;

  constructor(
    attempt: () => Promise<boolean>,
    later = (run: () => Promise<void>, ms: number): void => {
      setTimeout(() => void run(), ms);
    },
  ) {
    this.attempt = attempt;
    this.later = later;
  }

  reset(): void {
    this.attempts = 0;
  }

  schedule(): void {
    if (this.pending || this.running) return;
    this.pending = true;
    const delay = Math.min(15000, 1000 * ++this.attempts);
    this.later(async () => {
      this.pending = false;
      this.running = true;
      let ok = false;
      try {
        ok = await this.attempt();
      } catch {
        ok = false;
      } finally {
        this.running = false;
        if (ok) this.reset();
        else this.schedule();
      }
    }, delay);
  }
}

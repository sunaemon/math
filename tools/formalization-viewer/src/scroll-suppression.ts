// Programmatic navigation and PDF link jumps share one release window.
export class ScrollSuppression {
  readonly panes = new Set<string>();
  private cancel: (() => void) | null = null;
  private readonly later: (run: () => void, ms: number) => () => void;
  private readonly changed: () => void;

  constructor(later: (run: () => void, ms: number) => () => void, changed: () => void) {
    this.later = later;
    this.changed = changed;
  }

  begin(panes: string[]): void {
    this.cancel?.();
    this.cancel = null;
    this.panes.clear();
    panes.forEach((pane) => this.panes.add(pane));
    this.changed();
  }

  hold(pane: string): void {
    this.panes.add(pane);
    this.changed();
    this.releaseAfter(1200);
  }

  releaseAfter(ms = 300): void {
    this.cancel?.();
    this.cancel = this.later(() => {
      this.cancel = null;
      this.panes.clear();
      this.changed();
    }, ms);
  }
}

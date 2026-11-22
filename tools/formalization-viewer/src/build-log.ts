import { t } from "./i18n.js";
// Subscribe to pushed build output only while the user has the log open.
export function attachBuildLog(button: HTMLElement, logDir: () => string): void {
  button.title = t("Show build log");
  button.setAttribute("aria-haspopup", "dialog");
  button.addEventListener("click", () => {
    const dialog = document.createElement("dialog");
    dialog.className = "build-log-dialog";
    const heading = document.createElement("h2");
    heading.textContent = t("Build log");
    const close = document.createElement("button");
    close.className = "build-log-close";
    close.type = "button";
    close.textContent = "×";
    close.setAttribute("aria-label", t("Close"));
    close.title = t("Close");
    close.addEventListener("click", () => dialog.close());
    const header = document.createElement("div");
    header.className = "build-log-header";
    header.append(heading, close);
    dialog.addEventListener("click", (event) => {
      if (event.target !== dialog) return;
      const bounds = dialog.getBoundingClientRect();
      if (
        event.clientX < bounds.left ||
        event.clientX > bounds.right ||
        event.clientY < bounds.top ||
        event.clientY > bounds.bottom
      ) {
        dialog.close();
      }
    });
    const output = document.createElement("pre");
    output.tabIndex = 0;
    const logText = document.createElement("span");
    logText.className = "build-log-text";
    logText.textContent = t("Loading…");
    const progress = document.createElement("span");
    progress.className = "build-log-progress";
    progress.setAttribute("role", "status");
    progress.setAttribute("aria-live", "polite");
    progress.textContent = t("Building…");
    progress.hidden = true;
    output.append(logText, progress);
    dialog.append(header, output);
    document.body.append(dialog);
    dialog.showModal();
    const followsEnd = () => output.scrollHeight - output.scrollTop - output.clientHeight < 40;
    const updateProgress = () => {
      const follow = followsEnd();
      progress.hidden = button.dataset.state !== "building";
      if (follow) output.scrollTop = output.scrollHeight;
    };
    // Reuse the build state already driving this book's header icon. The cue
    // remains the last child even when output arrives in partial-line chunks.
    const buildState = new MutationObserver(updateProgress);
    buildState.observe(button, { attributes: true, attributeFilter: ["data-state"] });
    updateProgress();
    let timer: ReturnType<typeof setTimeout> | undefined;
    let socket: WebSocket | undefined;
    const connection = document.createElement("span");
    connection.className = "build-log-connection";
    dialog.insertBefore(connection, output);
    dialog.addEventListener("close", () => {
      buildState.disconnect();
      clearTimeout(timer);
      socket?.close();
      dialog.remove();
      button.focus();
    });
    const connect = () => {
      if (!dialog.open) return;
      connection.hidden = false;
      connection.textContent = t("Connecting…");
      const url = new URL("/build/log", location.href);
      url.protocol = location.protocol === "https:" ? "wss:" : "ws:";
      url.searchParams.set("dir", logDir());
      socket = new WebSocket(url);
      socket.onopen = () => {
        connection.hidden = true;
        connection.textContent = "";
      };
      socket.onmessage = (event) => {
        const message = JSON.parse(event.data) as { text: string; reset: boolean };
        const follow = followsEnd();
        if (message.reset) logText.textContent = "";
        logText.textContent = ((logText.textContent ?? "") + message.text).slice(-1024 * 1024);
        if (follow) output.scrollTop = output.scrollHeight;
      };
      socket.onclose = () => {
        if (!dialog.open) return;
        connection.hidden = false;
        connection.textContent = t("Disconnected. Reconnecting…");
        timer = setTimeout(connect, 1500);
      };
    };
    connect();
  });
}

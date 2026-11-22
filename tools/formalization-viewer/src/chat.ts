import { t } from "./i18n.js";
import { setHTML } from "./safe-html.js";
import { BrowserChat } from "./chat-client.js";
import { OPENAI_JWKS } from "./chat-jwks.js";
import { chatCallbackUrl } from "./chat-callback.js";
import { project, state } from "./state.js";
import { repoPath, repoUrl, escapeHtml } from "./util.js";
import {
  sourceExcerpt,
  referencedDefinitions,
  questionWithContext,
  type ChatSelection,
  type ChatAttachment,
} from "./chat-context.js";
import { definitionHtml } from "./definition-render.js";
import { katexRenderMacros } from "./katex-compat.js";
import { dismissTermPopup } from "./term-preview.js";

interface Message {
  role: "user" | "assistant";
  content: string;
}
// Code fences stay literal; prose uses the same escaped Markdown/KaTeX renderer
// as definitions. No response HTML is ever inserted as trusted markup.
function answerHtml(source: string): string {
  return source
    .split(/(```[^]*?```)/g)
    .map((part) => {
      if (part.startsWith("```"))
        return `<pre><code>${escapeHtml(part.replace(/^```[^\n]*\n?/, "").replace(/```$/, ""))}</code></pre>`;
      return part
        .split(/\n{2,}/)
        .map((block) => {
          const heading = /^(#{1,6})\s+([^]*)/.exec(block);
          const body = heading ? heading[2] : block;
          const rendered = state.katex
            ? definitionHtml(body, state.katex, katexRenderMacros(state.katexMacros ?? {}), project.chapterTitles)
            : escapeHtml(body);
          return heading
            ? `<h${Math.min(heading[1].length + 1, 6)}>${rendered}</h${Math.min(heading[1].length + 1, 6)}>`
            : `<div class="chat-paragraph">${rendered}</div>`;
        })
        .join("");
    })
    .join("");
}
function elementOf(node: Node | null): Element | null {
  return node instanceof Element ? node : (node?.parentElement ?? null);
}
function captureSelection(): ChatSelection | null {
  const selection = window.getSelection();
  if (!selection || selection.isCollapsed || !selection.rangeCount) return null;
  const range = selection.getRangeAt(0);
  const first = elementOf(range.startContainer),
    last = elementOf(range.endContainer);
  const pane = first?.closest<HTMLElement>(".pane[data-pane]");
  if (!pane || last?.closest(".pane") !== pane) return null;
  const name = pane.dataset.pane!;
  if (!["md", "lean", "tex", "pdf", "pdf-peer"].includes(name)) return null;
  const text = selection.toString().trim().slice(0, 12000);
  if (!text) return null;
  const entries = new Set<number>();
  if (name.startsWith("pdf")) {
    // Text and marker bands are siblings. Compare actual selection rectangles
    // with bands on the selected page(s), not the last active marker.
    const rectangles = [...range.getClientRects()].filter((rect) => rect.width > 0 && rect.height > 0);
    for (const band of pane.querySelectorAll<HTMLElement>(".pdf-mark[data-entry]")) {
      const box = band.getBoundingClientRect();
      if (
        rectangles.some(
          (rect) => rect.left < box.right && rect.right > box.left && rect.top < box.bottom && rect.bottom > box.top,
        )
      )
        entries.add(Number(band.dataset.entry));
    }
  } else {
    for (const mark of pane.querySelectorAll<HTMLElement>(".mark[data-entry]")) {
      if (range.intersectsNode(mark)) entries.add(Number(mark.dataset.entry));
    }
  }
  return {
    text,
    pane: name,
    entries: [...entries].filter(Number.isInteger).slice(0, 4),
    file: state.selectedSources[name as "md" | "lean" | "tex"] ?? undefined,
    startLine: Number(first?.closest<HTMLElement>(".line")?.dataset.line) || undefined,
    endLine: Number(last?.closest<HTMLElement>(".line")?.dataset.line) || undefined,
  };
}
async function attachmentsFor(selection: ChatSelection): Promise<ChatAttachment[]> {
  const attachments: ChatAttachment[] = [];
  const used = new Set<string>();
  const addSource = async (
    file: string | undefined,
    start: number | undefined,
    end: number | undefined,
    padding = 3,
  ) => {
    if (!file || !start || used.has(`${file}:${start}`)) return;
    used.add(`${file}:${start}`);
    const relative = repoPath(file);
    try {
      let text = state.sourceCache.get(relative);
      if (text === undefined) {
        const response = await fetch(repoUrl(file));
        if (!response.ok) throw new Error(`HTTP ${response.status}`);
        text = await response.text();
      }
      attachments.push({ label: `${relative}:${start}`, text: sourceExcerpt(text, start, end ?? start, padding) });
    } catch {
      attachments.push({ label: relative, text: "Source could not be loaded." });
    }
  };
  if (selection.file && selection.startLine) await addSource(selection.file, selection.startLine, selection.endLine);
  for (const index of selection.entries) {
    const entry = state.entries[index];
    if (!entry) continue;
    const match = entry.match;
    if (match?.status === "matched") await addSource(match.source, match.startLine, match.endLine);
    else if (entry.booklink?.excerpt)
      attachments.push({ label: "Booklink excerpt", text: String(entry.booklink.excerpt).slice(0, 5000) });
    const lean = entry.lean;
    if (lean)
      await addSource(lean.source, lean.declLine, Math.max(lean.declEndLine ?? 0, (lean.declLine ?? 0) + 35), 1);
  }
  attachments.push(
    ...referencedDefinitions(
      attachments.map((item) => item.text).join("\n") + "\n" + selection.text,
      project.definitionRegistry,
    ),
  );
  // Include only macros used in the attached context, including dependencies.
  const macros = project.katexMacros ?? state.katexMacros ?? {};
  let source = attachments.map((item) => item.text).join("\n") + selection.text;
  const needed = new Map<string, string>();
  for (let pass = 0; pass < 4; pass++)
    for (const match of source.matchAll(/\\[A-Za-z]+/g)) {
      const name = match[0];
      if (typeof macros[name] === "string" && !needed.has(name)) {
        needed.set(name, macros[name]);
        source += "\n" + macros[name];
      }
    }
  if (needed.size)
    attachments.push({
      label: "Mathematical notation macros",
      text: [...needed]
        .map(([name, body]) => `${name} := ${body}`)
        .join("\n")
        .slice(0, 6000),
    });
  let budget = 28000;
  return attachments.flatMap((item) => {
    const text = item.text.slice(0, Math.max(0, budget));
    budget -= text.length;
    return text ? [{ ...item, text }] : [];
  });
}

export function initChat(): void {
  const client = new BrowserChat(OPENAI_JWKS);
  const toggle = document.createElement("button");
  toggle.id = "chat-toggle";
  toggle.type = "button";
  toggle.setAttribute("aria-label", t("チャットを開く"));
  toggle.title = t("チャットを開く");
  setHTML(
    toggle,
    '<svg width="26" height="26" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M21 11.5a8.4 8.4 0 0 1-.9 3.8 8.5 8.5 0 0 1-7.6 4.7 8.4 8.4 0 0 1-3.8-.9L3 21l1.9-5.7a8.4 8.4 0 0 1-.9-3.8 8.5 8.5 0 0 1 4.7-7.6 8.4 8.4 0 0 1 3.8-.9h.5a8.5 8.5 0 0 1 8 8v.5Z"/><path d="M8 11h8M8 15h5"/></svg>',
  );
  toggle.setAttribute("aria-controls", "viewer-chat");
  toggle.setAttribute("aria-expanded", "false");
  document.body.append(toggle);
  const ask = document.createElement("button");
  ask.id = "selection-ask";
  ask.type = "button";
  ask.textContent = t("これを説明");
  ask.hidden = true;
  document.body.append(ask);
  const panel = document.createElement("aside");
  panel.id = "viewer-chat";
  panel.hidden = true;
  panel.setAttribute("aria-label", t("選択箇所について質問"));
  setHTML(
    panel,
    `<header class="chat-header"><strong>${t("選択箇所について質問")}</strong><button type="button" id="chat-new">${t("新しい会話")}</button><button type="button" id="chat-close" aria-label="${t("質問パネルを閉じる")}">×</button></header>
    <details class="chat-connection"><summary id="chat-account">${t("ChatGPT に接続")}</summary><div class="chat-connect-body"><button type="button" id="chat-login">${t("Continue with ChatGPT")}</button><button type="button" id="chat-disconnect" hidden>${t("接続解除")}</button><a href="https://chatgpt.com/" target="_blank" rel="noreferrer">${t("ChatGPT で利用状況を管理")}</a>
    <div id="chat-login-pending" hidden><p>${t("ログイン用タブで許可した後、この画面へ戻ってください。127.0.0.1 のページは開けないため、そのタブのアドレス欄を長押しして URL 全体をコピーし、下に貼り付けてください。")}</p><input id="chat-callback" type="text" inputmode="url" aria-label="${t("ログイン後の戻り先 URL")}" aria-describedby="chat-login-error" placeholder="${t("開けなかったタブからコピーした URL 全体")}" autocomplete="off" autocapitalize="off" spellcheck="false"><button type="button" id="chat-complete" disabled>${t("ログインを完了")}</button><p id="chat-login-error" role="alert"></p></div>
    <details><summary>${t("API キーで接続")}</summary><p>${t("キーはこのタブ内だけで保持し、再読み込みすると消去します。サイトのサーバーには送信しません。")}</p><input id="chat-key" type="password" aria-label="${t("OpenAI API キー")}" autocomplete="off" placeholder="${t("OpenAI API key")}"><button type="button" id="chat-key-save">${t("接続")}</button></details>
    <label>${t("モデル")} <select id="chat-model" aria-label="${t("質問に使用するモデル")}"></select></label></div></details>
    <details id="chat-context"><summary>${t("送信する引用・文脈")} <span id="chat-context-count"></span></summary><div id="chat-context-body">${t("本文や PDF を選択して「これを説明」を押してください。")}</div></details>
    <div id="chat-messages" role="log" aria-label="${t("会話")}"></div><p id="chat-status" role="status" aria-live="polite"></p>
    <form id="chat-form"><textarea id="chat-question" rows="3" maxlength="6000" aria-label="${t("質問")}" placeholder="${t("これはどういうこと？")}"></textarea><div class="chat-actions"><span>${t("引用・文脈と質問を OpenAI に送信します")}</span><button type="button" id="chat-stop" hidden>${t("停止")}</button><button type="submit" id="chat-send" disabled>${t("送信")}</button></div></form>`,
  );
  document.body.append(panel);
  const get = <T extends HTMLElement = HTMLElement>(id: string) => panel.querySelector<T>(`#${id}`)!;
  const question = get<HTMLTextAreaElement>("chat-question"),
    model = get<HTMLSelectElement>("chat-model"),
    send = get<HTMLButtonElement>("chat-send"),
    status = get("chat-status"),
    log = get("chat-messages");
  let selected: ChatSelection | null = null,
    attachments: ChatAttachment[] = [],
    history: Message[] = [],
    connection: string | null = null,
    loadingContext = false,
    busy: AbortController | null = null,
    contextToken = 0;
  const update = () => {
    send.disabled = !connection || !selected || loadingContext || !!busy || !model.value || !question.value.trim();
  };
  const show = (open: boolean) => {
    panel.hidden = !open;
    toggle.hidden = open;
    document.body.classList.toggle("chat-open", open);
    toggle.setAttribute("aria-expanded", String(open));
    ask.hidden = true;
    if (open) question.focus({ preventScroll: true });
  };
  const fail = (error: unknown) => {
    status.textContent = t((error as Error).message);
  };
  const account = async () => {
    const value = client.status();
    connection = value.provider;
    if (!connection) panel.querySelector<HTMLDetailsElement>(".chat-connection")!.open = true;
    get("chat-account").textContent = connection
      ? `${connection === "chatgpt" ? "ChatGPT" : t("API キー")}${value.email ? ` · ${value.email}` : ""}`
      : t("ChatGPT に接続");
    get("chat-disconnect").hidden = !connection;
    get("chat-login-pending").hidden = !value.pending;
    update();
    return value;
  };
  const models = async () => {
    setHTML(model, "");
    update();
    if (!connection) return;
    const value = { models: await client.models() };
    for (const item of value.models) model.add(new Option(item.name, item.id));
    let saved: string | null = null;
    try {
      saved = sessionStorage.getItem("viewer-chat-model");
    } catch {
      /* Storage can be disabled by browser privacy settings. */
    }
    if ([...model.options].some((option) => option.value === saved)) model.value = saved!;
    else if ([...model.options].some((option) => option.value === "gpt-6.1-sol")) model.value = "gpt-6.1-sol";
    if (!model.options.length)
      status.textContent = t("利用できるモデルがありません。プランの利用許可を確認してください。");
    update();
  };
  toggle.onclick = () => {
    show(!!panel.hidden);
    if (!panel.hidden) void account().then(models).catch(fail);
  };
  get("chat-close").onclick = () => {
    show(false);
    toggle.focus({ preventScroll: true });
  };
  const reset = () => {
    contextToken++;
    busy?.abort();
    busy = null;
    history = [];
    loadingContext = false;
    log.replaceChildren();
    status.textContent = "";
    get("chat-stop").hidden = true;
    update();
  };
  get("chat-new").onclick = () => {
    reset();
    question.focus();
  };
  model.onchange = () => {
    try {
      sessionStorage.setItem("viewer-chat-model", model.value);
    } catch {
      /* Selection remains valid without persistence. */
    }
  };
  question.oninput = update;
  get("chat-disconnect").onclick = () => {
    reset();
    client.disconnect();
    void account().then(models).catch(fail);
  };
  get("chat-key-save").onclick = async () => {
    const field = get<HTMLInputElement>("chat-key");
    const key = field.value;
    field.value = "";
    try {
      client.setApiKey(key);
      await account();
      await models();
      status.textContent = t("API キーで接続しました。");
    } catch (error) {
      fail(error);
    }
  };
  get("chat-login").onclick = async () => {
    // Open synchronously within the gesture so popup blockers do not discard it.
    callbackField.value = "";
    loginError.textContent = "";
    callbackField.removeAttribute("aria-invalid");
    updateCallback();
    const tab = window.open("about:blank", "_blank");
    if (tab) tab.opener = null;
    try {
      const value = await client.begin();
      if (tab) tab.location.href = value.url;
      else {
        status.textContent = t("ポップアップを許可して、もう一度接続してください。");
      }
      await account();
    } catch (error) {
      tab?.close();
      fail(error);
    }
  };
  const callbackField = get<HTMLInputElement>("chat-callback");
  const completeButton = get<HTMLButtonElement>("chat-complete");
  const loginError = get("chat-login-error");
  let completingLogin = false;
  const updateCallback = () => {
    completeButton.disabled = completingLogin || !callbackField.value.trim();
  };
  callbackField.oninput = () => {
    callbackField.removeAttribute("aria-invalid");
    loginError.textContent = "";
    updateCallback();
  };
  completeButton.onclick = async () => {
    if (completingLogin) return;
    loginError.textContent = "";
    callbackField.removeAttribute("aria-invalid");
    const original = callbackField.value;
    let connected = false;
    try {
      const url = chatCallbackUrl(original);
      completingLogin = true;
      updateCallback();
      completeButton.textContent = t("接続を確認中…");
      status.textContent = t("ChatGPT への接続を確認しています…");
      await client.complete(url);
      connected = true;
      // Keep the input on failure, including malformed/expired callbacks. Clear
      // the short-lived code only once the server has accepted the connection.
      if (callbackField.value === original) callbackField.value = "";
      await account();
      await models();
      status.textContent = t("ChatGPT に接続しました。");
    } catch (error) {
      const message = t((error as Error).message);
      status.textContent = connected
        ? t("Login succeeded, but connection information could not be retrieved. {0}", t(message))
        : message;
      if (!connected) {
        loginError.textContent = message;
        callbackField.setAttribute("aria-invalid", "true");
        callbackField.focus({ preventScroll: true });
      }
    } finally {
      completingLogin = false;
      completeButton.textContent = t("ログインを完了");
      updateCallback();
    }
  };
  const prepare = async (selection: ChatSelection) => {
    reset();
    selected = selection;
    attachments = [];
    const token = ++contextToken;
    loadingContext = true;
    dismissTermPopup();
    show(true);
    if (!question.value.trim()) question.value = t("これはどういうこと？");
    status.textContent = t("関連する文章と定義を準備しています…");
    const body = get("chat-context-body");
    body.textContent = t("読み込み中…");
    get("chat-context").setAttribute("open", "");
    update();
    try {
      const items = await attachmentsFor(selection);
      if (token !== contextToken) return;
      attachments = items;
      setHTML(
        body,
        `<h4>${escapeHtml(t("Selected passage · {0}", selection.pane))}</h4><pre>${escapeHtml(selection.text)}</pre>${items.map((item) => `<h4>${escapeHtml(item.label)}</h4><pre>${escapeHtml(item.text)}</pre>`).join("")}`,
      );
      get("chat-context-count").textContent = `(${items.length + 1})`;
      status.textContent = selection.entries.length
        ? t("内容を確認して送信してください。")
        : t("対応するマーカーがないため、選択した文章と取得できた文脈を送ります。");
      await account();
      if (!model.options.length) await models();
    } catch (error) {
      fail(error);
    } finally {
      if (token === contextToken) {
        loadingContext = false;
        update();
      }
    }
  };
  let pendingSelection: ChatSelection | null = null;
  const selectionChanged = () => {
    const selection = captureSelection();
    pendingSelection = selection;
    ask.hidden = !selection;
    if (!selection) return;
    const range = window.getSelection()!.getRangeAt(0),
      box = range.getBoundingClientRect();
    ask.style.left = `${Math.max(8, Math.min(window.innerWidth - 130, box.right))}px`;
    ask.style.top = `${Math.min(window.innerHeight - 45, Math.max(8, box.bottom + 5))}px`;
  };
  document.addEventListener("pointerup", (event) => {
    if (!panel.contains(event.target as Node) && event.target !== ask) selectionChanged();
  });
  document.addEventListener("keyup", (event) => {
    if (event.key === "Shift" || event.key.startsWith("Arrow")) selectionChanged();
  });
  document.addEventListener("selectionchange", () => {
    if (window.getSelection()?.isCollapsed) ask.hidden = true;
  });
  document.addEventListener(
    "scroll",
    () => {
      ask.hidden = true;
    },
    true,
  );
  ask.onpointerdown = (event) => event.preventDefault();
  ask.onclick = () => {
    if (pendingSelection) void prepare(pendingSelection);
  };
  get("chat-stop").onclick = () => busy?.abort();
  get<HTMLFormElement>("chat-form").onsubmit = async (event) => {
    event.preventDefault();
    if (send.disabled || !selected) return;
    const asked = question.value.trim();
    const turnToken = contextToken;
    const content = history.length
      ? asked
      : questionWithContext(asked, selected, attachments, String(project.name ?? project.dir ?? ""));
    const messages: Message[] = [...history, { role: "user", content }];
    const user = document.createElement("div");
    user.className = "chat-message chat-user";
    user.textContent = asked;
    log.append(user);
    const answer = document.createElement("div");
    answer.className = "chat-message chat-assistant";
    log.append(answer);
    const controller = new AbortController();
    busy = controller;
    update();
    question.value = "";
    status.textContent = t("回答中…");
    get("chat-stop").hidden = false;
    let text = "",
      lastRender = 0;
    const render = () => {
      const bottom = log.scrollHeight - log.scrollTop - log.clientHeight < 90;
      setHTML(answer, answerHtml(text));
      if (bottom) log.scrollTop = log.scrollHeight;
      lastRender = performance.now();
    };
    try {
      state.katex ??= (await import(new URL("../vendor/katex/katex.mjs", import.meta.url).href)).default;
      for await (const delta of client.respond(model.value, messages, controller.signal)) {
        text += delta;
        if (text.length > 150000) throw new Error(t("回答が長すぎます。"));
        if (performance.now() - lastRender > 120) render();
      }
      if (busy === controller && turnToken === contextToken) {
        history = [...messages, { role: "assistant", content: text }];
        status.textContent = "";
      }
    } catch (error) {
      if (busy === controller && turnToken === contextToken) {
        status.textContent = controller.signal.aborted ? t("回答を停止しました。") : t((error as Error).message);
        question.value = asked;
      }
      // A partial answer is visible but never added as completed conversation.
      answer.dataset.incomplete = "true";
    } finally {
      render();
      if (busy === controller) {
        busy = null;
        get("chat-stop").hidden = true;
        update();
      }
    }
  };
  question.onkeydown = (event) => {
    if (event.key === "Enter" && (event.metaKey || event.ctrlKey)) {
      event.preventDefault();
      get<HTMLFormElement>("chat-form").requestSubmit();
    }
  };
  panel.addEventListener("keydown", (event) => {
    if (event.key === "Escape") {
      show(false);
      toggle.focus();
    }
  });
  const toolbar = document.querySelector(".toolbar")!;
  const resize = new ResizeObserver(() => {
    panel.style.top = `${toolbar.getBoundingClientRect().bottom}px`;
  });
  resize.observe(toolbar);
}

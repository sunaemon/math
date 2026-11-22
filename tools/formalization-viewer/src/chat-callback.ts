// Shared browser/server validation for manually relaying the OAuth callback.
// Never include its code/state in errors or logs.
export function chatCallbackUrl(value: unknown): string {
  if (typeof value !== "string" || !value.trim()) throw new Error("ログイン後の戻り先 URL を貼り付けてください。");
  let text = value.trim();
  if (text.length > 16000) throw new Error("戻り先 URL が長すぎます。アドレス欄からコピーし直してください。");
  // Safari may display/copy an address without its HTTP scheme.
  if (/^127\.0\.0\.1:\d+\//.test(text)) text = `http://${text}`;
  let url: URL;
  try {
    url = new URL(text);
  } catch {
    throw new Error(
      "URL を読み取れません。ログイン後に開けなかったタブのアドレス欄から、URL 全体をコピーしてください。",
    );
  }
  if (
    url.protocol !== "http:" ||
    url.hostname !== "127.0.0.1" ||
    !url.port ||
    url.pathname !== "/auth/callback" ||
    url.username ||
    url.password ||
    url.hash
  )
    throw new Error(
      "ログイン後の戻り先 URL が必要です。127.0.0.1 で開けなかったタブのアドレス欄からコピーしてください。",
    );
  if (
    text.includes("…") ||
    text.includes("...") ||
    !url.searchParams.get("state") ||
    (!url.searchParams.get("code") && !url.searchParams.get("error"))
  )
    throw new Error(
      "URL の認証情報が不足しています。省略表示ではなく、code や state を含む URL 全体をコピーしてください。",
    );
  return url.href;
}

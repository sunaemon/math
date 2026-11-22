// Incremental LSP framing shared by the live bridge and static-cache client.
// Lengths count UTF-8 bytes; malformed headers must never move the cursor back.
export class LspFrames {
  private buffer = Buffer.alloc(0);

  push(chunk: Buffer): string[] {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    const messages: string[] = [];
    for (;;) {
      const end = this.buffer.indexOf("\r\n\r\n");
      if (end < 0) return messages;
      let length: number | undefined;
      for (const line of this.buffer.subarray(0, end).toString("latin1").split("\r\n")) {
        const separator = line.indexOf(":");
        if (line.slice(0, separator).toLowerCase() !== "content-length") continue;
        const value = line.slice(separator + 1).trim();
        if (length !== undefined || !/^\d+$/.test(value) || !Number.isSafeInteger(Number(value))) {
          throw new Error("Malformed LSP Content-Length");
        }
        length = Number(value);
      }
      if (length === undefined) throw new Error("Missing LSP Content-Length");
      const start = end + 4;
      if (this.buffer.length - start < length) return messages;
      messages.push(this.buffer.subarray(start, start + length).toString("utf-8"));
      this.buffer = this.buffer.subarray(start + length);
    }
  }
}

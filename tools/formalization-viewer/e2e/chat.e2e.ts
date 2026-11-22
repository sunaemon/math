import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";
import path from "node:path";

test(
  "selected source opens a reviewable chat context and streams math with follow-up history",
  { timeout: 45000 },
  async (t) => {
    const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
    t.after(() => server.stop());
    const build = spawnSync(
      "esbuild",
      [
        "--bundle",
        "--format=iife",
        "--platform=browser",
        "--log-level=error",
        `--define:import.meta.url=${JSON.stringify(server.baseUrl + "/polish-space/build/chat.js")}`,
      ],
      {
        cwd: new URL("../../..", import.meta.url),
        encoding: "utf8",
        maxBuffer: 4 * 1024 * 1024,
        input: `import {initChat} from './tools/formalization-viewer/src/chat.ts';import {state,setProject} from './tools/formalization-viewer/src/state.ts';window.chatTest={initChat,state,setProject};`,
      },
    );
    assert.equal(build.status, 0, build.stderr);
    const browser = await CdpBrowser.launch();
    t.after(() => browser.close());
    const tab = await browser.newPage();
    await tab.onNewDocument("Object.defineProperty(navigator,'languages',{get:()=>['ja-JP','en-US']})");
    await tab.setViewport(1200, 900);
    await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
    await tab.evaluate(build.stdout);
    const styles = readFileSync(new URL("../styles.css", import.meta.url), "utf8");
    await tab.evaluate(
      `{ const style=document.createElement("style");style.textContent=${JSON.stringify(styles)};document.head.append(style); }`,
    );
    await tab.evaluate(`(async()=>{
    document.body.innerHTML='<header class="toolbar"><div class="settings"></div></header><main class="workspace"><section class="pane" data-pane="md"><pre id="md-source"><div class="line" data-line="2">A <span class="mark" data-entry="0">Polish space has a complete compatible metric.</span></div></pre></section></main>';
    const {setProject,state}=window.chatTest;
    setProject({name:'Test book',dir:'polish-space',mount:'/polish-space',static:true});
    state.selectedSources.md='src/test.md';state.sourceCache.set('src/test.md','Before\\nA Polish space has a complete compatible metric.\\nAfter');
    state.entries=[{match:{status:'matched',source:'src/test.md',startLine:2,endLine:2},lean:{source:'lean/test.lean',declLine:1,declEndLine:2}}];
    state.sourceCache.set('lean/test.lean','theorem example : True := by\\n  trivial');
    window.sentChats=[];window.chatNetwork=[];
    window.fetch=async(url,options)=>{
      window.chatNetwork.push(String(url));
      if(url==='https://api.openai.com/v1/models')return Response.json({data:[{id:'gpt-example'}]});
      if(url==='https://api.openai.com/v1/responses'){
        window.sentChats.push(JSON.parse(options.body));
        if(window.replyMode==='wait')return new Response(new ReadableStream({start(controller){options.signal.addEventListener('abort',()=>controller.error(new DOMException('Aborted','AbortError')));}}));
        return new Response('data: '+JSON.stringify({type:'response.output_text.delta',delta:'Because **complete** means $x=1$. <img src=x onerror=alert(1)>'})+'\\n\\n'+'data: '+JSON.stringify({type:'response.completed'})+'\\n\\n');
      }
      throw new Error("Unexpected network request: "+url);
    };
    window.chatTest.initChat();
  })()`);
    assert.equal(await tab.evaluate("document.querySelector('#viewer-chat').hidden"), true);
    await tab.setViewport(390, 800);
    const launcher = await tab.evaluate<{
      width: number;
      height: number;
      right: number;
      bottom: number;
      radius: string;
    }>(
      `(()=>{const button=document.querySelector('#chat-toggle');const r=button.getBoundingClientRect();return {width:r.width,height:r.height,right:innerWidth-r.right,bottom:innerHeight-r.bottom,radius:getComputedStyle(button).borderRadius};})()`,
    );
    assert.equal(launcher.width, 56);
    assert.equal(launcher.height, 56);
    assert.equal(launcher.radius, "50%");
    assert.equal(launcher.right, 20);
    assert.equal(launcher.bottom, 20);
    assert.equal(await tab.evaluate("document.querySelector('.toolbar #chat-toggle')"), null);
    await tab.evaluate("document.querySelector('#chat-toggle').click()");
    await tab.waitFor("document.querySelector('#viewer-chat').hidden===false");
    await tab.evaluate(
      "document.querySelector('#chat-key').value='test-api-key-12345';document.querySelector('#chat-key-save').click()",
    );
    await tab.waitFor("document.querySelector('#chat-model').options.length===1");
    assert.equal(await tab.evaluate("document.querySelector('#chat-toggle').hidden"), true);
    await tab.evaluate("document.querySelector('#chat-close').click()");
    assert.equal(await tab.evaluate("document.querySelector('#viewer-chat').hidden"), true);
    assert.equal(await tab.evaluate("document.activeElement.id"), "chat-toggle");
    await tab.setViewport(1200, 900);
    await tab.evaluate(`(()=>{
    const range=document.createRange();range.selectNodeContents(document.querySelector('.mark'));const selection=window.getSelection();selection.removeAllRanges();selection.addRange(range);
    document.querySelector('.mark').dispatchEvent(new PointerEvent('pointerup',{bubbles:true}));
    document.querySelector('#selection-ask').click();
  })()`);
    await tab.waitFor("document.querySelector('#chat-send')?.disabled===false");
    assert.equal(await tab.evaluate("window.sentChats.length"), 0);
    assert.equal(await tab.evaluate("document.body.classList.contains('chat-open')"), true);
    await tab.setViewport(390, 800);
    const right = await tab.evaluate<number>("document.querySelector('#viewer-chat').getBoundingClientRect().right");
    assert.ok(right <= 390);
    await tab.setViewport(1200, 900);
    const context = await tab.evaluate<string>("document.querySelector('#chat-context-body').textContent");
    assert.match(context, /complete compatible metric/);
    assert.match(context, /theorem example/);
    assert.match(context, /src\/test.md:2/);
    await tab.evaluate(`(()=>{
      const question=document.querySelector('#chat-question');
      question.value='My unfinished question';question.dispatchEvent(new Event('input'));
      const range=document.createRange();range.selectNodeContents(document.querySelector('.mark'));
      const selection=window.getSelection();selection.removeAllRanges();selection.addRange(range);
      document.querySelector('.mark').dispatchEvent(new PointerEvent('pointerup',{bubbles:true}));
      document.querySelector('#selection-ask').click();
    })()`);
    await tab.waitFor("document.querySelector('#chat-send')?.disabled===false");
    assert.equal(await tab.evaluate("document.querySelector('#chat-question').value"), "My unfinished question");
    await tab.evaluate("document.querySelector('#chat-form').requestSubmit()");
    await tab.waitFor(
      "document.querySelector('.chat-assistant .katex') && document.querySelector('#chat-status').textContent===''",
    );
    assert.equal(await tab.evaluate("document.querySelectorAll('.chat-assistant img').length"), 0);
    assert.equal(await tab.evaluate("document.querySelector('.chat-assistant strong').textContent"), "complete");
    await tab.evaluate(
      "document.querySelector('#chat-question').value='Why complete?';document.querySelector('#chat-question').dispatchEvent(new Event('input'));document.querySelector('#chat-form').requestSubmit()",
    );
    await tab.waitFor("window.sentChats.length===2 && document.querySelector('#chat-status').textContent===''");
    const messages = await tab.evaluate<Array<{ role: string; content: string }>>("window.sentChats[1].input");
    assert.deepEqual(
      messages.map((item) => item.role),
      ["user", "assistant", "user"],
    );
    assert.match(messages[0].content, /theorem example/);
    assert.equal(
      await tab.evaluate("window.chatNetwork.every(url=>url.startsWith('https://api.openai.com/v1/'))"),
      true,
    );
    assert.equal(messages[2].content, "Why complete?");
    await tab.evaluate("document.querySelector('#chat-new').click()");
    assert.equal(await tab.evaluate("document.querySelector('#chat-messages').textContent"), "");
    await tab.evaluate(
      "window.replyMode='wait';document.querySelector('#chat-question').value='Wait';document.querySelector('#chat-question').dispatchEvent(new Event('input'));document.querySelector('#chat-form').requestSubmit()",
    );
    await tab.waitFor("document.querySelector('#chat-stop').hidden===false");
    await tab.evaluate("document.querySelector('#chat-stop').click()");
    await tab.waitFor("document.querySelector('#chat-status').textContent==='回答を停止しました。'");
    assert.equal(await tab.evaluate("document.querySelector('#chat-question').value"), "Wait");
    // A bad callback stays available to correct without any server request.
    assert.equal(await tab.evaluate("document.querySelector('#chat-complete').disabled"), true);
    await tab.evaluate(
      `{document.querySelector('#chat-login-pending').hidden=false;const field=document.querySelector('#chat-callback');field.value='not a URL';field.dispatchEvent(new Event('input'));document.querySelector('#chat-complete').click();}`,
    );
    assert.equal(await tab.evaluate("document.querySelector('#chat-callback').value"), "not a URL");
    assert.match(await tab.evaluate<string>("document.querySelector('#chat-login-error').textContent"), /URL 全体/);
  },
);

import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("AI Catalog discovery and WebMCP callbacks expose real book-to-Lean locations", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.onNewDocument(
    `window.viewerTools=new Map();Object.defineProperty(document,'modelContext',{value:{registerTool:async(tool,options)=>{window.viewerTools.set(tool.name,tool);options.signal.addEventListener('abort',()=>window.viewerTools.delete(tool.name));}}});`,
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  assert.equal(await tab.evaluate("window.viewerTools.size"), 7);
  const discovered = await tab.evaluate<any>(
    `(async()=>{const link=document.querySelector('link[rel=ai-catalog]'), response=await fetch(link.href);return {type:response.headers.get('content-type'),catalog:await response.json()};})()`,
  );
  assert.equal(discovered.type, "application/ai-catalog+json");
  assert.equal(discovered.catalog.specVersion, "1.0");
  const root = await fetch(`${server.baseUrl}/.well-known/ai-catalog.json`);
  assert.equal(root.status, 200);
  assert.deepEqual(await root.json(), discovered.catalog);
  const result = await tab.evaluate<any>(`(async()=>{
   const call=(name,args)=>window.viewerTools.get(name).execute(args,{});
   const {markers}=await call('list_markers',{query:'preface_rational_complexity'});
   const marker=await call('get_marker',{marker:markers[0].marker});
   const reverse=await call('find_markers_for_location',{source:marker.lean.source,line:marker.lean.declarationStartLine});
   const source=await call('read_source',{source:marker.lean.source,startLine:marker.lean.declarationStartLine,endLine:marker.lean.declarationEndLine});
   const target=(await call('list_markers',{query:'closed_subspace_polish'})).markers[0];
   await call('navigate_marker',{marker:target.marker});
   const state=await call('get_viewer_state',{});
   const search=await call('search_book',{query:'Polish',limit:2});
   return {marker,reverse,source,state,target,search};
 })()`);
  assert.equal(result.marker.lean.declaration, "preface_rational_complexity");
  assert.ok(result.reverse.markers.some((item: any) => item.marker === result.marker.marker));
  assert.ok(result.source.lines.some((line: any) => line.text.includes("preface_rational_complexity")));
  assert.equal(result.state.location.marker, result.target.marker);
  assert.ok(result.search.total > 0);
  assert.ok(result.search.hits.length <= 2);
  assert.equal(JSON.stringify(result).includes("/Users/"), false);
});

test("native WebMCP registers tools when the browser provides the current API", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch([
    "--enable-features=WebMCP",
    "--enable-blink-features=WebMCP",
    "--enable-experimental-web-platform-features",
  ]);
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  if (!(await tab.evaluate("typeof document.modelContext?.getTools==='function'"))) {
    t.skip("Installed Chrome does not expose the current document.modelContext testing API");
    return;
  }
  const result = await tab.evaluate<any>(
    `(async()=>{const api=document.modelContext, tools=await api.getTools();const tool=tools.find(tool=>tool.name==='get_viewer_state');if(!tool)throw new Error('Viewer tools not registered');const output=await api.executeTool(tool,{});return typeof output==='string'?JSON.parse(output):output;})()`,
  );
  assert.equal(result.book.name, "polish-space");
});

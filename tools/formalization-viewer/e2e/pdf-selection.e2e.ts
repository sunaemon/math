import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test(
  "cropped PDF pages expose selectable text above marker bands and retain alignment on resize",
  { timeout: 30000 },
  async (t) => {
    const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
    t.after(() => server.stop());
    const browser = await CdpBrowser.launch();
    t.after(() => browser.close());
    const tab = await browser.newPage();
    await tab.setViewport(1200, 1200);
    await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
    await tab.evaluate(`(async()=>{
    const link=document.createElement('link');link.rel='stylesheet';link.href='./styles.css';
    const ready=new Promise((resolve,reject)=>{link.onload=resolve;link.onerror=reject;});document.head.append(link);await ready;
    document.body.innerHTML='<div class="pdf-page" style="width:700px;margin:30px"><canvas></canvas></div>';
    const pdfjs=await import('./vendor/pdfjs/pdf.mjs');pdfjs.GlobalWorkerOptions.workerSrc='./vendor/pdfjs/pdf.worker.mjs';
    const doc=await pdfjs.getDocument({url:'./build/polish-space-book-preview-preface.pdf'}).promise;
    let page;
    for(let i=1;i<=doc.numPages;i++){page=await doc.getPage(i);if((await page.getTextContent()).items.some(item=>item.str?.length>20)) break;}
    window.selectionPage=page;
    const vp=page.getViewport({scale:1});window.selectionCrop={x0:20,x1:vp.width-20};
    const {paintPdfPage}=await import('./build/pdf-document.js');window.paintSelection=paintPdfPage;
    const canvas=document.querySelector('canvas');await paintPdfPage(page,canvas,window.selectionCrop,700);
    const band=document.createElement('div');band.className='pdf-mark';band.dataset.entry='0';band.style.inset='0';document.querySelector('.pdf-page').append(band);
    await document.fonts.ready;
  })()`);
    const boxes = await tab.evaluate<Array<{ x: number; y: number; width: number }>>(`(()=>{
    return [...document.querySelectorAll('.pdf-text-layer span')].filter(span=>span.textContent.trim().length>20).slice(0,2).map(span=>{const r=span.getBoundingClientRect();return {x:r.left,y:r.top+r.height/2,width:r.width};});
  })()`);
    assert.equal(boxes.length, 2);
    await tab.drag({ x: boxes[0].x + 2, y: boxes[0].y }, { x: boxes[1].x + boxes[1].width - 2, y: boxes[1].y });
    const selected = await tab.evaluate<string>("window.getSelection().toString()");
    assert.ok(selected.trim().length > 20, JSON.stringify(selected));
    assert.equal(
      await tab.evaluate("getComputedStyle(document.querySelector('.pdf-text-layer span')).color"),
      "rgba(0, 0, 0, 0)",
    );
    await tab.setViewport(1200, 1200, 2);
    await tab.evaluate(
      `(async()=>{document.querySelector('.pdf-page').style.width='500px';await window.paintSelection(window.selectionPage,document.querySelector('canvas'),window.selectionCrop,500);})()`,
    );
    assert.equal(await tab.evaluate("document.querySelectorAll('.pdf-text-host').length"), 1);
    const resized = await tab.evaluate<{ left: number; width: number }>(`(()=>{
    const page=document.querySelector('.pdf-page').getBoundingClientRect();
    const span=[...document.querySelectorAll('.pdf-text-layer span')].find(span=>span.textContent.trim().length>20).getBoundingClientRect();
    return {left:span.left-page.left,width:span.width};
  })()`);
    assert.ok(Math.abs(resized.left - ((boxes[0].x - 30) * 5) / 7) < 2);
    assert.ok(Math.abs(resized.width - (boxes[0].width * 5) / 7) < 2);
  },
);

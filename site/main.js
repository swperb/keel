// Keel site: the hero's digital rain and the copy buttons. The page is
// complete without this script; both features are enhancements.

const GLYPHS = "ｱｲｳｴｵｶｷｸｹｺｻｼｽｾｿﾀﾁﾂﾃﾄﾅﾆﾇﾈﾉﾊﾋﾌﾍﾎﾏﾐﾑﾒﾓﾔﾕﾖﾗﾘﾙﾚﾛﾜﾝ0123456789+-*<=>";
const CELL = 16; // px per glyph
const TICK_MS = 80; // time between rain steps
const BG = "#050a07";

function randomGlyph() {
  return GLYPHS[Math.floor(Math.random() * GLYPHS.length)];
}

// Each column holds the row of its falling head. Every tick draws one glyph
// per column and paints a translucent background over the previous frame,
// which turns earlier glyphs into fading trails.
function startRain(canvas, animate) {
  const ctx = canvas.getContext("2d");
  let width = 0;
  let height = 0;
  let heads = [];

  function resize() {
    const box = canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    width = box.width;
    height = box.height;
    canvas.width = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.font = `${CELL}px "IBM Plex Mono", monospace`;
    ctx.fillStyle = BG;
    ctx.fillRect(0, 0, width, height);
    const columns = Math.ceil(width / CELL);
    const rows = Math.ceil(height / CELL);
    heads = Array.from({ length: columns }, () => Math.floor(Math.random() * rows));
    if (!animate) {
      // Reduced motion: one still frame of short trails.
      for (let i = 0; i < 12; i++) step();
    }
  }

  function step() {
    ctx.fillStyle = "rgba(5, 10, 7, 0.12)";
    ctx.fillRect(0, 0, width, height);
    ctx.fillStyle = "#4fbf78";
    heads.forEach((row, col) => {
      ctx.fillText(randomGlyph(), col * CELL, row * CELL);
      const offBottom = row * CELL > height;
      heads[col] = offBottom && Math.random() < 0.03 ? 0 : row + 1;
    });
  }

  resize();
  window.addEventListener("resize", resize);

  if (animate) {
    let last = 0;
    const frame = (now) => {
      if (now - last >= TICK_MS) {
        last = now;
        step();
      }
      requestAnimationFrame(frame);
    };
    requestAnimationFrame(frame);
  }
}

// Copy the text of the element named by data-copy. If the clipboard is
// unavailable, select the text so the reader can copy it themselves.
function setUpCopyButtons() {
  for (const button of document.querySelectorAll("[data-copy]")) {
    const source = document.getElementById(button.dataset.copy);
    const flash = (label) => {
      button.textContent = label;
      setTimeout(() => (button.textContent = "copy"), 1500);
    };
    const selectSource = () => {
      const range = document.createRange();
      range.selectNodeContents(source);
      const selection = window.getSelection();
      selection.removeAllRanges();
      selection.addRange(range);
      flash("selected");
    };
    button.addEventListener("click", () => {
      if (!navigator.clipboard) return selectSource();
      navigator.clipboard.writeText(source.textContent).then(() => flash("copied"), selectSource);
    });
  }
}

const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
startRain(document.getElementById("rain"), !reduceMotion);
setUpCopyButtons();

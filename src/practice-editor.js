const PCOLPractice = (() => {
  'use strict';
  const NAMES = ['白球', '红球', '黄球', '绿球', '棕球', '蓝球', '粉球', '黑球'];
  const COLOURS = ['#f7f6ec', '#db2538', '#f5ce42', '#329866', '#a16b42', '#418cdb', '#ef9cba', '#282d35'];
  const EPSILON = 1e-6;

  function placementError(layout, candidate, bounds) {
    const { x, z, r } = candidate;
    if (![x, z, r].every(Number.isFinite) || r <= 0) return '球的位置无效';
    if (x - r < bounds.minX - EPSILON || x + r > bounds.maxX + EPSILON ||
        z - r < bounds.minZ - EPSILON || z + r > bounds.maxZ + EPSILON) return '球不能越过库边';
    if (bounds.pockets.some(p => Math.hypot(x - p.x, z - p.z) < p.r + r - EPSILON)) return '球不能摆在袋口内';
    if (layout.some(b => b.active && b.i !== candidate.i && Math.hypot(x - b.x, z - b.z) < r + b.r - EPSILON)) return '与另一颗球重叠，请稍微移开';
    return '';
  }

  function createEditor({ document, window, container, balls, onSelect, onClear, onStandard, onCancel }) {
    const POSITION_KEY = 'pcol-rules-patch:practice-palette-position';
    const root = document.createElement('aside');
    root.className = 'pe-palette-panel';
    root.setAttribute('aria-label', '自由摆球');
    root.innerHTML = `
      <style>
        .pe-palette-panel{position:fixed;right:14px;top:86px;width:154px;max-width:calc(100vw - 16px);max-height:calc(100dvh - 16px);overflow:auto;overscroll-behavior:contain;z-index:1000;pointer-events:auto;box-sizing:border-box;padding:10px;border:1px solid #fffffff0;border-radius:20px;background:rgba(248,250,253,.92);backdrop-filter:blur(22px) saturate(110%);box-shadow:0 10px 35px #18243126,inset 0 1px 0 #ffffff;color:#1d1d1f;font:12px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI","Microsoft YaHei",sans-serif;scrollbar-width:thin;scrollbar-color:#a6acb5 transparent}
        .pe-palette-panel[hidden]{display:none}.pe-palette-panel *{box-sizing:border-box}.pe-palette-panel button{font:inherit;cursor:pointer}.pe-palette-panel button:disabled{opacity:.38;cursor:default}.pe-palette-panel button:focus-visible{outline:2px solid #007aff;outline-offset:2px}
        .pe-heading{margin:0 0 8px;padding:5px 2px 7px;text-align:center;font-size:16px;font-weight:600;letter-spacing:.02em;cursor:grab;touch-action:none;user-select:none}.pe-heading:active{cursor:grabbing}.pe-ball-list{display:grid;gap:3px}.pe-ball-button{display:flex;justify-content:center;align-items:center;width:100%;height:36px;padding:3px;border:1px solid transparent;border-radius:11px;background:transparent;transition:background .12s,border-color .12s}.pe-ball-button:hover{background:#ffffff80}.pe-ball-button[aria-pressed="true"]{background:#007aff12;border-color:#007aff85}.pe-orb{display:block;width:27px;height:27px;flex-shrink:0;border-radius:50%;background:radial-gradient(circle at 30% 22%,#ffffffc0,transparent 36%),var(--ball);box-shadow:inset -4px -5px 7px #0006,inset 1px 1px 2px #ffffff80,0 2px 4px #202d392b}
        .pe-controls{display:grid;grid-template-columns:1fr 1fr;gap:5px;margin-top:9px;padding-top:9px;border-top:1px solid #59616d1a}.pe-control{padding:7px 1px;color:#4b515a;border:1px solid #ffffffdb;border-radius:8px;background:#ffffff8a;font-size:10px!important;white-space:nowrap}.pe-control:hover:not(:disabled){background:#ffffff;color:#007aff}.pe-cancel{grid-column:1/-1;padding:6px 1px;border-color:transparent;background:transparent;color:#6e6e73}
        @media(max-height:590px){.pe-heading{margin-bottom:5px;padding-top:3px}.pe-ball-button{height:32px}.pe-orb{width:25px;height:25px}.pe-controls{margin-top:7px;padding-top:7px}}
        @media(prefers-reduced-motion:reduce){.pe-ball-button{transition:none}}
      </style>
      <h2 class="pe-heading">自由摆球</h2>
      <div class="pe-ball-list"></div>
      <div class="pe-controls">
        <button type="button" class="pe-control pe-clear">清空目标球</button>
        <button type="button" class="pe-control pe-standard">标准球形</button>
        <button type="button" class="pe-control pe-cancel">取消本次编辑</button>
      </div>`;
    const $ = selector => root.querySelector(selector);
    const heading = $('.pe-heading');
    const buttons = [];
    for (let n = 0; n <= 7; n++) {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'pe-ball-button';
      button.setAttribute('aria-label', `选择${NAMES[n]}`);
      button.title = NAMES[n];
      button.innerHTML = `<span class="pe-orb" style="--ball:${COLOURS[n]}" aria-hidden="true"></span>`;
      button.addEventListener('click', () => onSelect(n));
      $('.pe-ball-list').append(button);
      buttons.push(button);
    }
    $('.pe-clear').addEventListener('click', onClear);
    $('.pe-standard').addEventListener('click', onStandard);
    $('.pe-cancel').addEventListener('click', onCancel);
    for (const type of ['pointerdown', 'pointerup', 'pointermove', 'mousedown', 'mouseup', 'mousemove', 'click', 'dblclick', 'wheel', 'contextmenu']) {
      root.addEventListener(type, event => event.stopPropagation());
    }
    for (const type of ['keydown', 'keyup', 'keypress']) {
      root.addEventListener(type, event => {
        if (!['w', 'ArrowUp', 'Escape'].includes(event.key.length === 1 ? event.key.toLowerCase() : event.key)) event.stopPropagation();
      });
    }
    let position = null, drag = null;
    try {
      const saved = JSON.parse(window.localStorage.getItem(POSITION_KEY));
      if (Number.isFinite(saved?.x) && Number.isFinite(saved?.y)) position = saved;
    } catch (_) {}
    function savePosition() {
      try {
        if (position) window.localStorage.setItem(POSITION_KEY, JSON.stringify(position));
        else window.localStorage.removeItem(POSITION_KEY);
      } catch (_) {}
    }
    function place(x, y) {
      const rect = root.getBoundingClientRect();
      if (root.hidden || !rect.width || !rect.height) return;
      position = {
        x: Math.max(8, Math.min(x, window.innerWidth - rect.width - 8)),
        y: Math.max(8, Math.min(y, window.innerHeight - rect.height - 8))
      };
      root.style.left = `${position.x}px`;
      root.style.top = `${position.y}px`;
      root.style.right = 'auto';
    }
    function clamp() {
      const rect = root.getBoundingClientRect();
      place(position ? position.x : rect.left, position ? position.y : rect.top);
    }
    function finishDrag() {
      if (!drag) return;
      const pointerId = drag.pointerId;
      drag = null;
      if (heading.hasPointerCapture(pointerId)) heading.releasePointerCapture(pointerId);
      savePosition();
    }
    heading.addEventListener('pointerdown', event => {
      if (event.button !== 0) return;
      event.preventDefault();
      const rect = root.getBoundingClientRect();
      drag = { pointerId: event.pointerId, x: event.clientX - rect.left, y: event.clientY - rect.top };
      heading.setPointerCapture(event.pointerId);
    });
    heading.addEventListener('pointermove', event => {
      if (drag?.pointerId === event.pointerId) place(event.clientX - drag.x, event.clientY - drag.y);
    });
    for (const type of ['pointerup', 'pointercancel', 'lostpointercapture']) heading.addEventListener(type, finishDrag);
    heading.addEventListener('dblclick', () => {
      position = null;
      root.style.left = '';
      root.style.top = '';
      root.style.right = '';
      savePosition();
      clamp();
    });
    window.addEventListener('resize', clamp);
    function update(current, selectedIndex, editing = false) {
      const selected = current.find(b => b.i === selectedIndex);
      buttons.forEach((button, n) => button.setAttribute('aria-pressed', String(selected?.n === n)));
      buttons[1].title = `红球 · 已放 ${current.filter(b => b.n === 1 && b.active).length} / 15`;
      $('.pe-clear').disabled = !current.some(b => b.n !== 0 && b.active);
      $('.pe-cancel').disabled = !editing;
    }
    function setVisible(visible) {
      if (!visible) finishDrag();
      root.hidden = !visible;
      if (visible) clamp();
    }
    container.append(root);
    update(balls, null);
    clamp();
    return {
      update,
      setVisible,
      destroy() {
        finishDrag();
        window.removeEventListener('resize', clamp);
        root.remove();
      }
    };
  }
  return { placementError, createEditor };
})();
module.exports = PCOLPractice;

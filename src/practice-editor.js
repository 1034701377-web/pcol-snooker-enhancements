const PCOLPractice = (() => {
  'use strict';
  const NAMES = ['白球', '红球', '黄球', '绿球', '棕球', '蓝球', '粉球', '黑球'];
  const COLOURS = ['#f7f6ec', '#db2538', '#f5ce42', '#329866', '#a16b42', '#418cdb', '#ef9cba', '#282d35'];
  const EPSILON = 1e-6;
  const copy = layout => layout.map(b => ({ ...b, spot: { ...b.spot } }));
  let editorCount = 0;

  function placementError(layout, candidate, bounds) {
    const { x, z, r } = candidate;
    if (![x, z, r].every(Number.isFinite) || r <= 0) return '球的位置无效';
    if (x - r < bounds.minX - EPSILON || x + r > bounds.maxX + EPSILON ||
        z - r < bounds.minZ - EPSILON || z + r > bounds.maxZ + EPSILON) return '球不能越过库边';
    if (bounds.pockets.some(p => Math.hypot(x - p.x, z - p.z) < p.r + r - EPSILON)) return '球不能摆在袋口内';
    if (layout.some(b => b.active && b.i !== candidate.i && Math.hypot(x - b.x, z - b.z) < r + b.r - EPSILON)) return '与另一颗球重叠，请稍微移开';
    return '';
  }

  function validateLayout(layout, bounds) {
    const active = layout.filter(b => b.active);
    if (active.filter(b => b.n === 0).length !== 1) return '球台上必须保留一颗白球';
    for (let n = 1; n <= 7; n++) {
      if (active.filter(b => b.n === n).length > (n === 1 ? 15 : 1)) return `${NAMES[n]}数量超出限制`;
    }
    for (const ball of active) {
      const error = placementError(layout, ball, bounds);
      if (error) return `${NAMES[ball.n]}：${error}`;
    }
    return '';
  }

  function createEditor({ document, window, container, balls, bounds, onApply, onCancel }) {
    const initial = copy(balls);
    let layout = copy(balls), selected = null, palette = balls.some(b => b.n === 1 && !b.active) ? 1 : null, drag = null, ghost = null;
    const history = [];
    const id = `pcol-practice-${++editorCount}`;
    const width = bounds.maxX - bounds.minX, height = bounds.maxZ - bounds.minZ;
    const padding = Math.min(width, height) * 0.075;
    const center = { x: (bounds.minX + bounds.maxX) / 2, z: (bounds.minZ + bounds.maxZ) / 2 };
    let cursor = { ...center };
    const previousFocus = container.getRootNode().activeElement || document.activeElement;
    const root = document.createElement('div');
    root.className = 'pe-root';
    root.setAttribute('role', 'dialog');
    root.setAttribute('aria-modal', 'true');
    root.setAttribute('aria-labelledby', `${id}-title`);
    root.innerHTML = `
      <style>
        .pe-root{position:fixed;inset:0;z-index:1000;display:grid;place-items:center;padding:22px;background:rgba(3,10,10,.82);backdrop-filter:blur(12px);color:#e7eee9;font:14px/1.5 system-ui,-apple-system,"Segoe UI","Microsoft YaHei",sans-serif;box-sizing:border-box}
        .pe-root *{box-sizing:border-box}.pe-root button,.pe-root select{font:inherit}.pe-root button{cursor:pointer}.pe-root button:disabled{opacity:.34;cursor:default}
        .pe-card{width:min(1150px,100%);max-height:calc(100dvh - 44px);overflow:auto;border:1px solid #476158;border-radius:20px;background:linear-gradient(145deg,#152723,#0b1916);box-shadow:0 28px 100px #0009}
        .pe-header{display:flex;align-items:center;justify-content:space-between;gap:20px;padding:24px 28px 18px;border-bottom:1px solid #ffffff12}.pe-eyebrow{color:#c8ac72;letter-spacing:.2em;font-size:10px;font-weight:700}.pe-title{margin:3px 0 2px;font-size:24px;letter-spacing:.03em;font-weight:650}.pe-subtitle{color:#9bb0a6;font-size:12px}.pe-count{text-align:right;color:#bfcebf;font-variant-numeric:tabular-nums;white-space:nowrap}
        .pe-workspace{display:grid;grid-template-columns:minmax(0,1fr) 236px;gap:24px;padding:24px 28px}.pe-board{min-width:0;display:flex;flex-direction:column;justify-content:center}.pe-table{width:100%;max-height:55vh;display:block;touch-action:none;user-select:none;overflow:visible;border-radius:16px;outline:none}.pe-table:focus-visible{box-shadow:0 0 0 2px #d7b778}.pe-ball{cursor:grab}.pe-ball:hover .pe-ball-body{filter:brightness(1.18)}.pe-ball.pe-selected .pe-selection{opacity:1}
        .pe-board-caption{display:flex;justify-content:space-between;gap:12px;padding:14px 8px 0;color:#8ba397;font-size:11px}.pe-board-caption kbd{font:inherit;color:#c8d6ce;border:1px solid #ffffff28;border-radius:3px;padding:1px 4px}
        .pe-sidebar{border-left:1px solid #ffffff12;padding-left:24px;display:flex;flex-direction:column;gap:20px}.pe-label{display:flex;justify-content:space-between;gap:8px;color:#c5d3cb;font-size:12px;font-weight:600;margin-bottom:9px}.pe-label span{color:#839d8e;font-size:10px;font-weight:400;letter-spacing:.05em}.pe-palette{display:grid;grid-template-columns:repeat(4,1fr);gap:7px}
        .pe-swatch{display:flex;flex-direction:column;align-items:center;gap:5px;padding:9px 2px 7px;background:#ffffff04;border:1px solid #ffffff13;border-radius:9px;color:#b8c7bd;font-size:10px!important}.pe-swatch[aria-pressed="true"]{background:#c5a36c19;border-color:#c9ab72;color:#f0dbae}.pe-swatch:hover:not(:disabled){background:#ffffff0c}.pe-orb{display:block;width:20px;height:20px;border-radius:50%;background:radial-gradient(circle at 32% 25%,#ffffff95,transparent 38%),var(--ball);box-shadow:inset -3px -4px 6px #0005,0 2px 4px #0007}
        .pe-help{color:#839d8e;font-size:11px;margin:8px 0 0;min-height:34px}.pe-select{width:100%;padding:8px 9px;border:1px solid #ffffff20;border-radius:8px;background:#10211b;color:#e3ece6;outline:none}.pe-select:focus-visible,.pe-root button:focus-visible{outline:2px solid #d7b778;outline-offset:3px}.pe-select option{background:#10211b}.pe-coordinate{min-height:20px;margin:7px 0;color:#91a89b;font-size:11px;font-variant-numeric:tabular-nums}.pe-button{padding:8px 11px;border:1px solid #ffffff22;border-radius:8px;background:#ffffff06;color:#cbd8d0}.pe-button:hover:not(:disabled){background:#ffffff10;border-color:#ffffff3a}.pe-button.pe-remove{width:100%;color:#dab6ab}.pe-tools{display:grid;gap:7px;margin-top:auto}.pe-tool-row{display:grid;grid-template-columns:1fr 1fr;gap:7px}.pe-tools .pe-button{font-size:11px}
        .pe-footer{display:flex;align-items:center;gap:18px;justify-content:space-between;padding:17px 28px 21px;background:#00000013;border-top:1px solid #ffffff12}.pe-status{font-size:12px;color:#b3c6b8;min-height:18px}.pe-status[data-error="true"]{color:#ffaaa0}.pe-actions{display:flex;gap:9px;flex-shrink:0}.pe-start{background:#d6b779;color:#17251c;border-color:#d6b779;padding:9px 22px;font-weight:650}.pe-start:hover:not(:disabled){background:#e6ca92;border-color:#e6ca92}
        @media(min-width:781px) and (max-height:720px){.pe-header{padding:10px 24px}.pe-title{font-size:21px;margin:1px 0}.pe-workspace{padding:10px 24px;gap:20px}.pe-sidebar{gap:8px;padding-left:20px}.pe-label{margin-bottom:5px}.pe-swatch{padding:5px 2px;gap:3px}.pe-orb{width:17px;height:17px}.pe-help{min-height:25px;margin-top:5px}.pe-select{padding:5px 8px}.pe-coordinate{min-height:16px;margin:4px 0}.pe-sidebar .pe-button{padding:5px 8px}.pe-tools{gap:5px}.pe-footer{padding:9px 24px}.pe-board-caption{padding-top:10px}}
        @media(max-width:780px){.pe-root{padding:10px}.pe-card{max-height:calc(100dvh - 20px);border-radius:14px}.pe-header{padding:18px 18px 14px}.pe-title{font-size:21px}.pe-workspace{grid-template-columns:1fr;gap:18px;padding:18px}.pe-sidebar{border-left:0;border-top:1px solid #ffffff12;padding:16px 0 0;display:grid;grid-template-columns:1fr 1fr;gap:16px}.pe-tools{grid-column:1/-1;grid-template-columns:1fr 1fr;gap:8px}.pe-tools .pe-reset{grid-column:1/-1}.pe-palette{gap:5px}.pe-footer{padding:15px 18px;align-items:stretch;flex-direction:column;gap:12px}.pe-actions{justify-content:flex-end}.pe-table{max-height:43vh}.pe-count{font-size:11px}.pe-board-caption{padding-top:10px;flex-wrap:wrap}.pe-subtitle{font-size:11px}}
        @media(prefers-reduced-motion:no-preference){.pe-card{animation:pe-enter .18s ease-out}@keyframes pe-enter{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}}
      </style>
      <section class="pe-card">
        <header class="pe-header"><div><div class="pe-eyebrow">PRACTICE STUDIO</div><h2 class="pe-title" id="${id}-title">摆一桌自己的练习</h2><div class="pe-subtitle">留下想练的球，摆到想练的位置。</div></div><div class="pe-count"></div></header>
        <div class="pe-workspace">
          <div class="pe-board"><svg class="pe-table" xmlns="http://www.w3.org/2000/svg" tabindex="0" role="group" aria-label="俯视球台：点击放球、拖动移球。选中球后可用方向键微调。"></svg><div class="pe-board-caption"><span>点球盘，再点桌面放球 · 拖动球可移动</span><span><kbd>方向键</kbd> 1 cm · <kbd>Shift</kbd> 1 mm</span></div></div>
          <aside class="pe-sidebar">
            <div><div class="pe-label">球盘<span>选球 · 放置</span></div><div class="pe-palette"></div><p class="pe-help"></p></div>
            <div><label class="pe-label" for="${id}-selected">选中球<span>精细调整</span></label><select class="pe-select" id="${id}-selected" aria-label="选择要调整的球"></select><div class="pe-coordinate"></div><button type="button" class="pe-button pe-remove">移除选中球</button></div>
            <div class="pe-tools"><div class="pe-tool-row"><button type="button" class="pe-button pe-undo">撤销一步</button><button type="button" class="pe-button pe-clear">清空目标球</button></div><button type="button" class="pe-button pe-standard">标准球形</button><button type="button" class="pe-button pe-reset">还原本次编辑</button></div>
          </aside>
        </div>
        <footer class="pe-footer"><div class="pe-status" role="status" aria-live="polite"></div><div class="pe-actions"><button type="button" class="pe-button pe-cancel">取消</button><button type="button" class="pe-button pe-start">开始练习 ↗</button></div></footer>
      </section>`;
    container.append(root);
    const $ = selector => root.querySelector(selector);
    const svg = $('.pe-table');
    const status = $('.pe-status');
    const paletteElement = $('.pe-palette');
    const selectedElement = $('.pe-select');
    const ns = 'http://www.w3.org/2000/svg';
    const element = (name, attrs, parent) => {
      const el = document.createElementNS(ns, name);
      for (const [key, value] of Object.entries(attrs)) el.setAttribute(key, value);
      if (parent) parent.append(el);
      return el;
    };
    svg.setAttribute('viewBox', `${bounds.minX - padding} ${bounds.minZ - padding} ${width + 2 * padding} ${height + 2 * padding}`);
    const defs = element('defs', {}, svg);
    const cloth = element('linearGradient', { id: `${id}-cloth`, x1: 0, y1: 0, x2: 1, y2: 1 }, defs);
    element('stop', { offset: 0, 'stop-color': '#24705a' }, cloth);
    element('stop', { offset: 1, 'stop-color': '#164c3d' }, cloth);
    COLOURS.forEach((colour, n) => {
      const gradient = element('radialGradient', { id: `${id}-ball-${n}`, cx: '.3', cy: '.25', r: '.8' }, defs);
      element('stop', { offset: 0, 'stop-color': n === 7 ? '#677079' : '#ffffff' }, gradient);
      element('stop', { offset: '.25', 'stop-color': colour }, gradient);
      element('stop', { offset: 1, 'stop-color': n === 0 ? '#b9c1b8' : colour, 'stop-opacity': '.84' }, gradient);
    });
    element('rect', { x: bounds.minX - padding, y: bounds.minZ - padding, width: width + padding * 2, height: height + padding * 2, rx: padding * .5, fill: '#342d22', stroke: '#6a5b3e', 'stroke-width': padding * .06 }, svg);
    element('rect', { x: bounds.minX - padding * .35, y: bounds.minZ - padding * .35, width: width + padding * .7, height: height + padding * .7, rx: padding * .12, fill: '#123d31', stroke: '#8c9a6855', 'stroke-width': padding * .03 }, svg);
    element('rect', { x: bounds.minX, y: bounds.minZ, width, height, fill: `url(#${id}-cloth)` }, svg);
    const lineStyle = { stroke: '#c4d1b86b', 'stroke-width': width * .0006, fill: 'none' };
    element('line', { x1: bounds.baulkX, x2: bounds.baulkX, y1: bounds.minZ, y2: bounds.maxZ, ...lineStyle }, svg);
    const baulkSide = bounds.baulkX - bounds.minX < bounds.maxX - bounds.baulkX ? -1 : 1;
    const arc = [];
    for (let step = 0; step <= 40; step++) {
      const angle = -Math.PI / 2 + Math.PI * step / 40;
      arc.push(`${step ? 'L' : 'M'}${bounds.baulkX + baulkSide * bounds.dRadius * Math.cos(angle)},${center.z + bounds.dRadius * Math.sin(angle)}`);
    }
    element('path', { d: arc.join(' '), ...lineStyle }, svg);
    for (const ball of balls.filter(b => b.n >= 2)) {
      element('circle', { cx: ball.spot.x, cy: ball.spot.z, r: width * .0011, fill: '#e3d4ac85' }, svg);
    }
    for (const pocket of bounds.pockets) {
      element('circle', { cx: pocket.x, cy: pocket.z, r: pocket.r, fill: '#06100d', stroke: '#ae90504d', 'stroke-width': width * .0015 }, svg);
    }
    const ballLayer = element('g', {}, svg);
    const previewLayer = element('g', { 'pointer-events': 'none' }, svg);

    function notice(text, error = false) {
      status.textContent = text;
      status.dataset.error = String(error);
    }
    function remember() {
      history.push(copy(layout));
      if (history.length > 80) history.shift();
    }
    function activeName(ball) { return ball.n === 1 ? `红球 ${ball.i}` : NAMES[ball.n]; }
    function drawBall(ball, parent, preview = false, error = '') {
      const group = element('g', { transform: `translate(${ball.x} ${ball.z})`, class: `pe-ball${ball.i === selected && !preview ? ' pe-selected' : ''}`, ...(preview ? { opacity: '.7' } : { 'data-ball': ball.i, role: 'button', 'aria-label': activeName(ball) }) }, parent);
      element('circle', { cy: ball.r * .13, r: ball.r * 1.03, fill: '#00000065' }, group);
      element('circle', { r: ball.r, fill: `url(#${id}-ball-${ball.n})`, stroke: '#ffffff35', 'stroke-width': ball.r * .055, class: 'pe-ball-body' }, group);
      element('circle', { r: ball.r * 1.32, fill: 'none', stroke: error ? '#ff9282' : '#f2d293', 'stroke-width': ball.r * .095, opacity: preview ? 1 : 0, class: 'pe-selection', 'stroke-dasharray': preview ? `${ball.r * .26} ${ball.r * .15}` : 'none' }, group);
      if (!preview) {
        const title = element('title', {}, group);
        title.textContent = activeName(ball);
      }
    }
    function renderBalls() {
      ballLayer.replaceChildren();
      for (const ball of layout.filter(b => b.active)) {
        if (drag && ball.i === drag.i) continue;
        drawBall(ball, ballLayer);
      }
      renderPreview();
    }
    function renderPreview() {
      previewLayer.replaceChildren();
      if (ghost) drawBall(ghost.ball, previewLayer, true, ghost.error);
    }
    function render() {
      renderBalls();
      const active = layout.filter(b => b.active), selectedBall = active.find(b => b.i === selected);
      const reds = active.filter(b => b.n === 1).length;
      $('.pe-count').textContent = `${active.length} 颗球 · 红球 ${reds} / 15`;
      for (const button of paletteElement.children) {
        const n = Number(button.dataset.n);
        button.setAttribute('aria-pressed', String(palette === n));
        button.disabled = n === 1 && reds === 15;
      }
      $('.pe-help').textContent = palette == null ? '拖动选中球，或在球台上用方向键微调。' : palette === 1 ? '连续点桌面添加红球，最多 15 颗。' : `点桌面放置${NAMES[palette]}；已有的球会移到新位置。`;
      selectedElement.replaceChildren();
      const option = document.createElement('option');
      option.value = '';
      option.textContent = '选择桌上的球…';
      selectedElement.append(option);
      for (const ball of active) {
        const entry = document.createElement('option');
        entry.value = ball.i;
        entry.textContent = activeName(ball);
        selectedElement.append(entry);
      }
      selectedElement.value = selectedBall ? String(selectedBall.i) : '';
      $('.pe-coordinate').textContent = selectedBall ? `距左库 ${((selectedBall.x - bounds.minX) * 100).toFixed(1)} cm · 上库 ${((selectedBall.z - bounds.minZ) * 100).toFixed(1)} cm` : '白球始终保留在球台上';
      $('.pe-remove').disabled = !selectedBall || selectedBall.n === 0;
      $('.pe-undo').disabled = history.length === 0;
      $('.pe-reset').disabled = history.length === 0;
      $('.pe-clear').disabled = active.length === 1;
    }
    function candidateAt(position) {
      if (palette == null) return null;
      const ball = palette === 1 ? layout.find(b => b.n === 1 && !b.active) : layout.find(b => b.n === palette);
      return ball ? { ...ball, active: true, x: position.x, y: ball.spot.y, z: position.z } : null;
    }
    function previewAt(position) {
      cursor = position;
      const ball = candidateAt(position);
      ghost = ball ? { ball, error: placementError(layout, ball, bounds) } : null;
      renderPreview();
    }
    function place(position) {
      cursor = position;
      const ball = candidateAt(position);
      if (!ball) return;
      const error = placementError(layout, ball, bounds);
      if (error) { notice(error, true); return; }
      remember();
      layout[layout.findIndex(b => b.i === ball.i)] = ball;
      selected = ball.i;
      if (palette !== 1 || layout.filter(b => b.n === 1 && b.active).length === 15) palette = null;
      ghost = null;
      notice(`${activeName(ball)}已摆好；还可以继续添加或调整。`);
      render();
    }
    function point(event) {
      const p = svg.createSVGPoint();
      p.x = event.clientX;
      p.y = event.clientY;
      const transformed = p.matrixTransform(svg.getScreenCTM().inverse());
      return { x: transformed.x, z: transformed.y };
    }
    function cancelDrag() {
      if (!drag) return;
      const pointerId = drag.pointerId;
      drag = null;
      ghost = null;
      if (svg.hasPointerCapture(pointerId)) svg.releasePointerCapture(pointerId);
      renderBalls();
    }
    function cancel() { onCancel(); }
    function remove() {
      const ball = layout.find(b => b.i === selected);
      if (!ball || ball.n === 0) return;
      remember();
      ball.active = false;
      selected = null;
      ghost = null;
      notice(`${activeName(ball)}已放回球盘。`);
      render();
    }
    function undo() {
      if (!history.length) return;
      cancelDrag();
      layout = history.pop();
      selected = null;
      ghost = null;
      notice('已撤销上一步摆球。');
      render();
    }

    for (let n = 0; n <= 7; n++) {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'pe-swatch';
      button.dataset.n = n;
      button.setAttribute('aria-label', `放置${NAMES[n]}`);
      button.innerHTML = `<span class="pe-orb" style="--ball:${COLOURS[n]}" aria-hidden="true"></span><span>${NAMES[n].replace('球', '')}</span>`;
      button.addEventListener('click', () => {
        palette = n;
        selected = null;
        ghost = null;
        cursor = { ...center };
        notice(`已选${NAMES[n]}：点击桌面放置，也可将焦点移到球台后按 Enter。`);
        render();
        svg.focus();
      });
      paletteElement.append(button);
    }
    selectedElement.addEventListener('change', () => {
      selected = selectedElement.value === '' ? null : Number(selectedElement.value);
      palette = null;
      ghost = null;
      render();
      svg.focus();
      notice('用方向键移动 1 cm；按住 Shift 移动 1 mm。');
    });
    svg.addEventListener('pointerdown', event => {
      if (event.button !== 0) return;
      event.preventDefault();
      svg.focus();
      const position = point(event);
      const hit = event.target.closest('[data-ball]');
      if (hit) {
        selected = Number(hit.dataset.ball);
        palette = null;
        const ball = layout.find(b => b.i === selected);
        drag = { i: selected, pointerId: event.pointerId, offsetX: position.x - ball.x, offsetZ: position.z - ball.z };
        ghost = { ball: { ...ball }, error: '' };
        svg.setPointerCapture(event.pointerId);
        notice(`${activeName(ball)} · 拖动摆放，Esc 取消这次移动。`);
        render();
      } else {
        place(position);
      }
    });
    svg.addEventListener('pointermove', event => {
      const position = point(event);
      if (drag) {
        const original = layout.find(b => b.i === drag.i);
        const ball = { ...original, x: position.x - drag.offsetX, z: position.z - drag.offsetZ };
        const error = placementError(layout, ball, bounds);
        ghost = { ball, error };
        notice(error || `${activeName(ball)} · 松手确认位置`, !!error);
        renderPreview();
      } else if (palette != null) previewAt(position);
    });
    svg.addEventListener('pointerup', event => {
      if (!drag || drag.pointerId !== event.pointerId) return;
      const { ball, error } = ghost;
      const original = layout.find(b => b.i === drag.i);
      if (!error && (original.x !== ball.x || original.z !== ball.z)) {
        remember();
        layout[layout.findIndex(b => b.i === ball.i)] = ball;
      }
      cancelDrag();
      notice(error ? `${error}，已回到原位。` : `${activeName(ball)}已选中，可用方向键微调。`, !!error);
      render();
    });
    svg.addEventListener('pointercancel', cancelDrag);
    svg.addEventListener('lostpointercapture', cancelDrag);
    svg.addEventListener('pointerleave', () => {
      if (drag) return;
      ghost = null;
      renderPreview();
    });
    root.addEventListener('keydown', event => {
      event.stopPropagation();
      if (event.key === 'Escape') {
        event.preventDefault();
        if (drag) { cancelDrag(); notice('已取消这次移动。'); } else cancel();
        return;
      }
      if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 'z') {
        event.preventDefault();
        undo();
        return;
      }
      if (event.key === 'Tab') {
        const focusable = [...root.querySelectorAll('button:not(:disabled),select,svg[tabindex]')];
        const current = root.getRootNode().activeElement;
        if (event.shiftKey && current === focusable[0]) { event.preventDefault(); focusable.at(-1).focus(); }
        else if (!event.shiftKey && current === focusable.at(-1)) { event.preventDefault(); focusable[0].focus(); }
        return;
      }
      if (event.target !== svg) return;
      if ((event.key === 'Enter' || event.key === ' ') && palette != null) {
        event.preventDefault();
        place(cursor);
        return;
      }
      if (event.key === 'Delete' || event.key === 'Backspace') { event.preventDefault(); remove(); return; }
      const directions = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] };
      if (!directions[event.key]) return;
      event.preventDefault();
      const [dx, dz] = directions[event.key], step = event.shiftKey ? .001 : .01;
      if (palette != null) { previewAt({ x: cursor.x + dx * step, z: cursor.z + dz * step }); return; }
      const ball = layout.find(b => b.i === selected);
      if (!ball) return;
      const candidate = { ...ball, x: ball.x + dx * step, z: ball.z + dz * step };
      const error = placementError(layout, candidate, bounds);
      if (error) { notice(error, true); return; }
      remember();
      layout[layout.findIndex(b => b.i === ball.i)] = candidate;
      notice(`${activeName(ball)}已微调。`);
      render();
    });
    root.addEventListener('keyup', event => event.stopPropagation());
    root.addEventListener('keypress', event => event.stopPropagation());
    root.addEventListener('pointerdown', event => event.stopPropagation());
    root.addEventListener('pointerup', event => event.stopPropagation());
    root.addEventListener('click', event => event.stopPropagation());
    for (const type of ['mousedown', 'mouseup', 'mousemove', 'wheel']) root.addEventListener(type, event => event.stopPropagation());
    $('.pe-remove').addEventListener('click', remove);
    $('.pe-undo').addEventListener('click', undo);
    $('.pe-clear').addEventListener('click', () => {
      remember();
      for (const ball of layout) if (ball.n !== 0) ball.active = false;
      selected = null;
      palette = 1;
      ghost = null;
      notice('目标球已收起，白球保留。可以开始摆球。');
      render();
    });
    $('.pe-standard').addEventListener('click', () => {
      const standard = layout.map(b => ({ ...b, active: true, ...b.spot }));
      const error = validateLayout(standard, bounds);
      if (error) { notice(error, true); return; }
      remember();
      layout = standard;
      selected = null;
      palette = null;
      ghost = null;
      notice('已摆回完整标准球形。');
      render();
    });
    $('.pe-reset').addEventListener('click', () => {
      layout = copy(initial);
      history.length = 0;
      selected = null;
      palette = initial.some(b => b.n === 1 && !b.active) ? 1 : null;
      ghost = null;
      notice('已还原到打开摆球界面时的位置。');
      render();
    });
    $('.pe-cancel').addEventListener('click', cancel);
    $('.pe-start').addEventListener('click', () => {
      const error = validateLayout(layout, bounds);
      if (error) { notice(error, true); return; }
      onApply(copy(layout));
    });
    notice('选球、摆球，准备好后开始练习。每一杆结束都可以复位重打。');
    render();
    svg.focus();
    return {
      destroy() {
        cancelDrag();
        root.remove();
        if (previousFocus?.isConnected) previousFocus.focus();
      }
    };
  }
  return { placementError, validateLayout, createEditor };
})();
module.exports = PCOLPractice;

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

  function createEditor({ document, container, balls, onSelect, onSelectRed, onRemove, onClear, onStandard, onDone, onCancel }) {
    const root = document.createElement('aside');
    root.className = 'pe-palette-panel';
    root.setAttribute('aria-label', '三维球台摆球工具');
    root.innerHTML = `
      <style>
        .pe-palette-panel{position:fixed;right:14px;top:100px;width:165px;max-height:calc(100dvh - 114px);overflow-y:auto;overscroll-behavior:contain;z-index:1000;pointer-events:auto;box-sizing:border-box;padding:12px 10px 10px;border:1px solid #64726070;border-radius:15px;background:linear-gradient(150deg,#172b25f5,#0b1916f5);box-shadow:0 12px 38px #0007;color:#e7eee9;font:12px/1.4 system-ui,-apple-system,"Segoe UI","Microsoft YaHei",sans-serif;scrollbar-width:thin;scrollbar-color:#526a59 transparent}
        .pe-palette-panel *{box-sizing:border-box}.pe-palette-panel button,.pe-palette-panel select{font:inherit}.pe-palette-panel button{cursor:pointer}.pe-palette-panel button:disabled{opacity:.35;cursor:default}.pe-palette-panel button:focus-visible,.pe-palette-panel select:focus-visible{outline:2px solid #e1c18b;outline-offset:2px}
        .pe-eyebrow{color:#c9ad76;letter-spacing:.15em;font-size:8px;font-weight:700}.pe-heading{margin:2px 0 7px;font-size:17px;font-weight:600;letter-spacing:.08em}.pe-hint{margin:0 0 10px;color:#a7bbae;font-size:10px;line-height:1.55}.pe-green{color:#80d3a2}.pe-orange{color:#e7b076}
        .pe-ball-list{display:grid;gap:3px}.pe-ball-button{display:flex;align-items:center;gap:10px;width:100%;padding:6px 8px;text-align:left;color:#d5e1d8;border:1px solid transparent;border-radius:9px;background:#ffffff03}.pe-ball-button:hover{background:#ffffff0b}.pe-ball-button[aria-pressed="true"]{background:#d0b17718;border-color:#d0b177;color:#f2dca9}.pe-orb{flex-shrink:0;display:block;width:24px;height:24px;border-radius:50%;background:radial-gradient(circle at 30% 23%,#ffffffa8 0,transparent 34%),var(--ball);box-shadow:inset -4px -5px 7px #0007,inset 1px 1px 2px #ffffff55,0 3px 5px #0008}.pe-ball-text{display:block;min-width:0}.pe-ball-name{display:block;font-size:12px}.pe-ball-state{display:block;margin-top:1px;color:#8fa699;font-size:9px;font-variant-numeric:tabular-nums}
        .pe-red-select{display:block;width:calc(100% - 8px);margin:2px 4px 5px;padding:5px 6px;border:1px solid #ffffff20;border-radius:6px;background:#10231c;color:#c5d5ca;font-size:10px!important}.pe-red-select option{background:#10231c}.pe-status{margin:9px 2px 8px;min-height:29px;color:#b9cdbd;font-size:10px;line-height:1.45;overflow-wrap:anywhere}.pe-controls{display:grid;grid-template-columns:1fr 1fr;gap:5px;border-top:1px solid #ffffff12;padding-top:9px}.pe-control{padding:6px 3px;color:#c3d2c8;border:1px solid #ffffff20;border-radius:7px;background:#ffffff05;font-size:10px!important}.pe-control:hover:not(:disabled){background:#ffffff0c}.pe-remove{grid-column:1/-1;color:#deb9aa}.pe-done{grid-column:1/-1;padding:8px 4px;background:#d6b779;color:#14231b;border-color:#d6b779;font-size:12px!important;font-weight:650}.pe-done:hover:not(:disabled){background:#e2c88f}.pe-cancel{grid-column:1/-1;border-color:transparent;background:transparent;color:#829c8c;padding:4px}.pe-cancel:hover:not(:disabled){color:#c9d7ce;background:#ffffff06}
        @media(max-height:660px){.pe-palette-panel{top:82px;max-height:calc(100dvh - 92px);padding-top:9px;overflow-anchor:none}.pe-eyebrow{display:none}.pe-heading{font-size:15px;margin:0 0 4px}.pe-hint{font-size:9px;line-height:1.35;margin-bottom:4px}.pe-ball-list{gap:2px}.pe-ball-button{padding:3px 6px;gap:7px;min-height:28px}.pe-orb{width:20px;height:20px}.pe-ball-text{display:flex;align-items:center;gap:5px;white-space:nowrap}.pe-ball-name{font-size:11px}.pe-ball-state{font-size:8px;margin:0}.pe-red-select{padding:3px 6px;margin-bottom:2px}.pe-status{min-height:24px;line-height:1.25;font-size:9px;margin:5px 2px}.pe-controls{padding-top:5px;gap:4px}.pe-control{padding:4px 3px}.pe-done{padding:6px 4px}.pe-cancel{padding:2px}.pe-heading{font-size:15px}}
        @media(max-width:580px){.pe-palette-panel{right:7px;width:150px}}
      </style>
      <div class="pe-eyebrow">PRACTICE STUDIO</div>
      <h2 class="pe-heading">自由摆球</h2>
      <p class="pe-hint">选球后在原球台点放<br><span class="pe-green">绿圈可放</span> · <span class="pe-orange">橙圈不可放</span></p>
      <div class="pe-ball-list"></div>
      <div class="pe-status" role="status" aria-live="polite"></div>
      <div class="pe-controls">
        <button type="button" class="pe-control pe-remove">移除选中球</button>
        <button type="button" class="pe-control pe-clear">清空目标球</button>
        <button type="button" class="pe-control pe-standard">标准球形</button>
        <button type="button" class="pe-control pe-done">完成摆球 ↗</button>
        <button type="button" class="pe-control pe-cancel">取消本次编辑</button>
      </div>`;
    const $ = selector => root.querySelector(selector);
    const list = $('.pe-ball-list');
    const buttons = [];
    const redSelect = document.createElement('select');
    redSelect.className = 'pe-red-select';
    redSelect.setAttribute('aria-label', '添加或选择已放置的红球');
    for (let n = 0; n <= 7; n++) {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'pe-ball-button';
      button.setAttribute('aria-label', `选择${NAMES[n]}`);
      button.innerHTML = `<span class="pe-orb" style="--ball:${COLOURS[n]}" aria-hidden="true"></span><span class="pe-ball-text"><span class="pe-ball-name">${NAMES[n]}</span><span class="pe-ball-state"></span></span>`;
      button.addEventListener('click', () => onSelect(n));
      list.append(button);
      buttons.push(button);
      if (n === 1) list.append(redSelect);
    }
    redSelect.addEventListener('change', () => onSelectRed(redSelect.value === '' ? null : Number(redSelect.value)));
    $('.pe-remove').addEventListener('click', onRemove);
    $('.pe-clear').addEventListener('click', onClear);
    $('.pe-standard').addEventListener('click', onStandard);
    $('.pe-done').addEventListener('click', onDone);
    $('.pe-cancel').addEventListener('click', onCancel);
    for (const type of ['pointerdown', 'pointerup', 'pointermove', 'mousedown', 'mouseup', 'mousemove', 'click', 'dblclick', 'wheel', 'contextmenu']) {
      root.addEventListener(type, event => event.stopPropagation());
    }
    for (const type of ['keydown', 'keyup', 'keypress']) {
      root.addEventListener(type, event => { if (event.key !== 'Escape') event.stopPropagation(); });
    }
    let redKey = null;
    function update(current, selectedIndex, message = '') {
      const selected = current.find(b => b.i === selectedIndex);
      const reds = current.filter(b => b.n === 1 && b.active);
      buttons.forEach((button, n) => {
        button.setAttribute('aria-pressed', String(selected?.n === n));
        button.querySelector('.pe-ball-state').textContent = n === 1 ? `已放 ${reds.length} / 15` : current.some(b => b.n === n && b.active) ? '已放 · 可移动' : '待放';
      });
      const key = reds.map(b => b.i).join(',');
      if (redKey !== key) {
        redKey = key;
        const option = document.createElement('option');
        option.value = '';
        option.textContent = reds.length === 15 ? '红球已全部放置' : '＋ 新增一颗红球';
        option.disabled = reds.length === 15;
        redSelect.replaceChildren(option);
        for (const ball of reds) {
          const entry = document.createElement('option');
          entry.value = ball.i;
          entry.textContent = `移动红球 ${ball.i}`;
          redSelect.append(entry);
        }
      }
      redSelect.value = selected?.n === 1 && selected.active ? String(selected.i) : '';
      $('.pe-remove').disabled = !selected || !selected.active || selected.n === 0;
      $('.pe-clear').disabled = !current.some(b => b.n !== 0 && b.active);
      $('.pe-status').textContent = message || (selected ? `正在摆放${NAMES[selected.n]}，移动鼠标选择落点。` : '选择球盘中的球开始摆放。');
    }
    container.append(root);
    update(balls, null);
    root.scrollTop=0;
    return { update, destroy() { root.remove(); } };
  }
  return { placementError, createEditor };
})();
module.exports = PCOLPractice;

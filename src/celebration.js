const PCOLCelebration = (() => {
  'use strict';
  const DURATION = 3200;
  const STYLE = `
    :host { all: initial; position: fixed; z-index: 2147483646; inset: 19% 16px auto;
      display: flex; justify-content: center; pointer-events: none; color-scheme: dark; }
    *, *::before, *::after { box-sizing: border-box; }
    .card { position: relative; display: flex; align-items: center; gap: 28px;
      width: min(580px, 100%); min-height: 164px; padding: 24px 38px;
      color: #f9efd5; border: 1px solid #d8b87466; border-radius: 3px;
      background: radial-gradient(ellipse at 18% 75%, #355c4380, transparent 60%),
        linear-gradient(115deg, #102d25f5, #0b1e1af5 70%, #172e24f5);
      box-shadow: 0 18px 70px #0008, inset 0 0 36px #d7bd6b08;
      font: 14px/1.4 "Microsoft YaHei", "PingFang SC", sans-serif;
      animation: arrival ${DURATION}ms cubic-bezier(.22,.8,.3,1) both; }
    .card::before, .card::after { content: ''; position: absolute; height: 1px;
      left: 25px; right: 25px; background: linear-gradient(90deg, transparent, #edcc85, transparent); }
    .card::before { top: 7px; } .card::after { bottom: 7px; }
    .glow { position: absolute; inset: 0; overflow: hidden; border-radius: inherit; }
    .glow::before { content: ''; position: absolute; inset: -100% -50%;
      background: linear-gradient(110deg, transparent 43%, #fff3be18 49%, transparent 55%);
      animation: glint 1500ms 250ms ease-out both; }
    .score { position: relative; flex: 0 0 auto; min-width: 150px; text-align: center;
      border-right: 1px solid #c5a46555; padding-right: 28px; }
    .number { display: block; color: #f8dea0; font: 500 80px/.95 Georgia, "Times New Roman", serif;
      font-variant-numeric: tabular-nums; letter-spacing: -5px; text-shadow: 0 0 30px #f4ca6750; }
    .score-label { display: block; margin-top: 12px; color: #c4b791; font-size: 10px; letter-spacing: 4px; }
    .words { position: relative; min-width: 0; }
    .eyebrow { color: #dabe7d; font-size: 10px; letter-spacing: 3px; }
    .title { margin: 7px 0 8px; font-size: 29px; font-weight: 500; letter-spacing: 5px; }
    .player { color: #d1dcd2; font-size: 12px; letter-spacing: 1px; overflow-wrap: anywhere; }
    .diamond { display: inline-block; width: 5px; height: 5px; margin-right: 10px;
      background: #dabe7d; transform: rotate(45deg); vertical-align: 2px; }
    .spark { position: absolute; left: var(--x); top: var(--y); width: 2px; height: 2px;
      background: #ffe7ab; box-shadow: 0 0 7px #ebc76f; border-radius: 50%; opacity: 0;
      animation: spark 1900ms var(--delay) ease-out both; }
    @keyframes arrival { 0% { opacity: 0; transform: translateY(14px) scale(.97); }
      14%, 80% { opacity: 1; transform: translateY(0) scale(1); }
      100% { opacity: 0; transform: translateY(-8px) scale(1); } }
    @keyframes glint { from { transform: translateX(-45%); } to { transform: translateX(45%); } }
    @keyframes spark { 0% { opacity: 0; transform: translateY(12px); }
      20% { opacity: .7; } 100% { opacity: 0; transform: translateY(-20px); } }
    @media (max-width: 480px) {
      :host { inset: 17% 12px auto; }
      .card { min-height: 138px; gap: 18px; padding: 24px 20px; }
      .score { min-width: 110px; padding-right: 18px; } .number { font-size: 62px; }
      .title { font-size: 23px; letter-spacing: 2px; }
      .eyebrow { font-size: 8px; letter-spacing: 2px; }
    }
    @media (prefers-reduced-motion: reduce) {
      .card { animation-name: quiet; } .spark, .glow { display: none; }
      @keyframes quiet { 0%, 100% { opacity: 0; } 10%, 85% { opacity: 1; } }
    }
  `;

  function create({ document, window, host = document.body }) {
    let overlay = null;
    let timer = null;
    let destroyed = false;

    function clear() {
      if (timer !== null) window.clearTimeout(timer);
      timer = null;
      if (overlay) overlay.remove();
      overlay = null;
    }

    function show({ playerLabel, breakScore }) {
      if (destroyed) return;
      clear();
      overlay = document.createElement('div');
      overlay.dataset.pcolCelebration = '';
      const shadow = overlay.attachShadow({ mode: 'open' });
      const style = document.createElement('style');
      style.textContent = STYLE;
      const card = document.createElement('section');
      card.className = 'card';
      card.setAttribute('role', 'status');
      card.setAttribute('aria-live', 'polite');
      card.innerHTML = `<div class="glow" aria-hidden="true"></div>
        <div class="score"><span class="number"></span><span class="score-label">单杆得分</span></div>
        <div class="words"><div class="eyebrow"><span class="diamond" aria-hidden="true"></span>CENTURY BREAK</div>
          <div class="title">单杆破百</div><div class="player"></div></div>`;
      card.querySelector('.number').textContent = String(breakScore);
      card.querySelector('.player').textContent = playerLabel;
      for (let i = 0; i < 10; i++) {
        const spark = document.createElement('i');
        spark.className = 'spark';
        spark.setAttribute('aria-hidden', 'true');
        spark.style.cssText = `--x:${9 + i * 9}%;--y:${20 + (i * 23) % 67}%;--delay:${160 + (i * 137) % 900}ms`;
        card.append(spark);
      }
      shadow.append(style, card);
      host.append(overlay);
      timer = window.setTimeout(clear, DURATION);
    }

    function destroy() {
      clear();
      destroyed = true;
    }

    return { show, clear, destroy };
  }

  return { create };
})();

module.exports = PCOLCelebration;

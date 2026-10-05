const PCOLCelebration = (() => {
  'use strict';
  const DURATION = 3200;
  const TIERS = {
    century: { duration: DURATION, eyebrow: 'CENTURY BREAK', title: '单杆破百', sparks: 10 },
    maximum: { duration: 4600, eyebrow: 'MAXIMUM BREAK', title: '完美满分', sparks: 24 },
    ultimate: { duration: 6000, eyebrow: 'ULTIMATE BREAK', title: '极限满分', sparks: 40 }
  };
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
    .stage { position: relative; display: flex; justify-content: center; isolation: isolate;
      width: min(660px, 100%); animation: arrival var(--duration) cubic-bezier(.22,.8,.3,1) both; }
    .stage.ultimate { width: min(720px, 100%); }
    .stage .card { z-index: 1; width: 100%; min-height: 190px; padding: 30px 42px;
      gap: 34px; border-color: #edcf8cb5; border-radius: 5px; animation: none;
      background: radial-gradient(ellipse at 16% 70%, #54724d80, transparent 58%),
        linear-gradient(115deg, #15352bf5, #0b211cf7 65%, #223c2cf5);
      box-shadow: 0 20px 80px #0009, 0 0 44px #d6b55a25, inset 0 0 45px #dfc47f12; }
    .stage .card::before, .stage .card::after { left: 19px; right: 19px; height: 2px;
      background: linear-gradient(90deg, transparent, #b9914b 20%, #fff1c7 50%, #b9914b 80%, transparent); }
    .stage .score { z-index: 2; min-width: 220px; padding-right: 34px; }
    .stage .number { position: relative; font-size: 100px; letter-spacing: -6px;
      color: #ffe5a0; background: linear-gradient(160deg, #fffae9 8%, #f2cb70 52%, #ffe8b0 77%, #aa7835);
      background-clip: text; -webkit-background-clip: text; -webkit-text-fill-color: transparent;
      text-shadow: none; filter: drop-shadow(0 0 16px #eac36a50); }
    .stage .score-label { position: relative; margin-top: 15px; color: #e5ce97; }
    .stage .words { z-index: 2; }
    .stage .eyebrow { color: #e7cd93; letter-spacing: 3px; }
    .stage .title { color: #fff1d0; font-size: 34px; letter-spacing: 6px; }
    .stage .glow::before { background: linear-gradient(110deg, transparent 38%, #fff3be30 49%, transparent 60%);
      animation: glint 2100ms 300ms ease-out both; }
    .crest { position: absolute; width: 204px; height: 224px;
      left: calc(50% - 17px); top: 50%; transform: translate(-50%, -50%);
      color: #e6c67f; opacity: .66; pointer-events: none; }
    .crest svg { width: 100%; height: 100%; overflow: visible; }
    .effects { position: absolute; inset: 0; z-index: 0; pointer-events: none; }
    .aura { position: absolute; inset: -140px -110px;
      background: radial-gradient(ellipse, #e6c76722, transparent 62%);
      animation: aura 2600ms 150ms ease-out both; }
    .rays { position: absolute; width: 600px; height: 600px; left: 50%; top: 50%;
      background: repeating-conic-gradient(from 6deg, transparent 0deg 16deg, #f3d9893d 18deg, transparent 20deg 30deg);
      mask-image: radial-gradient(circle, transparent 15%, #000 33%, transparent 68%);
      animation: radiance 4000ms ease-out both; }
    .stage .spark { width: 3px; height: 3px; background: #ffe7a5; box-shadow: 0 0 9px #efc768;
      animation: drift 2900ms var(--delay) ease-out both; }
    .stage .spark:nth-child(3n) { width: 4px; height: 7px; border-radius: 1px; }
    .burst { position: absolute; left: var(--x); top: var(--y); width: 1px; height: 1px; }
    .burst i { position: absolute; width: 2px; height: 7px; border-radius: 2px;
      background: #fff0bc; box-shadow: 0 0 9px #f3cb75; opacity: 0;
      animation: firework 1700ms var(--delay) cubic-bezier(.12,.62,.26,1) both; }
    .ultimate .card { min-height: 218px; padding: 36px 46px; border-color: #f3dfb3;
      background: radial-gradient(ellipse at 8% 70%, #446d6180, transparent 57%),
        radial-gradient(ellipse at 100% 10%, #ae91542b, transparent 60%),
        linear-gradient(115deg, #15372ff7, #0c2220fa 65%, #213c30f7);
      box-shadow: 0 24px 90px #0009, 0 0 70px #e5c76b38, inset 0 0 70px #bceee212; }
    .ultimate .score { min-width: 245px; }
    .ultimate .number { font-size: 114px; background-image: linear-gradient(155deg, #fffcef 12%, #ecd194 40%, #d7f5f0 60%, #ffe4a6 82%);
      filter: drop-shadow(0 0 20px #f0d89b70); }
    .ultimate .crest { width: 226px; height: 250px; color: #f2dca2; opacity: .8; }
    .ultimate .title { font-size: 38px; }
    .ultimate .eyebrow { color: #d8efdf; }
    .ultimate .diamond { background: #d6f4ea; box-shadow: 0 0 8px #b9eedc80; }
    .ultimate .aura { background: radial-gradient(ellipse at 32% 50%, #dfbc713d, transparent 57%),
      radial-gradient(ellipse at 76% 40%, #a0e5e02b, transparent 60%); animation-duration: 4200ms; }
    .ultimate .rays { width: 760px; height: 760px; opacity: .85; animation-duration: 5600ms; }
    .halo { position: absolute; left: 50%; top: 50%; width: 105%; height: 172%; border-radius: 50%;
      border: 1px solid #ebce8b65; box-shadow: 0 0 14px #d8b4681f, inset 0 0 14px #d8b4681f;
      transform: translate(-50%, -50%) rotate(-12deg); animation: orbit 4800ms ease-out both; }
    .halo.second { width: 98%; height: 205%; border-color: #bdece55c;
      transform: translate(-50%, -50%) rotate(13deg); animation-delay: 350ms; }
    .ultimate .spark:nth-child(even), .ultimate .burst:nth-child(even) i {
      background: #d3f8ef; box-shadow: 0 0 10px #a6e9de; }
    @keyframes aura { 0% { opacity: 0; transform: scale(.6); }
      28%, 78% { opacity: 1; } 100% { opacity: .4; transform: scale(1.15); } }
    @keyframes radiance { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(-10deg) scale(.5); }
      20%, 75% { opacity: 1; } 100% { opacity: 0; transform: translate(-50%, -50%) rotate(8deg) scale(1.08); } }
    @keyframes drift { 0% { opacity: 0; transform: translate(0, 18px) rotate(0deg); }
      15% { opacity: .9; } 100% { opacity: 0; transform: translate(var(--drift), -65px) rotate(120deg); } }
    @keyframes firework { 0% { opacity: 0; transform: rotate(var(--angle)) translateY(8px) scale(.25); }
      12% { opacity: 1; } 100% { opacity: 0; transform: rotate(var(--angle)) translateY(var(--reach)) scale(.4); } }
    @keyframes orbit { 0% { opacity: 0; scale: .78; } 22%, 72% { opacity: 1; }
      100% { opacity: 0; scale: 1.09; } }
    @media (max-width: 480px) {
      :host { inset: 17% 12px auto; }
      .card { min-height: 138px; gap: 18px; padding: 24px 20px; }
      .score { min-width: 110px; padding-right: 18px; } .number { font-size: 62px; }
      .title { font-size: 23px; letter-spacing: 2px; }
      .eyebrow { font-size: 8px; letter-spacing: 2px; }
      .stage .card { min-height: 164px; padding: 24px 18px; gap: 18px; }
      .stage .score { min-width: 145px; padding-right: 18px; }
      .stage .number { font-size: 76px; letter-spacing: -4px; }
      .stage .title { font-size: 25px; letter-spacing: 3px; }
      .stage .eyebrow { font-size: 8px; letter-spacing: 2px; }
      .stage .crest { left: calc(50% - 9px); width: 150px; height: 178px; }
      .ultimate .card { min-height: 178px; }
      .ultimate .number { font-size: 84px; }
      .ultimate .crest { width: 162px; height: 190px; }
      .rays, .ultimate .rays { width: 480px; height: 480px; }
      .halo { width: 112%; height: 140%; }
      .halo.second { width: 106%; height: 165%; }
    }
    @media (prefers-reduced-motion: reduce) {
      .card, .stage { animation-name: quiet; } .stage .card { animation: none; }
      .spark, .glow, .effects { display: none; }
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
      const tierName = breakScore === 155 ? 'ultimate' : breakScore === 147 ? 'maximum' : 'century';
      const tier = TIERS[tierName];
      overlay = document.createElement('div');
      overlay.dataset.pcolCelebration = tierName;
      const shadow = overlay.attachShadow({ mode: 'open' });
      const style = document.createElement('style');
      style.textContent = STYLE;
      const card = document.createElement('section');
      card.className = 'card';
      card.setAttribute('role', 'status');
      card.setAttribute('aria-live', 'polite');
      card.innerHTML = `<div class="glow" aria-hidden="true"></div>
        <div class="score"><span class="number"></span><span class="score-label">单杆得分</span></div>
        <div class="words"><div class="eyebrow"><span class="diamond" aria-hidden="true"></span>${tier.eyebrow}</div>
          <div class="title">${tier.title}</div><div class="player"></div></div>`;
      card.querySelector('.number').textContent = String(breakScore);
      card.querySelector('.player').textContent = playerLabel;
      for (let i = 0; i < tier.sparks; i++) {
        const spark = document.createElement('i');
        spark.className = 'spark';
        spark.setAttribute('aria-hidden', 'true');
        spark.style.cssText = tierName === 'century'
          ? `--x:${9 + i * 9}%;--y:${20 + (i * 23) % 67}%;--delay:${160 + (i * 137) % 900}ms`
          : `--x:${(i * 47) % 101}%;--y:${10 + (i * 31) % 92}%;--drift:${(i % 5 - 2) * 18}px;--delay:${250 + (i * 179) % (tier.duration - 3000)}ms`;
        card.append(spark);
      }
      shadow.append(style);
      if (tierName === 'century') shadow.append(card);
      else {
        const stage = document.createElement('div');
        stage.className = `stage ${tierName}`;
        stage.style.cssText = `--duration:${tier.duration}ms`;
        const effects = document.createElement('div');
        effects.className = 'effects';
        effects.setAttribute('aria-hidden', 'true');
        effects.innerHTML = `<div class="aura"></div><div class="rays"></div>${tierName === 'ultimate'
          ? '<div class="halo"></div><div class="halo second"></div>' : ''}`;
        const bursts = tierName === 'ultimate'
          ? [[8, -12, 350], [92, -18, 1000], [24, -25, 2100], [76, 104, 2800]]
          : [[12, -10, 600], [88, -10, 900]];
        for (const [x, y, delay] of bursts) {
          const burst = document.createElement('div');
          burst.className = 'burst';
          burst.style.cssText = `--x:${x}%;--y:${y}%;--delay:${delay}ms`;
          for (let i = 0; i < 12; i++) {
            const ray = document.createElement('i');
            ray.style.cssText = `--angle:${i * 30}deg;--reach:${tierName === 'ultimate' ? 105 : 75}px`;
            burst.append(ray);
          }
          effects.append(burst);
        }
        const crest = document.createElement('div');
        crest.className = 'crest';
        crest.setAttribute('aria-hidden', 'true');
        const leaves = [[49, 53, -38], [38, 77, -52], [35, 102, -66], [42, 127, -78],
          [56, 151, -92], [74, 171, -105]].map(([x, y, angle]) =>
          `<ellipse cx="${x}" cy="${y}" rx="5" ry="12" transform="rotate(${angle} ${x} ${y})"/>`).join('');
        crest.innerHTML = `<svg viewBox="0 0 200 220" aria-hidden="true"><g fill="none" stroke="currentColor" stroke-width="1.3">
          <path d="M95 193C45 170 18 105 51 38M105 193C155 170 182 105 149 38"/>
          <path d="M83 23L78 10L92 17L100 5L108 17L122 10L117 23ZM83 28H117"/>
          </g><g fill="currentColor">${leaves}<g transform="translate(200 0) scale(-1 1)">${leaves}</g></g>
          <path d="M90 199L100 191L110 199L100 207Z" fill="currentColor"/></svg>`;
        card.querySelector('.score').append(crest);
        stage.append(effects, card);
        shadow.append(stage);
      }
      host.append(overlay);
      timer = window.setTimeout(clear, tier.duration);
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

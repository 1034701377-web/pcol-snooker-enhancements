const assert = require('node:assert/strict');
const test = require('node:test');
const PCOLCelebration = require('../src/celebration');

function environment(t) {
  t.mock.timers.enable({ apis: ['setTimeout'] });
  class Element {
    constructor() { this.children = []; this.dataset = {}; this.style = {}; this.fields = new Map(); }
    append(...children) { children.forEach(child => { child.parent = this; this.children.push(child); }); }
    remove() { this.parent.children = this.parent.children.filter(child => child !== this); }
    attachShadow() { this.shadowRoot = new Element(); return this.shadowRoot; }
    setAttribute() {}
    querySelector(selector) {
      if (!this.fields.has(selector)) this.fields.set(selector, new Element());
      return this.fields.get(selector);
    }
  }
  const document = { body: new Element(), createElement: () => new Element() };
  return { document, window: { setTimeout, clearTimeout } };
}

test('celebration retires after its short display and can show again', t => {
  const env = environment(t);
  const celebration = PCOLCelebration.create(env);
  celebration.show({ playerLabel: '玩家 1', breakScore: 101 });
  assert.equal(env.document.body.children.length, 1);
  t.mock.timers.tick(3100);
  assert.equal(env.document.body.children.length, 1);
  t.mock.timers.tick(100);
  assert.equal(env.document.body.children.length, 0);
  celebration.show({ playerLabel: '玩家 2', breakScore: 105 });
  assert.equal(env.document.body.children.length, 1);
});

test('a second celebration replaces the first and restarts its own display time', t => {
  const env = environment(t);
  const celebration = PCOLCelebration.create(env);
  celebration.show({ playerLabel: '玩家 1', breakScore: 100 });
  t.mock.timers.tick(2000);
  celebration.show({ playerLabel: '玩家 2', breakScore: 102 });
  assert.equal(env.document.body.children.length, 1);
  t.mock.timers.tick(1200);
  assert.equal(env.document.body.children.length, 1);
  t.mock.timers.tick(2000);
  assert.equal(env.document.body.children.length, 0);
});

test('clear cancels a pending display, and destroy prevents future displays', t => {
  const env = environment(t);
  const celebration = PCOLCelebration.create(env);
  celebration.show({ playerLabel: '玩家 1', breakScore: 100 });
  celebration.clear();
  assert.equal(env.document.body.children.length, 0);
  t.mock.timers.tick(5000);
  celebration.show({ playerLabel: '玩家 1', breakScore: 107 });
  assert.equal(env.document.body.children.length, 1);
  celebration.destroy();
  celebration.show({ playerLabel: '玩家 2', breakScore: 101 });
  assert.equal(env.document.body.children.length, 0);
  t.mock.timers.tick(5000);
});

for (const [breakScore, tier, duration, title] of [
  [147, 'maximum', 4600, '完美满分'],
  [155, 'ultimate', 6000, '极限满分']
]) {
  test(`${breakScore} shows its own celebration and retires after ${duration}ms`, t => {
    const env = environment(t);
    const celebration = PCOLCelebration.create(env);
    celebration.show({ playerLabel: '玩家 1', breakScore });
    const overlay = env.document.body.children[0];
    assert.equal(overlay.dataset.pcolCelebration, tier);
    const stage = overlay.shadowRoot.children[1];
    assert.equal(stage.className, `stage ${tier}`);
    const card = stage.children[1];
    assert.equal(card.querySelector('.number').textContent, String(breakScore));
    assert.ok(card.innerHTML.includes(title));
    t.mock.timers.tick(duration - 1);
    assert.equal(env.document.body.children.length, 1);
    t.mock.timers.tick(1);
    assert.equal(env.document.body.children.length, 0);
  });
}

test('upgrading a maximum to 155 replaces all effects and cancels the earlier timer', t => {
  const env = environment(t);
  const celebration = PCOLCelebration.create(env);
  celebration.show({ playerLabel: '玩家 1', breakScore: 147 });
  t.mock.timers.tick(1000);
  celebration.show({ playerLabel: '玩家 1', breakScore: 155 });
  t.mock.timers.tick(3600);
  assert.equal(env.document.body.children.length, 1);
  assert.equal(env.document.body.children[0].dataset.pcolCelebration, 'ultimate');
  celebration.destroy();
  t.mock.timers.tick(2400);
  assert.equal(env.document.body.children.length, 0);
});

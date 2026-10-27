// One local browser pass; use an already installed Playwright and browser, never download them.
const fs = require('node:fs');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require('playwright');

const personal = path.resolve(__dirname, '../..');
const output = path.join(personal, 'evidence/metrics');
const checkOutput = path.join(output, 'local-checks/history');
fs.mkdirSync(checkOutput, { recursive: true });
const presentation = path.join(personal, 'presentation-history-2026-10-25.html');
const checks = { checked_at: new Date().toISOString(), browser: 'not_started', checks: [], errors: [] };
function expect(name, actual) {
  checks.checks.push({ name, passed: Boolean(actual) });
  if (!actual) throw new Error(name);
}
(async () => {
  let browser;
  try {
    browser = await chromium.launch({ headless: true });
    checks.browser = browser.version();
    const page = await browser.newPage({ viewport: { width: 1280, height: 1100 } });
    page.on('pageerror', error => checks.errors.push(String(error)));
    page.on('console', message => { if (message.type() === 'error') checks.errors.push(message.text()); });
    await page.goto(pathToFileURL(presentation).href);
    const total = await page.locator('.slide').count();
    expect('sixteen main slides', await page.locator('.slide:not(.appendix)').count() === 16);
    expect('six appendix slides', await page.locator('.slide.appendix').count() === 6);
    expect('appendix follows main narrative', await page.locator('.slide').evaluateAll(nodes =>
      nodes.every((node, i) => node.classList.contains('appendix') === (i >= 16))));
    expect('research question arrives at slide three', await page.locator('.slide').nth(2).getAttribute('id') === 'search-question');
    expect('opens at first slide', await page.locator('#position').textContent() === `1 / ${total}`);
    await page.locator('#next').click();
    expect('next button', await page.locator('#position').textContent() === `2 / ${total}`);
    await page.locator('#prev').click();
    expect('previous button', await page.locator('#position').textContent() === `1 / ${total}`);
    await page.keyboard.press('End');
    expect('End key', await page.locator('#position').textContent() === `${total} / ${total}`);
    await page.keyboard.press('Home');
    expect('Home key', await page.locator('#position').textContent() === `1 / ${total}`);
    await page.keyboard.press('ArrowRight');
    expect('arrow navigation', await page.locator('#position').textContent() === `2 / ${total}`);
    await page.locator('#main-end').click();
    expect('main conclusion shortcut', await page.locator('#next-study').isVisible());
    await page.locator('#appendix').click();
    expect('appendix shortcut', await page.locator('#appendix-start').isVisible());
    await page.locator('#overview').click();
    expect('overview shows all slides', await page.locator('.slide:visible').count() === total);
    await page.emulateMedia({ media: 'print' });
    expect('print displays all slides', await page.locator('.slide:visible').count() === total);
    await page.emulateMedia({ media: 'screen' });
    await page.locator('#overview').click();
    async function showSlide(number) {
      await page.keyboard.press('Home');
      for (let i = 1; i < number; i++) await page.keyboard.press('ArrowRight');
      expect(`slide ${number} navigation`, await page.locator('#position').textContent() === `${number} / ${total}`);
    }
    async function showId(id) {
      const index = await page.locator('.slide').evaluateAll((nodes, id) => nodes.findIndex(node => node.id === id), id);
      expect(`slide id exists ${id}`, index >= 0);
      await showSlide(index + 1);
    }
    await showId('legacy-results');
    expect('legacy results visible', await page.locator('#legacy-results').isVisible());
    expect('all seven version rows', await page.locator('#legacy-results tbody tr').count() === 7);
    await showId('confirmation-results');
    expect('confirmation results visible', await page.locator('#confirmation-results').isVisible());
    expect('four confirmation conditions', await page.locator('#confirmation-results tbody tr').count() === 4);
    const session = path.join(output, 'agent/p11-20261017-ac-check4');
    const results = {};
    for (const id of ['a001', 'a002', 'a003', 'a004']) {
      const result = JSON.parse(fs.readFileSync(path.join(session, 'attempts', id, 'result.json'), 'utf8'));
      results[id] = result;
      expect(`${id} saved validation passed`, result.status === 'passed');
      const row = page.locator(`#confirmation-results [data-condition="${id}"]`);
      for (const field of ['heartbeat', 'proof_tokens']) {
        const shown = Number((await row.locator(`[data-field="${field}"]`).textContent()).replaceAll(',', ''));
        expect(`${id} ${field} matches raw result`, shown === result[field]);
      }
      const delta = await row.locator('[data-field="delta"]').textContent();
      expect(`${id} B-relative decrease`, id === 'a001' ? delta === '—' :
        Number(delta.replaceAll(',', '')) === results.a001.heartbeat - result.heartbeat);
    }
    await showId('pilot-results');
    expect('three independent pilot strategies', await page.locator('#pilot-results tbody tr').count() === 3);
    for (const strategy of ['S1', 'S2', 'S3']) {
      const row = page.locator(`#pilot-results [data-strategy="${strategy}"]`);
      for (const repetition of [1, 2]) {
        const run = path.join(output, `structural-pilot-2026-10-25/P11-${strategy}/candidate-${repetition}`);
        const result = JSON.parse(fs.readFileSync(path.join(run, 'result.json'), 'utf8'));
        const review = JSON.parse(fs.readFileSync(path.join(run, 'review.json'), 'utf8'));
        expect(`${strategy}/${repetition} validation and axiom comparison`, result.status === 'passed' && review.status === 'passed' && review.added_axioms.length === 0);
        for (const field of ['heartbeat', 'proof_tokens']) {
          const shown = Number((await row.locator(`[data-field="${field}"]`).textContent()).replaceAll(',', ''));
          expect(`${strategy}/${repetition} ${field} matches raw result`, shown === result[field]);
        }
        expect(`${strategy}/${repetition} improvement direction`, review.improved === (strategy !== 'S3'));
      }
    }
    await page.screenshot({ path: path.join(checkOutput, 'presentation-pilot.png'), fullPage: true });
    await showId('performance-results');
    expect('four P8 performance conditions', await page.locator('#performance-results tbody tr').count() === 4);
    for (const name of ['reference', 'start', 'c001', 'c002']) {
      const row = page.locator(`#performance-results [data-search="${name}"]`);
      for (const repetition of [1, 2, 3]) {
        const run = path.join(output, `performance-search-2026-10-25/P8/runs/${name}-${repetition}`);
        const result = JSON.parse(fs.readFileSync(path.join(run, 'raw/result.json'), 'utf8'));
        const review = JSON.parse(fs.readFileSync(path.join(run, 'review.json'), 'utf8'));
        expect(`P8 ${name}/${repetition} raw and audited pass`, result.status === 'passed' && review.status === 'passed');
        expect(`P8 ${name}/${repetition} no new axioms`, name === 'reference' || result.axioms.length === 0);
        for (const field of ['heartbeat', 'proof_tokens']) {
          const shown = Number((await row.locator(`[data-field="${field}"]`).textContent()).replaceAll(',', ''));
          expect(`P8 ${name}/${repetition} ${field} matches raw result`, shown === result[field]);
        }
      }
    }
    await page.screenshot({ path: path.join(checkOutput, 'presentation-performance.png'), fullPage: true });
    await showId('confirmation-results');
    expect('C decrease without A is 786', results.a001.heartbeat - results.a003.heartbeat === 786);
    expect('C decrease after A is 786', results.a002.heartbeat - results.a004.heartbeat === 786);
    await page.screenshot({ path: path.join(checkOutput, 'presentation-confirmation.png'), fullPage: true });
    for (const width of [1280, 400]) {
      await page.setViewportSize({ width, height: 1100 });
      for (const colorScheme of ['light', 'dark']) {
        await page.emulateMedia({ colorScheme });
        for (let number = 1; number <= total; number++) {
          await showSlide(number);
          expect(`no page overflow slide ${number} ${width}/${colorScheme}`,
            await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
        }
        await page.locator('#overview').click();
        expect(`overview no page overflow ${width}/${colorScheme}`,
          await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
        await page.locator('#overview').click();
        const ink = await page.evaluate(() => getComputedStyle(document.body).color);
        expect(`theme ${width}/${colorScheme}`, ink === (colorScheme === 'dark' ? 'rgb(227, 235, 245)' : 'rgb(24, 43, 64)'));
      }
    }
    await showId('confirmation-results');
    await page.screenshot({ path: path.join(checkOutput, 'presentation-confirmation-mobile-dark.png'), fullPage: true });
    await page.evaluate(() => document.documentElement.setAttribute('data-theme', 'light'));
    expect('explicit light overrides dark OS', await page.evaluate(() => getComputedStyle(document.body).color === 'rgb(24, 43, 64)'));
    const links = await page.locator('a[href]').evaluateAll(nodes => nodes.map(node => node.getAttribute('href')));
    for (const link of links) {
      if (/^(https?:|#)/.test(link)) continue;
      expect(`local link ${link}`, fs.existsSync(path.resolve(personal, decodeURIComponent(link.split('#')[0]))));
    }
    expect('no browser errors', checks.errors.length === 0);
    checks.status = 'passed';
  } catch (error) {
    checks.status = 'failed';
    checks.errors.push(String(error));
    process.exitCode = 1;
  } finally {
    if (browser) await browser.close();
    fs.writeFileSync(path.join(checkOutput, 'document-checks.json'), JSON.stringify(checks, null, 2) + '\n');
    console.log(JSON.stringify(checks, null, 2));
  }
})();

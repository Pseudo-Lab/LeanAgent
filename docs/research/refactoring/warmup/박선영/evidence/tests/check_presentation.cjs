// Week 4 deck: use installed Playwright and browser; never download them.
const fs = require('node:fs');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require('playwright');
const personal = path.resolve(__dirname, '../..');
const output = path.join(personal, 'evidence/metrics');
const checkOutput = path.join(output, 'local-checks');
fs.mkdirSync(checkOutput, { recursive: true });
const checks = { checked_at: new Date().toISOString(), checks: [], errors: [] };
function expect(name, actual) {
  checks.checks.push({ name, passed: Boolean(actual) });
  if (!actual) throw new Error(name);
}
function saved(problem, name, repetition) {
  const run = path.join(output, `performance-search-2026-10-25/P${problem}/runs/${name}-${repetition}`);
  const result = JSON.parse(fs.readFileSync(path.join(run, 'raw/result.json'), 'utf8'));
  const review = JSON.parse(fs.readFileSync(path.join(run, 'review.json'), 'utf8'));
  expect(`P${problem} ${name}/${repetition} raw and audited pass`, result.status === 'passed' && review.status === 'passed');
  return result;
}
(async () => {
  let browser;
  try {
    browser = await chromium.launch({ headless: true });
    checks.browser = browser.version();
    const page = await browser.newPage({ viewport: { width: 1280, height: 1000 } });
    page.on('pageerror', error => checks.errors.push(String(error)));
    page.on('console', message => { if (message.type() === 'error') checks.errors.push(message.text()); });
    await page.goto(pathToFileURL(path.join(personal, 'presentation.html')).href);
    const total = await page.locator('.slide').count();
    expect('nine Week4-only slides', total === 9);
    expect('no appended historical slides', await page.locator('.appendix').count() === 0);
    expect('one speaker note per slide', await page.locator('.slide details').count() === total);
    const ids = await page.locator('[id]').evaluateAll(nodes => nodes.map(n => n.id));
    expect('unique HTML ids', new Set(ids).size === ids.length);
    async function show(number) {
      await page.keyboard.press('Home');
      for (let i = 1; i < number; i++) await page.keyboard.press('ArrowRight');
      expect(`navigate ${number}`, await page.locator('#position').textContent() === `${number} / ${total}`);
    }
    await page.locator('#next').click();
    expect('next button', await page.locator('#position').textContent() === '2 / 9');
    await page.locator('#prev').click();
    expect('previous button', await page.locator('#position').textContent() === '1 / 9');
    await page.locator('#main-end').click();
    expect('conclusion shortcut', await page.locator('#next-study').isVisible());
    await page.keyboard.press('Home');
    await page.keyboard.press('n');
    expect('notes keyboard opens', await page.locator('.slide.active details').evaluate(n => n.open));
    await page.locator('#notes').click();
    expect('notes button closes', await page.locator('.slide.active details').evaluate(n => !n.open));
    await show(2);
    for (const strategy of ['S1', 'S2', 'S3']) {
      const row = page.locator(`[data-strategy="${strategy}"]`);
      for (const repetition of [1, 2]) {
        const run = path.join(output, `structural-pilot-2026-10-25/P11-${strategy}/candidate-${repetition}`);
        const raw = JSON.parse(fs.readFileSync(path.join(run, 'result.json'), 'utf8'));
        for (const field of ['heartbeat', 'proof_tokens']) {
          expect(`${strategy}/${repetition} ${field}`, Number((await row.locator(`[data-field="${field}"]`).textContent()).replaceAll(',', '')) === raw[field]);
        }
      }
    }
    await show(5);
    for (const name of ['start', 'c006', 'c004', 'c001']) {
      for (const repetition of [1, 2, 3]) {
        const result = saved(8, name, repetition);
        expect(`P8 control ${name}/${repetition} matches`, Number((await page.locator(`[data-control="${name}"]`).textContent()).replaceAll(',', '')) === result.heartbeat);
      }
    }
    await show(7);
    for (const [problem, candidate] of [[8, 'c003'], [11, 'c002']]) {
      const row = page.locator(`[data-problem="${problem}"]`);
      const shown = async field => Number((await row.locator(`[data-field="${field}"]`).textContent()).replaceAll(',', '').replace('%', ''));
      for (const repetition of [1, 2, 3]) {
        const result = saved(problem, candidate, repetition);
        const start = saved(problem, 'start', repetition);
        const reference = saved(problem, 'reference', repetition);
        expect(`P${problem}/${repetition} axiom subset`, result.axioms.every(a => reference.axioms.includes(a)));
        expect(`P${problem}/${repetition} heartbeat`, await shown('heartbeat') === result.heartbeat);
        expect(`P${problem}/${repetition} tokens`, await shown('proof_tokens') === result.proof_tokens);
        expect(`P${problem}/${repetition} starting heartbeat`, await shown('start-hb') === start.heartbeat);
        expect(`P${problem}/${repetition} starting tokens`, await shown('start-tokens') === start.proof_tokens);
        expect(`P${problem}/${repetition} HB percentage`, await shown('hb-reduction') === Number((100 * (1 - result.heartbeat / start.heartbeat)).toFixed(2)));
        expect(`P${problem}/${repetition} token percentage`, await shown('token-reduction') === Number((100 * (1 - result.proof_tokens / start.proof_tokens)).toFixed(2)));
      }
    }
    await page.screenshot({ path: path.join(checkOutput, 'week4-results.png'), fullPage: true });
    await page.locator('#overview').click();
    expect('overview shows all slides', await page.locator('.slide:visible').count() === total);
    await page.locator('#overview').click();
    await page.emulateMedia({ media: 'print' });
    expect('print shows all slides', await page.locator('.slide:visible').count() === total);
    expect('print hides notes', await page.locator('details:visible').count() === 0);
    await page.emulateMedia({ media: 'screen' });
    for (const width of [1280, 400]) {
      await page.setViewportSize({ width, height: 1000 });
      for (const colorScheme of ['light', 'dark']) {
        await page.emulateMedia({ colorScheme });
        for (let number = 1; number <= total; number++) {
          await show(number);
          expect(`no horizontal overflow ${number} ${width}/${colorScheme}`, await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
          await page.locator('#notes').click();
          expect(`notes no horizontal overflow ${number} ${width}/${colorScheme}`, await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
          await page.locator('#notes').click();
          if (width === 1280) {
            expect(`desktop slide fits ${number}/${colorScheme}`, await page.locator('.slide.active').evaluate(n => n.getBoundingClientRect().height <= 850));
          }
        }
        const ink = await page.evaluate(() => getComputedStyle(document.body).color);
        expect(`theme ${width}/${colorScheme}`, ink === (colorScheme === 'dark' ? 'rgb(227, 235, 245)' : 'rgb(24, 43, 64)'));
        await page.locator('#overview').click();
        expect(`overview no overflow ${width}/${colorScheme}`, await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
        await page.locator('#overview').click();
      }
    }
    await show(7);
    await page.screenshot({ path: path.join(checkOutput, 'week4-results-mobile-dark.png'), fullPage: true });
    await page.evaluate(() => document.documentElement.setAttribute('data-theme', 'light'));
    expect('explicit light overrides dark OS', await page.evaluate(() => getComputedStyle(document.body).color === 'rgb(24, 43, 64)'));
    for (const link of await page.locator('a[href]').evaluateAll(nodes => nodes.map(n => n.getAttribute('href')))) {
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

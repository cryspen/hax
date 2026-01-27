import { test, expect, request, BrowserContext, Page } from '@playwright/test';
import { CrawlPage } from '../global-setup';
import fs from 'fs';

const cssEscape = (s: string) =>
    s.replace(/^[0-9-]|[^a-zA-Z0-9_-]/g, (ch, idx) => {
        const code = ch.codePointAt(0)!.toString(16).toUpperCase();
        return `\\${code} `;
    });

const PAGES = JSON.parse(fs.readFileSync('generated.json', 'utf-8')) as CrawlPage[];


async function tryNavigateTo(page: Page, url: string) {
    const response = await page.request.get(url, {
        headers: {
            accept: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        }
    });
    const status = response.status();
    const contentType = response.headers()['content-type'] || '';

    if (!contentType.includes('text/html'))
        return { status, html: false };

    try {
        await page.goto(url, { waitUntil: 'domcontentloaded' });
        return { status, html: true };
    } catch (e) {
        return { status, html: false };
    }
}

// test.describe('Documentation consistency checks', () => {
let run_tests = () => {
    let tried = new Set();

    let links_origins: Map<string, Set<string>> = new Map();
    let links: Set<string> = new Set();
    for (let page of PAGES) {
        for (let link of page.links) {
            let absolute_link = (new URL(link, page.url)).toString();
            links.add(absolute_link);
            links_origins.has(absolute_link) || links_origins.set(absolute_link, new Set());
            links_origins.get(absolute_link)!.add(page.url);
        }
    }


    for (let link of links) {
        if (link.includes("hax-playground.cryspen.com/") || link.includes("#__codelineno"))
            continue;
        test('Check if link is live: ' + link, (async ({ page, baseURL }, testInfo) => {
            await testInfo.attach('Parent pages', {
                body: [...(links_origins.get(link) || new Set())].join('\n'),
                contentType: 'text/plain',
            });
            let other_page = await page.context().newPage();
            let { status, html } = await tryNavigateTo(other_page, link.toString());
            let anti_bot_codes = [401, 403, 429, 451, 999].includes(status);
            expect(anti_bot_codes || (status >= 200 && status < 300)).toBeTruthy()

            let hash = (new URL(link)).hash?.replace(/^#/, '');
            if (hash && !link.includes(""))
                await test.step("Try detection of fragment `" + hash + '`', async () => {
                    let el = other_page.locator('[id="' + cssEscape(hash) + '"]');
                    if (await el.count() === 0)
                        console.warn('⚠️ Could not find anchor in a page ', link);
                });
        }));
    }

    for (let p of PAGES) {
        if (!p.has_playground)
            continue;
        test('Test playgrounds in `' + p.url + '`', async ({ page, baseURL }, testInfo) => {
            await page.goto(p.url, { waitUntil: 'domcontentloaded' });
            const playableLocators = page.locator('.playable:has(.md-hax-playground .fa-check)');
            const count = await playableLocators.count();

            for (let i = 0; i < count; i++) {
                await test.step(`Try playground #${i}`, async () => {
                    const playable = playableLocators.nth(i);
                    const contents = await playable.locator(".cm-content").first().innerText();
                    await testInfo.attach('Code snippet contents', {
                        body: contents,
                        contentType: 'text/plain',
                    });

                    const checkBtn = playable.locator('.md-hax-playground .fa-check');
                    await checkBtn.first().click();

                    let classes = '';
                    let hasSuccess = false;
                    let hasFailure = false;

                    for (let i = 0; i < 60; i++) {
                        classes = (await playable.getAttribute('class')) || '';
                        hasSuccess = classes.includes('state-success');
                        hasFailure = classes.includes('state-failure');
                        if (hasSuccess || hasFailure)
                            break;
                        await new Promise(r => setTimeout(r, 1000));
                    }

                    expect(hasSuccess || hasFailure, "At least class `state-success` or `state-failure` should have been attached; none detected.").toBeTruthy();

                    const expectFailure = classes.includes('expect-failure');

                    if (expectFailure) {
                        expect(hasFailure, '`.state-failure` should be set (the snippet is tagged with a class `expect-failure`), but `.state-success` was detected').toBeTruthy();
                    } else {
                        expect(hasSuccess, '`.state-success` should be set, but `.state-failure` was detected').toBeTruthy();
                    }
                });
            }
        });
    }
};

run_tests();

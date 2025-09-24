// Global setup: writes `generated.json`, the list of pages
import { BrowserContext, chromium, expect, FullConfig } from '@playwright/test';
import fs from 'fs';

export type CrawlPage = { url: string; has_playground: boolean, links: string[] };
const DOCS_HOST = 'localhost:8000';

const skip_url = (s: string) => s.includes("/livereload");

/// Run jobs in parallel.
/// `job` runs a new job, returns true if more jobs are to be run.
async function parallel(
    job: () => Promise<boolean>,
    maxJobs = 10
): Promise<void> {
    const workers: { promise?: Promise<void>, free: boolean }[] = (new Array(maxJobs)).fill(0).map(_ => ({ free: true }));

    let spawn = (self: { promise?: Promise<void>, free: boolean }) => {
        self.promise = (async () => { self.free = false; let cont = await job(); self.free = true; cont && control() })();
    };
    let control = () => workers.filter(w => w.free).forEach(spawn);
    control();

    let active_workers: Promise<void>[] = [];
    do {
        active_workers = workers.filter(w => !w.free).map(w => w.promise).filter(p => p !== undefined);
        await Promise.all(active_workers);
    } while (active_workers.length > 0)
}

/// Crawl the documentation
const crawl = async (baseURL: string, context: BrowserContext): Promise<CrawlPage[]> => {
    if (!baseURL) throw new Error('Base URL not configured.');

    const pages: CrawlPage[] = [];
    const visited = new Set<string>();
    const queue: string[] = [new URL('/', baseURL).toString()];

    await parallel(async () => {
        const url = queue.shift();
        if (url === undefined || visited.has(url))
            return false;
        visited.add(url);

        const page = await context.newPage();

        const res = await page.goto(url, { waitUntil: 'domcontentloaded' });
        await page.waitForLoadState('networkidle').catch(() => { });
        const status = res?.status() ?? 0;
        expect(status, `Failed to GET ${url}`).toBeGreaterThanOrEqual(200);
        expect(status, `Failed to GET ${url}`).toBeLessThan(400);

        const has_playground = (await page.content()).includes('md-hax-playground');
        const links = await page.$$eval('a[href]', as => as.map(a => (a as HTMLAnchorElement).getAttribute('href')!));

        pages.push({ url, has_playground, links });

        for (const href of links) {
            if (!href || href.startsWith('mailto:') || href.startsWith('tel:') || href.startsWith('javascript:')) continue;

            const absolute = new URL(href, url);
            const sameHost = absolute.host === DOCS_HOST;
            if (!sameHost) continue;
            absolute.hash = '';
            const absStr = absolute.toString();
            if (!visited.has(absStr) && !skip_url(absStr) && !queue.includes(absStr)) queue.push(absStr);
        }

        page.close();
        return true;
    });

    return pages;
}

async function globalSetup(config: FullConfig) {
    const browser = await chromium.launch();
    let PAGES = await crawl('http://localhost:8000', await browser.newContext());
    await browser.close();
    fs.writeFileSync('generated.json', JSON.stringify(PAGES, null, 2), 'utf-8');
}
export default globalSetup;

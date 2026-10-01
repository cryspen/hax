import { defineConfig } from '@playwright/test';

export default defineConfig({
    globalSetup: './global-setup.ts',
    timeout: 600_000,
    expect: { timeout: 300_000 },
    reporter: [['list']],
    workers: process.env.CI ? 8 : undefined,
    retries: process.env.CI ? 2 : 0,
    use: {
        baseURL: 'http://localhost:8000',
        serviceWorkers: 'block',
        trace: 'on-first-retry',
    },
    webServer: {
        command: 'nix run ../..#serve-docs',
        port: 8000,
        reuseExistingServer: !process.env.CI,
        timeout: 5 * 60 * 1000,
        stderr: 'ignore',
        stdout: 'ignore',
    }
});

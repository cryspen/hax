import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

// ─────────────────────────────────────────────────────────────────────────────
// VLQ / Source Map v3 decoder
// ─────────────────────────────────────────────────────────────────────────────

const BASE64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
const B64: Record<string, number> = {};
for (let i = 0; i < BASE64.length; i++) B64[BASE64[i]] = i;

function decodeVlq(s: string, pos: number): [number, number] {
    let result = 0, shift = 0;
    for (;;) {
        const digit = B64[s[pos++]];
        result |= (digit & 31) << shift;
        shift += 5;
        if (!(digit & 32)) { break; }
    }
    return [(result & 1) ? -(result >>> 1) : (result >>> 1), pos];
}

// ─────────────────────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────────────────────

interface Mapping {
    genLine: number;
    genCol: number;
    srcIdx: number;
    srcLine: number;
    srcCol: number;
}

interface SourceMapData {
    mappings: Mapping[];
    sources: string[];
    sourcesContent: (string | null)[];
    /** srcIdx → resolved absolute filesystem path */
    resolvedPaths: Map<number, string>;
}

// ─────────────────────────────────────────────────────────────────────────────
// Source map parsing
// ─────────────────────────────────────────────────────────────────────────────

function decodeSourceMap(mapFilePath: string): SourceMapData | null {
    let raw: { sources?: string[]; sourcesContent?: (string|null)[]; mappings?: string };
    try { raw = JSON.parse(fs.readFileSync(mapFilePath, 'utf8')); }
    catch { return null; }

    const sources: string[] = raw.sources ?? [];
    const sourcesContent: (string | null)[] = raw.sourcesContent ?? sources.map(() => null);
    const encoded: string = raw.mappings ?? '';
    const mappings: Mapping[] = [];

    let genLine = 0;
    let pGC = 0, pSI = 0, pSL = 0, pSC = 0;

    for (let i = 0; i < encoded.length;) {
        const ch = encoded[i];
        if (ch === ';') { genLine++; pGC = 0; i++; continue; }
        if (ch === ',') { i++; continue; }

        let dGC: number;
        [dGC, i] = decodeVlq(encoded, i);
        const genCol = pGC + dGC;
        pGC = genCol;

        if (i >= encoded.length || encoded[i] === ';' || encoded[i] === ',') { continue; }

        let dSI: number, dSL: number, dSC: number;
        [dSI, i] = decodeVlq(encoded, i);
        [dSL, i] = decodeVlq(encoded, i);
        [dSC, i] = decodeVlq(encoded, i);

        // optional name index
        if (i < encoded.length && encoded[i] !== ';' && encoded[i] !== ',') {
            [, i] = decodeVlq(encoded, i);
        }

        pSI += dSI; pSL += dSL; pSC += dSC;
        mappings.push({ genLine, genCol, srcIdx: pSI, srcLine: pSL, srcCol: pSC });
    }

    const resolvedPaths = resolveSources(sources, mapFilePath);
    return { mappings, sources, sourcesContent, resolvedPaths };
}

function normPath(p: string): string {
    try { return fs.realpathSync(p); } catch { return path.resolve(p); }
}

function resolveSources(sources: string[], mapFilePath: string): Map<number, string> {
    const resolved = new Map<number, string>();
    const mapDir = path.dirname(mapFilePath);

    for (let idx = 0; idx < sources.length; idx++) {
        const src = sources[idx];
        if (!src) { continue; }

        const tryAdd = (p: string) => {
            if (fs.existsSync(p)) { resolved.set(idx, normPath(p)); return true; }
            return false;
        };

        if (path.isAbsolute(src)) { tryAdd(src); continue; }

        // Workspace roots
        let found = false;
        for (const folder of vscode.workspace.workspaceFolders ?? []) {
            if (tryAdd(path.join(folder.uri.fsPath, src))) { found = true; break; }
        }
        if (found) { continue; }

        // Walk up from map file
        let dir = mapDir;
        for (let depth = 0; depth < 12; depth++) {
            if (tryAdd(path.join(dir, src))) { break; }
            const parent = path.dirname(dir);
            if (parent === dir) { break; }
            dir = parent;
        }
    }
    return resolved;
}

// ─────────────────────────────────────────────────────────────────────────────
// Colour palette
// ─────────────────────────────────────────────────────────────────────────────

// 8-colour palette, legible on dark and light themes.
const PALETTE: Array<{ r: number; g: number; b: number }> = [
    { r: 224, g: 108, b: 117 }, // red
    { r: 229, g: 192, b: 123 }, // amber
    { r: 152, g: 195, b: 121 }, // green
    { r:  86, g: 182, b: 194 }, // cyan
    { r:  97, g: 175, b: 239 }, // blue
    { r: 198, g: 120, b: 221 }, // purple
    { r: 209, g: 154, b: 102 }, // orange
    { r: 171, g: 178, b: 191 }, // slate
];
const N = PALETTE.length;

function rgba(c: { r: number; g: number; b: number }, a: number): string {
    return `rgba(${c.r},${c.g},${c.b},${a})`;
}

function makeDecTypes(bgAlpha: number): {
    bg: vscode.TextEditorDecorationType[];
    active: vscode.TextEditorDecorationType[];
} {
    const bg: vscode.TextEditorDecorationType[] = [];
    const active: vscode.TextEditorDecorationType[] = [];
    for (const c of PALETTE) {
        bg.push(vscode.window.createTextEditorDecorationType({
            backgroundColor: rgba(c, bgAlpha),
            isWholeLine: true,
            overviewRulerColor: rgba(c, 0.6),
            overviewRulerLane: vscode.OverviewRulerLane.Left,
        }));
        active.push(vscode.window.createTextEditorDecorationType({
            backgroundColor: rgba(c, Math.min(1, bgAlpha * 2.8)),
            isWholeLine: true,
            border: `0 0 0 3px solid ${rgba(c, 0.9)}`,
            overviewRulerColor: rgba(c, 1.0),
            overviewRulerLane: vscode.OverviewRulerLane.Full,
        }));
    }
    return { bg, active };
}

// ─────────────────────────────────────────────────────────────────────────────
// Manager
// ─────────────────────────────────────────────────────────────────────────────

class HaxManager {
    private smCache = new Map<string, SourceMapData | null>();
    private colorMapCache = new Map<string, Map<number, number>>();
    /** rust absolute path → lean absolute paths that reference it */
    private rustToLean = new Map<string, Set<string>>();
    private decTypes: ReturnType<typeof makeDecTypes>;
    private readonly statusBar: vscode.StatusBarItem;
    private rainbowEnabled: boolean;

    constructor(private readonly ctx: vscode.ExtensionContext) {
        const cfg = vscode.workspace.getConfiguration('hax.sourcemap');
        this.rainbowEnabled = cfg.get<boolean>('rainbowOnOpen', true);
        this.decTypes = makeDecTypes(cfg.get<number>('rainbowOpacity', 0.07));

        this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
        this.statusBar.command = 'hax.jumpToSource';
        ctx.subscriptions.push(this.statusBar);

        ctx.subscriptions.push(vscode.workspace.onDidChangeConfiguration(e => {
            if (!e.affectsConfiguration('hax.sourcemap')) { return; }
            const newCfg = vscode.workspace.getConfiguration('hax.sourcemap');
            this.rainbowEnabled = newCfg.get<boolean>('rainbowOnOpen', true);
            // Dispose old decoration types and recreate with new opacity.
            for (const d of [...this.decTypes.bg, ...this.decTypes.active]) { d.dispose(); }
            this.decTypes = makeDecTypes(newCfg.get<number>('rainbowOpacity', 0.07));
            for (const editor of vscode.window.visibleTextEditors) { this.update(editor); }
        }));
    }

    // ── Source map access ────────────────────────────────────────────────────

    private loadSourceMap(leanPath: string): SourceMapData | null {
        if (this.smCache.has(leanPath)) { return this.smCache.get(leanPath)!; }
        const mapPath = leanPath + '.map';
        const sm = fs.existsSync(mapPath) ? decodeSourceMap(mapPath) : null;
        this.smCache.set(leanPath, sm);
        if (sm) {
            this.colorMapCache.set(leanPath, buildColorMap(sm));
            for (const [, resolved] of sm.resolvedPaths) {
                if (!this.rustToLean.has(resolved)) { this.rustToLean.set(resolved, new Set()); }
                this.rustToLean.get(resolved)!.add(leanPath);
            }
            // Update context key for rust files
            vscode.commands.executeCommand('setContext', 'hax.hasReverseMap',
                this.rustToLean.size > 0);
        }
        return sm;
    }

    private getColorMap(leanPath: string): Map<number, number> {
        if (this.colorMapCache.has(leanPath)) { return this.colorMapCache.get(leanPath)!; }
        const sm = this.loadSourceMap(leanPath);
        if (!sm) { return new Map(); }
        const cm = buildColorMap(sm);
        this.colorMapCache.set(leanPath, cm);
        return cm;
    }

    // ── Main update entry ────────────────────────────────────────────────────

    update(editor: vscode.TextEditor) {
        const p = editor.document.uri.fsPath;
        if (p.endsWith('.lean')) { this.updateLean(editor); }
        else if (p.endsWith('.rs')) { this.updateRust(editor); }
    }

    // ── Lean file update ─────────────────────────────────────────────────────

    private updateLean(editor: vscode.TextEditor) {
        const leanPath = editor.document.uri.fsPath;
        const sm = this.loadSourceMap(leanPath);

        if (!sm) {
            this.clearAll(editor);
            this.statusBar.hide();
            vscode.commands.executeCommand('setContext', 'hax.hasSourceMap', false);
            return;
        }

        vscode.commands.executeCommand('setContext', 'hax.hasSourceMap', true);
        const colorMap = this.getColorMap(leanPath);
        const cursor = editor.selection.active;

        // Rainbow background
        if (this.rainbowEnabled) {
            const buckets: vscode.Range[][] = Array.from({ length: N }, () => []);
            for (const [line, ci] of colorMap) {
                buckets[ci].push(new vscode.Range(line, 0, line, 0));
            }
            for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.bg[i], buckets[i]); }
        } else {
            for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.bg[i], []); }
        }

        // Active cursor highlight
        const activeMappings = findActiveSegment(sm, colorMap, cursor.line, cursor.character);
        for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.active[i], []); }

        if (activeMappings.length > 0) {
            const ci = colorMap.get(activeMappings[0].genLine) ?? 0;
            editor.setDecorations(this.decTypes.active[ci],
                activeMappings.map(m => new vscode.Range(m.genLine, 0, m.genLine, 0)));

            const rep = activeMappings[0];
            const srcPath = sm.resolvedPaths.get(rep.srcIdx) ?? sm.sources[rep.srcIdx] ?? '?';
            this.statusBar.text = `$(link) ${path.basename(srcPath)}:${rep.srcLine + 1}`;
            this.statusBar.tooltip = `Rust source: ${srcPath}:${rep.srcLine + 1}:${rep.srcCol + 1}\nClick to jump`;
            this.statusBar.show();

            // Highlight paired rust editors
            for (const ve of vscode.window.visibleTextEditors) {
                if (ve.document.uri.fsPath.endsWith('.rs')) {
                    this.applyRainbowToRust(ve, sm, colorMap, leanPath, rep, ci);
                }
            }
        } else {
            this.statusBar.hide();
            // Still paint rainbow on rust if visible
            for (const ve of vscode.window.visibleTextEditors) {
                if (ve.document.uri.fsPath.endsWith('.rs')) {
                    this.applyRainbowToRust(ve, sm, colorMap, leanPath, null, -1);
                }
            }
        }
    }

    // ── Rust file update ─────────────────────────────────────────────────────

    private updateRust(editor: vscode.TextEditor) {
        const rustPath = normPath(editor.document.uri.fsPath);

        // Ensure lean source maps are loaded for any open lean editors
        for (const ve of vscode.window.visibleTextEditors) {
            if (ve.document.fileName.endsWith('.lean')) {
                this.loadSourceMap(ve.document.uri.fsPath);
            }
        }

        const leanPaths = this.rustToLean.get(rustPath);
        if (!leanPaths || leanPaths.size === 0) {
            this.clearAll(editor);
            return;
        }
        vscode.commands.executeCommand('setContext', 'hax.hasReverseMap', true);

        const cursor = editor.selection.active;

        for (const leanPath of leanPaths) {
            const sm = this.loadSourceMap(leanPath);
            if (!sm) { continue; }
            const colorMap = this.getColorMap(leanPath);
            const srcIdx = [...sm.resolvedPaths.entries()].find(([, p]) => p === rustPath)?.[0];
            if (srcIdx === undefined) { continue; }

            this.applyRainbowToRust(editor, sm, colorMap, leanPath, null, -1);

            // Active: highlight current rust line
            const rustLineMappings = sm.mappings.filter(
                m => m.srcIdx === srcIdx && m.srcLine === cursor.line);
            if (rustLineMappings.length > 0) {
                const ci = colorMap.get(rustLineMappings[0].genLine) ?? 0;
                for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.active[i], []); }
                editor.setDecorations(this.decTypes.active[ci],
                    [new vscode.Range(cursor.line, 0, cursor.line, 0)]);
            }

            // Highlight lean editor if visible
            for (const ve of vscode.window.visibleTextEditors) {
                if (ve.document.uri.fsPath !== leanPath) { continue; }
                const leanMappings = sm.mappings.filter(
                    m => m.srcIdx === srcIdx && m.srcLine === cursor.line);
                for (let i = 0; i < N; i++) { ve.setDecorations(this.decTypes.active[i], []); }
                if (leanMappings.length > 0) {
                    const ci = colorMap.get(leanMappings[0].genLine) ?? 0;
                    ve.setDecorations(this.decTypes.active[ci],
                        leanMappings.map(m => new vscode.Range(m.genLine, 0, m.genLine, 0)));
                }
            }
        }
    }

    private applyRainbowToRust(
        editor: vscode.TextEditor,
        sm: SourceMapData,
        colorMap: Map<number, number>,
        _leanPath: string,
        activeMapping: Mapping | null,
        activeCi: number,
    ) {
        const rustPath = normPath(editor.document.uri.fsPath);
        const srcIdx = [...sm.resolvedPaths.entries()].find(([, p]) => p === rustPath)?.[0];
        if (srcIdx === undefined) { return; }

        if (this.rainbowEnabled) {
            // Build rust-line → colorIdx (one representative per source line).
            const rustLineColor = new Map<number, number>();
            for (const m of sm.mappings) {
                if (m.srcIdx !== srcIdx) { continue; }
                if (rustLineColor.has(m.srcLine)) { continue; }
                const ci = colorMap.get(m.genLine);
                if (ci !== undefined) { rustLineColor.set(m.srcLine, ci); }
            }

            // Sort and build contiguous ranges so gaps between mapped lines are filled.
            const sorted = [...rustLineColor.entries()].sort((a, b) => a[0] - b[0]);
            const buckets: vscode.Range[][] = Array.from({ length: N }, () => []);
            for (let i = 0; i < sorted.length; i++) {
                const [startLine, ci] = sorted[i];
                const endLine = i + 1 < sorted.length ? sorted[i + 1][0] - 1 : startLine;
                buckets[ci].push(new vscode.Range(startLine, 0, endLine, 0));
            }
            for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.bg[i], buckets[i]); }
        }

        if (activeMapping !== null && activeMapping.srcIdx === srcIdx) {
            for (let i = 0; i < N; i++) { editor.setDecorations(this.decTypes.active[i], []); }
            editor.setDecorations(this.decTypes.active[activeCi],
                [new vscode.Range(activeMapping.srcLine, 0, activeMapping.srcLine, 0)]);
        }
    }

    private clearAll(editor: vscode.TextEditor) {
        for (let i = 0; i < N; i++) {
            editor.setDecorations(this.decTypes.bg[i], []);
            editor.setDecorations(this.decTypes.active[i], []);
        }
    }

    // ── Commands ─────────────────────────────────────────────────────────────

    async jumpToSource() {
        const editor = vscode.window.activeTextEditor;
        if (!editor || !editor.document.fileName.endsWith('.lean')) { return; }

        const sm = this.loadSourceMap(editor.document.uri.fsPath);
        if (!sm) {
            vscode.window.showWarningMessage('Hax: no source map found for this file.');
            return;
        }

        const cursor = editor.selection.active;
        const m = closestMapping(sm.mappings, cursor.line, cursor.character);
        if (!m) {
            vscode.window.showWarningMessage('Hax: no mapping at cursor position.');
            return;
        }

        const resolved = sm.resolvedPaths.get(m.srcIdx);
        if (!resolved) {
            const content = sm.sourcesContent[m.srcIdx];
            if (content) {
                const doc = await vscode.workspace.openTextDocument({
                    language: 'rust',
                    content: `// Source: ${sm.sources[m.srcIdx]}\n// (file not found on disk)\n\n${content}`,
                });
                const te = await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
                const pos = new vscode.Position(m.srcLine + 3 /* header offset */, m.srcCol);
                te.selection = new vscode.Selection(pos, pos);
                te.revealRange(new vscode.Range(pos, pos), vscode.TextEditorRevealType.InCenter);
            } else {
                vscode.window.showWarningMessage(`Hax: source file not found: ${sm.sources[m.srcIdx]}`);
            }
            return;
        }

        const doc = await vscode.workspace.openTextDocument(vscode.Uri.file(resolved));
        const te = await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
        const pos = new vscode.Position(m.srcLine, m.srcCol);
        te.selection = new vscode.Selection(pos, pos);
        te.revealRange(new vscode.Range(pos, pos), vscode.TextEditorRevealType.InCenter);
    }

    async jumpToLean() {
        const editor = vscode.window.activeTextEditor;
        if (!editor) { return; }

        const rustPath = editor.document.uri.fsPath;

        // Eagerly load source maps for open lean editors
        for (const ve of vscode.window.visibleTextEditors) {
            if (ve.document.fileName.endsWith('.lean')) {
                this.loadSourceMap(ve.document.uri.fsPath);
            }
        }

        let leanPaths = this.rustToLean.get(rustPath);

        // If still empty, search workspace for .lean.map files
        if (!leanPaths || leanPaths.size === 0) {
            const maps = await vscode.workspace.findFiles('**/*.lean.map', '**/node_modules/**', 20);
            for (const mapUri of maps) {
                const leanPath = mapUri.fsPath.replace(/\.map$/, '');
                this.loadSourceMap(leanPath);
            }
            leanPaths = this.rustToLean.get(rustPath);
        }

        if (!leanPaths || leanPaths.size === 0) {
            vscode.window.showWarningMessage('Hax: no Lean extraction found for this Rust file.');
            return;
        }

        const cursorLine = editor.selection.active.line;

        for (const leanPath of leanPaths) {
            const sm = this.loadSourceMap(leanPath);
            if (!sm) { continue; }
            const srcIdx = [...sm.resolvedPaths.entries()].find(([, p]) => p === rustPath)?.[0];
            if (srcIdx === undefined) { continue; }

            const candidates = sm.mappings
                .filter(m => m.srcIdx === srcIdx && m.srcLine <= cursorLine + 5)
                .sort((a, b) => Math.abs(a.srcLine - cursorLine) - Math.abs(b.srcLine - cursorLine));

            if (candidates.length === 0) { continue; }

            const best = candidates[0];
            const doc = await vscode.workspace.openTextDocument(vscode.Uri.file(leanPath));
            const te = await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
            const pos = new vscode.Position(best.genLine, best.genCol);
            te.selection = new vscode.Selection(pos, pos);
            te.revealRange(new vscode.Range(pos, pos), vscode.TextEditorRevealType.InCenter);
            return;
        }

        vscode.window.showWarningMessage('Hax: no mapping found near cursor position.');
    }

    toggleRainbow() {
        this.rainbowEnabled = !this.rainbowEnabled;
        vscode.window.showInformationMessage(
            `Hax rainbow colours ${this.rainbowEnabled ? 'enabled' : 'disabled'}`);
        for (const editor of vscode.window.visibleTextEditors) { this.update(editor); }
    }

    invalidateCache() {
        this.smCache.clear();
        this.colorMapCache.clear();
        this.rustToLean.clear();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Pure helpers
// ─────────────────────────────────────────────────────────────────────────────

/** Assign a stable colour index to each (srcIdx:srcLine) key. */
function buildColorMap(sm: SourceMapData): Map<number, number> {
    const colorMap = new Map<number, number>();
    const keyToColor = new Map<string, number>();

    // Representative mapping per lean line (first one)
    const lineRep = new Map<number, Mapping>();
    for (const m of sm.mappings) {
        if (!lineRep.has(m.genLine)) { lineRep.set(m.genLine, m); }
    }

    let next = 0;
    // Sort by lean line so colours flow top-to-bottom
    for (const [genLine, m] of [...lineRep.entries()].sort((a, b) => a[0] - b[0])) {
        const key = `${m.srcIdx}:${m.srcLine}`;
        if (!keyToColor.has(key)) { keyToColor.set(key, next++ % N); }
        colorMap.set(genLine, keyToColor.get(key)!);
    }
    return colorMap;
}

/** Find the mapping entry at or just before (line, col). */
function closestMapping(mappings: Mapping[], line: number, col: number): Mapping | null {
    let best: Mapping | null = null;
    for (const m of mappings) {
        if (m.genLine > line) { break; }
        if (m.genLine < line || m.genCol <= col) { best = m; }
    }
    return best;
}

/**
 * Given a cursor position in the lean file, return all lean mappings that
 * belong to the same "active segment" (same srcIdx + srcLine as the cursor mapping).
 */
function findActiveSegment(
    sm: SourceMapData,
    colorMap: Map<number, number>,
    cursorLine: number,
    cursorCol: number,
): Mapping[] {
    const rep = closestMapping(sm.mappings, cursorLine, cursorCol);
    if (!rep) { return []; }

    // All lean lines that map to the same (srcIdx, srcLine)
    const seen = new Set<number>();
    return sm.mappings.filter(m => {
        if (m.srcIdx !== rep.srcIdx || m.srcLine !== rep.srcLine) { return false; }
        if (seen.has(m.genLine)) { return false; }
        seen.add(m.genLine);
        return true;
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// Hover provider
// ─────────────────────────────────────────────────────────────────────────────

class HaxHoverProvider implements vscode.HoverProvider {
    constructor(private readonly mgr: HaxManager) {}

    provideHover(
        document: vscode.TextDocument,
        position: vscode.Position,
    ): vscode.Hover | null {
        const leanPath = document.uri.fsPath;
        // Access the manager's source map via the public helper
        const mapPath = leanPath + '.map';
        if (!fs.existsSync(mapPath)) { return null; }
        // Decode inline (cached by mgr internally via update, but we need sm here)
        let raw: { sources?: string[]; sourcesContent?: (string|null)[]; mappings?: string };
        try { raw = JSON.parse(fs.readFileSync(mapPath, 'utf8')); }
        catch { return null; }

        const sources: string[] = raw.sources ?? [];
        const sourcesContent: (string | null)[] = raw.sourcesContent ?? [];
        const sm = decodeSourceMap(mapPath);
        if (!sm) { return null; }

        const m = closestMapping(sm.mappings, position.line, position.character);
        if (!m) { return null; }

        const srcPath = sm.resolvedPaths.get(m.srcIdx) ?? sources[m.srcIdx];
        if (!srcPath) { return null; }

        // Get a few lines of context
        let snippet: string;
        const content = sourcesContent[m.srcIdx];
        if (content) {
            const lines = content.split('\n');
            const start = Math.max(0, m.srcLine - 1);
            const end = Math.min(lines.length, m.srcLine + 3);
            snippet = lines.slice(start, end).join('\n');
        } else {
            try {
                const lines = fs.readFileSync(srcPath, 'utf8').split('\n');
                const start = Math.max(0, m.srcLine - 1);
                const end = Math.min(lines.length, m.srcLine + 3);
                snippet = lines.slice(start, end).join('\n');
            } catch {
                snippet = '';
            }
        }

        const label = `**Rust source** — \`${path.basename(srcPath)}\` line ${m.srcLine + 1}`;
        const md = new vscode.MarkdownString(
            `${label}\n\`\`\`rust\n${snippet}\n\`\`\``
        );
        return new vscode.Hover(md);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Extension entry point
// ─────────────────────────────────────────────────────────────────────────────

export function activate(ctx: vscode.ExtensionContext) {
    const mgr = new HaxManager(ctx);

    // Initial decoration pass
    for (const editor of vscode.window.visibleTextEditors) { mgr.update(editor); }

    ctx.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(e => { if (e) { mgr.update(e); } }),
        vscode.window.onDidChangeTextEditorSelection(e => { mgr.update(e.textEditor); }),
        vscode.window.onDidChangeVisibleTextEditors(editors => {
            for (const e of editors) { mgr.update(e); }
        }),
        // Invalidate cache when .lean.map files change on disk
        vscode.workspace.onDidSaveTextDocument(doc => {
            if (doc.fileName.endsWith('.lean.map') || doc.fileName.endsWith('.lean')) {
                mgr.invalidateCache();
                for (const e of vscode.window.visibleTextEditors) { mgr.update(e); }
            }
        }),
        vscode.commands.registerCommand('hax.jumpToSource', () => mgr.jumpToSource()),
        vscode.commands.registerCommand('hax.jumpToLean', () => mgr.jumpToLean()),
        vscode.commands.registerCommand('hax.toggleRainbow', () => mgr.toggleRainbow()),
        vscode.languages.registerHoverProvider(
            [{ language: 'lean4' }, { language: 'lean' }, { pattern: '**/*.lean' }],
            new HaxHoverProvider(mgr),
        ),
    );
}

export function deactivate() {}

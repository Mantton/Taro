const vscode = require('vscode');
const { LanguageClient } = require('vscode-languageclient/node');
const fs = require('fs');
const path = require('path');

let client = null;

function isUsableDistRoot(distRoot) {
    const taroName = process.platform === 'win32' ? 'taro.exe' : 'taro';
    return (
        fs.existsSync(path.join(distRoot, 'bin', taroName)) &&
        fs.existsSync(path.join(distRoot, 'lib', 'taro', 'std'))
    );
}

function maybeWithTaroHome(env, distRoot) {
    if (env.TARO_HOME || !distRoot || !isUsableDistRoot(distRoot)) {
        return env;
    }

    return { ...env, TARO_HOME: distRoot };
}

function resolveServerOptions() {
    const config = vscode.workspace.getConfiguration('taro');
    const configured = (config.get('languageServer.path') || '').trim();
    const env = resolveServerEnv(config);
    const exeName = process.platform === 'win32' ? 'taro-lsp.exe' : 'taro-lsp';

    // 1) Explicit user config wins.
    if (configured.length > 0) {
        return {
            command: configured,
            args: [],
            options: { env }
        };
    }

    // 2) Probe current workspace roots (local dist layout).
    const workspaceFolders = vscode.workspace.workspaceFolders || [];
    for (const folder of workspaceFolders) {
        const distRoot = path.join(folder.uri.fsPath, 'dist');
        const candidate = path.join(distRoot, 'bin', exeName);
        if (fs.existsSync(candidate)) {
            return {
                command: candidate,
                args: [],
                options: { env: maybeWithTaroHome(env, distRoot) }
            };
        }
    }

    // 3) Probe relative to this extension directory (repo-local dist layout).
    const repoRoot = path.resolve(__dirname, '..', '..');
    const distCandidate = path.join(repoRoot, 'dist', 'bin', exeName);
    if (fs.existsSync(distCandidate)) {
        return {
            command: distCandidate,
            args: [],
            options: { env: maybeWithTaroHome(env, path.join(repoRoot, 'dist')) }
        };
    }

    // 4) Probe repo-local debug build for extension development.
    const repoCandidate = path.join(repoRoot, 'target', 'debug', exeName);
    if (fs.existsSync(repoCandidate)) {
        return {
            command: repoCandidate,
            args: [],
            options: { env: maybeWithTaroHome(env, path.join(repoRoot, 'dist')) }
        };
    }

    // 5) Fallback to PATH lookup.
    const command = 'taro-lsp';
    return {
        command,
        args: [],
        options: { env }
    };
}

function resolveServerEnv(config) {
    const configuredEnv = config.get('languageServer.env') || {};
    if (
        configuredEnv === null ||
        typeof configuredEnv !== 'object' ||
        Array.isArray(configuredEnv)
    ) {
        return process.env;
    }

    const merged = { ...process.env };
    for (const [key, value] of Object.entries(configuredEnv)) {
        if (value === undefined || value === null) {
            continue;
        }
        merged[key] = String(value);
    }

    return merged;
}

function activate(context) {
    const serverOptions = resolveServerOptions();

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'taro' }]
    };

    client = new LanguageClient(
        'taroLanguageServer',
        'Taro Language Server',
        serverOptions,
        clientOptions
    );

    context.subscriptions.push(client.start());
}

function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

module.exports = {
    activate,
    deactivate
};

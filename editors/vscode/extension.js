const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

const SETTINGS = ['taro.languageServer.path', 'taro.sdk.path', 'taro.languageServer.bundle'];

let client;

/// The server accepts one source of standard-library analysis. An explicit
/// bundle is the narrower choice, so it wins over an SDK path.
function serverArguments(sdk, bundle) {
    if (bundle) {
        return ['--bundle', bundle];
    }
    return sdk ? ['--sdk', sdk] : [];
}

function createClient() {
    const config = vscode.workspace.getConfiguration('taro');
    const command = config.get('languageServer.path', 'taro-lsp');
    const sdk = config.get('sdk.path', '');
    const bundle = config.get('languageServer.bundle', '');
    if (sdk && bundle) {
        vscode.window.showWarningMessage(
            'Both taro.sdk.path and taro.languageServer.bundle are set; using the bundle.',
        );
    }
    return new LanguageClient(
        'taro',
        'Taro Language Server',
        { command, args: serverArguments(sdk, bundle), transport: TransportKind.stdio },
        {
            documentSelector: [{ scheme: 'file', language: 'taro' }],
        },
    );
}

function activate(context) {
    context.subscriptions.push(
        vscode.workspace.onDidChangeConfiguration(async (event) => {
            if (!SETTINGS.some((setting) => event.affectsConfiguration(setting))) {
                return;
            }
            await client?.stop();
            client = createClient();
            await client.start();
        }),
    );
    client = createClient();
    return client.start();
}

function deactivate() {
    return client?.stop();
}

module.exports = { activate, deactivate, serverArguments };

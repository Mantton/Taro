const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function activate(context) {
    const config = vscode.workspace.getConfiguration('taro');
    const command = config.get('languageServer.path', 'taro-lsp');
    const sdk = config.get('sdk.path', '');
    const bundle = config.get('languageServer.bundle', '');
    const args = [
        ...(sdk ? ['--sdk', sdk] : []),
        ...(bundle ? ['--bundle', bundle] : []),
    ];
    client = new LanguageClient(
        'taro',
        'Taro Language Server',
        { command, args, transport: TransportKind.stdio },
        {
            documentSelector: [{ scheme: 'file', language: 'taro' }],
        },
    );
    return client.start();
}

function deactivate() {
    return client?.stop();
}

module.exports = { activate, deactivate };

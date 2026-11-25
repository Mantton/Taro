const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function activate(context) {
    const command = vscode.workspace.getConfiguration('taro').get('languageServer.path', 'taro-lsp');
    const sources = vscode.workspace.createFileSystemWatcher('**/*.tr');
    const manifests = vscode.workspace.createFileSystemWatcher('**/{package.toml,package.lock}');
    context.subscriptions.push(sources, manifests);

    client = new LanguageClient(
        'taro',
        'Taro Language Server',
        { command, transport: TransportKind.stdio },
        {
            documentSelector: [{ scheme: 'file', language: 'taro' }],
            synchronize: { fileEvents: [sources, manifests] },
        },
    );
    return client.start();
}

function deactivate() {
    return client?.stop();
}

module.exports = { activate, deactivate };

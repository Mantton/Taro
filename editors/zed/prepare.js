// Zed fetches generated C from a Git checkout rather than running the generator.
// Stage a local dev extension while keeping generated artifacts out of source Git.
const { execFileSync } = require('node:child_process');
const { cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } = require('node:fs');
const path = require('node:path');
const { pathToFileURL } = require('node:url');

const root = path.resolve(__dirname, '../..');
const destination = path.join(root, 'tmp/zed-extension');
const checkout = path.join(destination, 'grammars/taro');
const repository = pathToFileURL(root).href;
const revision = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' }).trim();

mkdirSync(destination, { recursive: true });
if (!existsSync(checkout)) {
  execFileSync('git', ['clone', '--no-checkout', repository, checkout], { stdio: 'inherit' });
}
const origin = execFileSync('git', ['remote', 'get-url', 'origin'], { cwd: checkout, encoding: 'utf8' }).trim();
if (origin !== repository) throw new Error(`Unexpected grammar checkout origin: ${origin}`);
execFileSync('git', ['fetch', 'origin', revision], { cwd: checkout, stdio: 'inherit' });
execFileSync('git', ['checkout', '--detach', revision], { cwd: checkout, stdio: 'inherit' });

const parserSource = path.join(root, 'tree-sitter-taro/src');
if (!existsSync(path.join(parserSource, 'parser.c'))) throw new Error('Run npm run build first');
const stagedSource = path.join(checkout, 'tree-sitter-taro/src');
rmSync(stagedSource, { recursive: true, force: true });
cpSync(parserSource, stagedSource, { recursive: true });
const languages = path.join(destination, 'languages');
rmSync(languages, { recursive: true, force: true });
cpSync(path.join(__dirname, 'languages'), languages, { recursive: true });
writeFileSync(path.join(destination, 'extension.toml'),
  readFileSync(path.join(__dirname, 'extension.toml'), 'utf8') +
  `\n[grammars.taro]\nrepository = ${JSON.stringify(repository)}\nrev = "${revision}"\npath = "tree-sitter-taro"\n`);
console.log(`Install Dev Extension in Zed: ${destination}`);

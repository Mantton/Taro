const assert = require('node:assert/strict');
const { spawnSync } = require('node:child_process');
const { readdirSync } = require('node:fs');
const path = require('node:path');
const test = require('node:test');

const grammar = path.resolve(__dirname, '..');
const queries = path.resolve(grammar, '../editors/zed/languages/taro');
const fixture = path.join(__dirname, 'fixtures/editors.tr');

function treeSitter(...args) {
  const result = spawnSync(process.execPath, [require.resolve('tree-sitter-cli/cli'), ...args], {
    cwd: grammar,
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.error?.message ?? result.stderr + result.stdout);
  return result.stdout;
}

test('grammar parses repository examples and editor fixture without recovery', () => {
  const examples = path.resolve(grammar, '../examples');
  treeSitter('parse', '--quiet', fixture,
    ...readdirSync(examples).filter(name => name.endsWith('.tr')).map(name => path.join(examples, name)));
});

for (const [query, capture] of [
  ['highlights', 'function'],
  ['indents', 'indent'],
  ['textobjects', 'function.around'],
]) {
  test(`Zed ${query} query loads from the language directory and matches methods`, () => {
    const output = treeSitter('query', path.join(queries, `${query}.scm`), fixture);
    assert.ok(output.includes(capture), output);
    if (query === 'highlights') {
      assert.equal((output.match(/capture: \d+ - function, .*text: `read`/g) ?? []).length, 2);
    } else if (query === 'indents') {
      // Each container needs its whole multiline range, not just an opening brace.
      assert.equal((output.match(/capture: indent, /g) ?? []).length, 5);
    } else {
      assert.equal((output.match(/capture: class\.inside, /g) ?? []).length, 3);
      assert.match(output, /function\.around, .*text: `func read/);
    }
  });
}

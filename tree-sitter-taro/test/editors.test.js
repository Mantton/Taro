const assert = require('node:assert/strict');
const { spawnSync } = require('node:child_process');
const { readdirSync } = require('node:fs');
const path = require('node:path');
const test = require('node:test');

const grammar = path.resolve(__dirname, '..');
const queries = path.resolve(grammar, '../editors/zed/languages/taro');
const fixture = path.join(__dirname, 'fixtures/editors.tr');
const currentFixture = path.join(__dirname, 'fixtures/current-surface.tr');

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
  const fixtures = readdirSync(path.dirname(fixture)).filter(name => name.endsWith('.tr')).map(name => path.join(path.dirname(fixture), name));
  treeSitter('parse', '--quiet', ...fixtures,
    ...readdirSync(examples).filter(name => name.endsWith('.tr')).map(name => path.join(examples, name)));
});

test('current surface has dedicated span, accessor, async and defer nodes', () => {
  const output = treeSitter('parse', currentFixture);
  for (const node of ['span_type', 'subscript_declaration', 'computed_property_declaration',
    'extension_declaration', 'await_expression', 'defer_statement']) {
    assert.ok(output.includes(`(${node}`), output);
  }
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), currentFixture);
  assert.match(captures, /attribute, .*text: `NoCopy`/);
  assert.match(captures, /operator, .*text: `:=`/);
});

test('named constructors and patterns have field nodes', () => {
  const named = path.join(__dirname, 'fixtures/named-enums.tr');
  const output = treeSitter('parse', named);
  for (const node of ['enum_struct_field', 'struct_literal_expression', 'named_pattern', 'named_pattern_field']) {
    assert.ok(output.includes(`(${node}`), output);
  }
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), named);
  assert.match(captures, /property, .*text: `horizontal`|property, .*text: `x`/);
});

test('TextMate scopes describe current declarations and short bindings', () => {
  const syntax = require('../../editors/vscode/syntaxes/taro.tmLanguage.json');
  const storage = syntax.repository.storage.patterns.map(pattern => new RegExp(pattern.match));
  for (const word of ['class', 'extend', 'conform', 'init', 'var', 'subscript']) {
    assert.ok(storage.some(pattern => pattern.test(word)), word);
  }
  for (const word of ['let', 'impl', 'deinit', 'weak', 'ref', 'mut']) {
    assert.ok(storage.every(pattern => !pattern.test(word)), word);
  }
  assert.ok(syntax.repository.operators.patterns.some(pattern =>
    pattern.name === 'keyword.operator.assignment.short.taro' && new RegExp(pattern.match).test(':=')));
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
      assert.match(output, /function, .*text: `make`/);
    } else if (query === 'indents') {
      // Each container needs its whole multiline range, not just an opening brace.
      assert.equal((output.match(/capture: indent, /g) ?? []).length, 6);
    } else {
      assert.equal((output.match(/capture: class\.inside, /g) ?? []).length, 3);
      assert.match(output, /function\.around, .*text: `func read/);
    }
  });
}

test('struct updates have a final base expression node', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/struct-updates.tr'));
  assert.equal((output.match(/\(struct_update_base/g) ?? []).length, 2);
});

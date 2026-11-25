const assert = require('node:assert/strict');
const { spawnSync } = require('node:child_process');
const { readdirSync, readFileSync } = require('node:fs');
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

test('inherent extensions contain nested nominal declarations', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/nested-types.tr'));
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /extension_body/);
  for (const kind of ['class', 'struct', 'enum', 'interface']) {
    assert.match(output, new RegExp(kind + '_declaration'));
  }
});

test('lazy parameter modifiers are recognized on positional and labeled arguments', () => {
  const source = path.resolve(grammar, '../language_tests/source_files/valid/lazy_argument_order.tr');
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), source);
  assert.equal((captures.match(/attribute, .*text: `@lazy`/g) || []).length, 2);
});

test('delegation names a stored field and leaves by available as an argument label', () => {
  const output = treeSitter('parse', path.join(grammar,
    '../language_tests/source_files/valid/conformance_delegation_reference.tr'));
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /delegation_clause[\s\S]*?field: \(identifier/);
});

test('tuple types and literals expose labels and preserve nested positions', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/labeled-tuples.tr'));
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /labeled_tuple_type_element/);
  assert.match(output, /labeled_tuple_element/);
  assert.match(output, /closure_parameter/);
});

test('positional struct declarations expose their field types', () => {
  const fixture = path.resolve(grammar, '../language_tests/source_files/valid/tuple_struct.tr');
  const output = treeSitter('parse', fixture);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.equal((output.match(/\(positional_struct_fields\b/g) || []).length, 3);
  const patterns = treeSitter('parse', path.join(path.dirname(fixture), 'tuple_struct_patterns.tr'));
  assert.doesNotMatch(patterns, /ERROR|MISSING/);
  assert.match(patterns, /\(positional_struct_pattern\b/);
  treeSitter('parse', '--quiet', path.join(path.dirname(fixture), 'chained_tuple_projection.tr'));
});

test('nested patterns retain whole bindings and alternatives', () => {
  const tests = path.resolve(grammar, '../language_tests/source_files/valid');
  for (const [name, bindings, alternatives] of [['nested_pattern', 2, 1], ['nested_pattern_groups', 4, 2]]) {
    const output = treeSitter('parse', path.join(tests, name + '.tr'));
    assert.doesNotMatch(output, /ERROR|MISSING/);
    assert.equal((output.match(/\(at_pattern\b/g) || []).length, bindings);
    assert.equal((output.match(/\(or_pattern\b/g) || []).length, alternatives);
  }
});

test('dynamic type patterns distinguish typed bindings and unbound tests', () => {
  const tests = path.resolve(grammar, '../language_tests/source_files/valid');
  for (const [name, count] of [['dynamic_type_pattern', 5], ['dynamic_type_pattern_overlap', 2]]) {
    const output = treeSitter('parse', path.join(tests, name + '.tr'));
    assert.doesNotMatch(output, /ERROR|MISSING/);
    assert.equal((output.match(/\(type_pattern\b/g) || []).length, count);
  }
});

test('range patterns keep both endpoints in match arms and is expressions', () => {
  const tests = path.resolve(grammar, '../language_tests/source_files/valid');
  for (const [name, count] of [['range_pattern', 5], ['range_pattern_boundaries', 5]]) {
    const output = treeSitter('parse', path.join(tests, name + '.tr'));
    assert.doesNotMatch(output, /ERROR|MISSING/);
    assert.equal((output.match(/\(range_pattern\b/g) || []).length, count);
  }
});

test('is expressions accept enum patterns and preserve existing type tests', () => {
  const input = path.join(__dirname, 'fixtures/is-pattern.tr');
  const output = treeSitter('parse', input);
  assert.equal((output.match(/\(is_expression\b/g) || []).length, 4);
  assert.equal((output.match(/\(enum_pattern\b/g) || []).length, 2);
  assert.match(output, /\(named_pattern\b/);
  assert.doesNotMatch(output, /ERROR|MISSING/);
});

test('errdefer highlights failure cleanups and preserves identifier use', () => {
  const input = path.join(__dirname, 'fixtures/scoped-errdefer.tr');
  const output = treeSitter('parse', input);
  assert.equal((output.match(/\(errdefer_statement\b/g) || []).length, 2);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), input);
  assert.equal((captures.match(/keyword.control, .*text: `errdefer`/g) || []).length, 2);
});

test('using highlights only the resource declaration', () => {
  const input = path.join(__dirname, 'fixtures/scoped-using.tr');
  const output = treeSitter('parse', input);
  assert.equal((output.match(/\(using_statement\b/g) || []).length, 1);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), input);
  assert.equal((captures.match(/keyword.control, .*text: `using`/g) || []).length, 1);
});

test('postfix spread is a distinct node in calls and array literals', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/collection-spread.tr'));
  assert.equal((output.match(/\(spread_element\b/g) || []).length, 3);
});

test('source locations parse in defaults and expressions and get builtin highlighting', () => {
  const input = path.join(__dirname, 'fixtures/source-locations.tr');
  const output = treeSitter('parse', input);
  assert.equal((output.match(/\(source_location_literal\b/g) || []).length, 3);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), input);
  for (const literal of ['#file', '#line', '#function']) {
    assert.ok(captures.split('\n').some(line => line.includes('constant.builtin') && line.includes(literal)));
  }
});

test('embedded assets expose their directive and literal path', () => {
  const input = path.resolve(grammar, '../language_tests/package_fixtures/embedded_assets/dep/src/lib.tr');
  const output = treeSitter('parse', input);
  assert.equal((output.match(/\(embed_expression\b/g) || []).length, 4);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), input);
  for (const directive of ['embed', 'embedBytes']) {
    assert.ok(captures.split('\n').some(line => line.includes('function.builtin') && line.includes('`' + directive + '`')));
  }
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

test('closure shorthand, ignored parameters and tuple assignment have editor nodes', () => {
  const arrows = path.join(__dirname, 'fixtures/arrow-closures.tr');
  const output = treeSitter('parse', arrows);
  assert.ok(!output.includes('ERROR'), output);
  assert.match(output, /parameter: \(identifier/);
  assert.match(output, /name: \(wildcard_pattern/);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), arrows);
  assert.match(captures, /variable.parameter, .*text: `value`/);
  const bindings = treeSitter('parse', path.join(__dirname, 'fixtures/bindings.tr'));
  assert.equal((bindings.match(/\(assignment_statement/g) ?? []).length, 2);
  assert.match(bindings, /name: \(wildcard_pattern/);
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

test('membership tests have nodes, with ranges as containers', () => {
  const membership = path.join(__dirname, 'fixtures/membership.tr');
  const output = treeSitter('parse', membership);
  assert.ok(!output.includes('ERROR'), output);
  assert.equal((output.match(/\(membership_expression/g) ?? []).length, 5);
  assert.equal((output.match(/container: \(range_expression/g) ?? []).length, 2);
  // `!inside` stays a negated identifier.
  assert.match(output, /\(unary_expression [^\n]*\n\s*\(identifier [^\n]*\)\)\)\)\)\)/);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), membership);
  assert.match(captures, /keyword, .*text: `!in`/);
  const syntax = require('../../editors/vscode/syntaxes/taro.tmLanguage.json');
  const membershipPattern = syntax.repository.operators.patterns.find(pattern =>
    pattern.name === 'keyword.operator.membership.taro');
  assert.ok(new RegExp(membershipPattern.match).test('value !in set'));
  assert.ok(!new RegExp(membershipPattern.match).test('!inside'));
});

test('optional default assignment is a compound assignment', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/membership.tr'));
  assert.match(output, /\(compound_assignment/);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), path.join(__dirname, 'fixtures/membership.tr'));
  assert.match(captures, /operator, .*text: `\?\?=`/);
  const syntax = require('../../editors/vscode/syntaxes/taro.tmLanguage.json');
  const compound = syntax.repository.operators.patterns.find(pattern =>
    pattern.name === 'keyword.operator.assignment.compound.taro');
  assert.equal(new RegExp(compound.match).exec('cache ??= value')[0], '??=');
});

test('struct updates have a final base expression node', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/struct-updates.tr'));
  assert.equal((output.match(/\(struct_update_base/g) ?? []).length, 2);
});

test('Tree-sitter highlights hash-matched and nested interpolation', () => {
  const strings = path.join(__dirname, 'fixtures/strings.tr');
  const output = treeSitter('parse', strings);
  assert.ok(!output.includes('ERROR'), output);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), strings);
  for (const marker of ['${', '$#{', '$##{']) {
    assert.ok(captures.includes('text: `' + marker + '`'), captures);
  }
  assert.ok(output.includes('(string_escape'), output);
});

test('TextMate distinguishes literal markers, matching hashes and nested strings', async () => {
  const textmate = require('vscode-textmate');
  const oniguruma = require('vscode-oniguruma');
  await oniguruma.loadWASM(readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm')));
  const registry = new textmate.Registry({
    onigLib: Promise.resolve({
      createOnigScanner: patterns => new oniguruma.OnigScanner(patterns),
      createOnigString: value => new oniguruma.OnigString(value),
    }),
    loadGrammar: async () => require('../../editors/vscode/syntaxes/taro.tmLanguage.json'),
  });
  const syntax = await registry.loadGrammar('source.taro');
  function scopesAt(line, index, state = textmate.INITIAL) {
    return syntax.tokenizeLine(line, state).tokens.find(token => token.startIndex <= index && index < token.endIndex)?.scopes ?? [];
  }
  for (let hashes = 0; hashes <= 4; hashes++) {
    const delimiter = '#'.repeat(hashes);
    const marker = '$' + delimiter + '{';
    const line = `${delimiter}"before ${marker}name} after"${delimiter}`;
    assert.ok(scopesAt(line, line.indexOf(marker)).includes('meta.interpolation.taro'), line);
    assert.ok(!scopesAt(line, line.indexOf('after')).includes('meta.interpolation.taro'), line);
    if (hashes > 0) {
      const literal = `${delimiter}"literal \${name}"${delimiter}`;
      assert.ok(!scopesAt(literal, literal.indexOf('${')).includes('meta.interpolation.taro'), literal);
    }
  }
  const escaped = '"literal \\${name}"';
  assert.ok(!scopesAt(escaped, escaped.indexOf('$')).includes('meta.interpolation.taro'));
  const highHashes = '#####"literal ${name} $#####{name} "# inside"#####';
  assert.ok(scopesAt(highHashes, highHashes.indexOf('inside')).includes('string.quoted.raw.taro'));
  assert.ok(!scopesAt(highHashes, highHashes.indexOf('$#####{')).includes('meta.interpolation.taro'));
  const nested = '"${lookup("}")} tail"';
  assert.ok(scopesAt(nested, nested.indexOf('lookup')).includes('meta.interpolation.taro'));
  assert.ok(!scopesAt(nested, nested.indexOf('tail')).includes('meta.interpolation.taro'));
  let state = textmate.INITIAL;
  for (const line of ['#"""', '${literal} $#{name}', '"""#']) {
    const result = syntax.tokenizeLine(line, state);
    if (line.includes('${literal}')) {
      assert.ok(!scopesAt(line, 0, state).includes('meta.interpolation.taro'));
      assert.ok(scopesAt(line, line.indexOf('$#{'), state).includes('meta.interpolation.taro'));
    }
    state = result.ruleStack;
  }
  assert.ok(!scopesAt('var next = 1', 0, state).some(scope => scope.startsWith('string.')));
  registry.dispose();
});

test('interpolation format specifiers parse without error and highlight', () => {
  const source = path.resolve(grammar, '../language_tests/source_files/valid/string_interpolation_format.tr');
  const output = treeSitter('parse', source);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /interpolation_format/);
  const captures = treeSitter('query', path.join(queries, 'highlights.scm'), source);
  assert.match(captures, /string\.special, .*text: `:>8\.2`/);
  assert.match(captures, /string\.special, .*text: `:\?`/);
});

test('trailing closures parse with and without parameter headers', () => {
  const source = path.resolve(grammar, '../language_tests/source_files/valid/trailing_closures.tr');
  const output = treeSitter('parse', source);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /trailing_closure/);
});

test('tuple shorthand destructuring parses cleanly', () => {
  const source = path.join(__dirname, 'fixtures/tuple-shorthand.tr');
  const output = treeSitter('parse', source);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /shorthand_tuple_pattern/);
  assert.equal((output.match(/\(short_declaration/g) ?? []).length, 5);
});

test('optional chaining subscripts and calls parse cleanly', () => {
  const source = path.join(__dirname, 'fixtures/optional-chaining-subscript-call.tr');
  const output = treeSitter('parse', source);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.equal((output.match(/\(optional_chain/g) ?? []).length, 4);
  assert.match(output, /trailing_closure/);
});

test('open-ended ranges parse cleanly in slicing, membership, and loops', () => {
  const source = path.join(__dirname, 'fixtures/open-ended-ranges.tr');
  const output = treeSitter('parse', source);
  assert.doesNotMatch(output, /ERROR|MISSING/);
  assert.match(output, /range_expression/);
});

test('loop labels, select arms and field reflection have distinct syntax nodes', () => {
  const output = treeSitter('parse', path.join(__dirname, 'fixtures/const-loop-select-reflection.tr'));
  assert.doesNotMatch(output, /ERROR|MISSING/);
  for (const kind of ['loop_expression', 'select_arm', 'comptime_for_statement', 'comptime_if_statement', 'type_name_expression']) {
    assert.ok(output.includes('(' + kind), kind);
  }
  assert.doesNotMatch(output, /interpolation_format/);
});

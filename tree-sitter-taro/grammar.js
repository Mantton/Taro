/// <reference types="tree-sitter-cli/dsl" />

// Tree-sitter grammar for the Taro programming language.
// Focused on correct syntax highlighting — not a full semantic parser.

const PREC = {
  ASSIGN: 1,
  PIPE: 2,
  OR: 3,
  AND: 4,
  COMPARE: 5,
  BITWISE_OR: 6,
  BITWISE_XOR: 7,
  BITWISE_AND: 8,
  SHIFT: 9,
  ADD: 10,
  MULTIPLY: 11,
  UNARY: 12,
  CAST: 13,
  CALL: 14,
  MEMBER: 15,
};

module.exports = grammar({
  name: "taro",

  extras: ($) => [/\s/, $.line_comment, $.doc_comment],

  word: ($) => $.identifier,

  supertypes: ($) => [$._expression, $._type, $._statement, $._pattern],

  conflicts: ($) => [
    [$.simple_type, $._expression],
    [$.inferred_type, $.wildcard_pattern],
    [$.simple_type, $.identifier_pattern],
    [$.callable_type, $._expression],
    [$.callable_type, $.identifier_pattern],
    [$.callable_type, $.simple_type],
  ],

  rules: {
    source_file: ($) => repeat($._declaration),

    // ──────────────────────────────────────────
    //  Declarations
    // ──────────────────────────────────────────

    _declaration: ($) =>
      choice(
        $.function_declaration,
        $.struct_declaration,
        $.enum_declaration,
        $.interface_declaration,
        $.impl_declaration,
        $.type_alias_declaration,
        $.const_declaration,
        $.static_declaration,
        $.import_declaration,
        $.namespace_declaration,
        $.extern_block,
      ),

    function_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "func",
        field("name", $.identifier),
        optional($.generic_parameters),
        $.parameter_list,
        optional(seq("->", field("return_type", $._type))),
        optional($.where_clause),
        field("body", $.block),
      ),

    // Used inside interface/impl bodies — body is optional (for interface signatures)
    method_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "func",
        field("name", $.identifier),
        optional($.generic_parameters),
        $.parameter_list,
        optional(seq("->", field("return_type", $._type))),
        optional($.where_clause),
        optional(field("body", $.block)),
      ),

    struct_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "struct",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional($.where_clause),
        $.struct_body,
      ),

    struct_body: ($) =>
      seq("{", repeat($.struct_field), "}"),

    struct_field: ($) =>
      seq(
        optional($.visibility_modifier),
        field("name", $.identifier),
        ":",
        field("type", $._type),
      ),

    enum_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "enum",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional($.where_clause),
        $.enum_body,
      ),

    enum_body: ($) => seq("{", repeat($.enum_variant), "}"),

    enum_variant: ($) =>
      seq(
        "case",
        field("name", $.identifier),
        optional(seq("(", commaSep1($._type), ")")),
      ),

    interface_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "interface",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional(seq(":", commaSep1($._type))),
        optional($.where_clause),
        $.declaration_body,
      ),

    impl_declaration: ($) =>
      seq(
        repeat($.attribute),
        "impl",
        optional($.generic_parameters),
        optional(seq($._type, "for")),
        field("type", $._type),
        optional($.where_clause),
        $.declaration_body,
      ),

    declaration_body: ($) =>
      seq(
        "{",
        repeat(choice($.method_declaration, $.type_alias_declaration, $.const_declaration)),
        "}",
      ),

    type_alias_declaration: ($) =>
      seq(
        optional($.visibility_modifier),
        "type",
        field("name", choice($.type_identifier, $.identifier)),
        optional($.generic_parameters),
        optional(seq("=", field("type", $._type))),
      ),

    const_declaration: ($) =>
      seq(
        optional($.visibility_modifier),
        "const",
        field("name", $.identifier),
        optional(seq(":", field("type", $._type))),
        "=",
        field("value", $._expression),
      ),

    static_declaration: ($) =>
      seq(
        optional($.visibility_modifier),
        "static",
        optional("var"),
        field("name", $.identifier),
        ":",
        field("type", $._type),
        "=",
        field("value", $._expression),
      ),

    import_declaration: ($) => seq("import", $.import_path),

    import_path: ($) =>
      seq($.identifier, repeat(seq(".", choice($.identifier, "*")))),

    namespace_declaration: ($) =>
      seq(
        optional($.visibility_modifier),
        "namespace",
        field("name", $.type_identifier),
        "{",
        repeat($._declaration),
        "}",
      ),

    extern_block: ($) =>
      seq(
        "extern",
        optional($.string_literal),
        "{",
        repeat($.extern_function),
        "}",
      ),

    extern_function: ($) =>
      seq(
        "func",
        field("name", $.identifier),
        $.parameter_list,
        optional(seq("->", field("return_type", $._type))),
      ),

    // ──────────────────────────────────────────
    //  Attributes
    // ──────────────────────────────────────────

    attribute: ($) =>
      seq(
        "@",
        $.identifier,
        optional(seq("(", optional($._attribute_content), ")")),
      ),

    _attribute_content: ($) =>
      commaSep1($._attribute_arg),

    _attribute_arg: ($) =>
      choice(
        $.identifier,
        $.string_literal,
        $.number_literal,
        seq($.identifier, "(", optional($._attribute_content), ")"),
        prec(3, seq("!", $._attribute_arg)),
        prec.left(1, seq($._attribute_arg, "||", $._attribute_arg)),
        prec.left(2, seq($._attribute_arg, "&&", $._attribute_arg)),
        seq("(", $._attribute_arg, ")"),
      ),

    // ──────────────────────────────────────────
    //  Visibility
    // ──────────────────────────────────────────

    visibility_modifier: ($) => choice("public", "private", "export"),

    // ──────────────────────────────────────────
    //  Generics & Where
    // ──────────────────────────────────────────

    generic_parameters: ($) =>
      seq("[", commaSep1($.generic_parameter), "]"),

    generic_parameter: ($) =>
      seq(
        field("name", choice($.type_identifier, "const")),
        optional(seq(":", $._type_bound)),
      ),

    _type_bound: ($) => seq($._type, repeat(seq("+", $._type))),

    generic_arguments: ($) => seq("[", commaSep1($._type_arg), "]"),

    _type_arg: ($) =>
      choice(
        $._type,
        $.type_binding,
      ),

    type_binding: ($) =>
      seq($.type_identifier, "=", $._type),

    where_clause: ($) =>
      seq("where", commaSep1($.where_predicate)),

    where_predicate: ($) =>
      seq($._type, ":", $._type_bound),

    // ──────────────────────────────────────────
    //  Parameters
    // ──────────────────────────────────────────

    parameter_list: ($) => seq("(", commaSep($.parameter), ")"),

    parameter: ($) =>
      choice(
        // self parameters
        seq(optional("&"), optional("mut"), "self"),
        // labelled: `label name: Type` or `_ name: Type`
        seq(
          field("label", choice($.identifier, "_")),
          field("name", $.identifier),
          ":",
          field("type", $._type),
          optional(seq("=", field("default", $._expression))),
        ),
        // unlabelled: `name: Type`
        seq(
          field("name", $.identifier),
          ":",
          field("type", $._type),
          optional(seq("=", field("default", $._expression))),
        ),
      ),

    // ──────────────────────────────────────────
    //  Types
    // ──────────────────────────────────────────

    _type: ($) =>
      choice(
        $.simple_type,
        $.generic_type,
        $.function_type,
        $.callable_type,
        $.reference_type,
        $.optional_type,
        $.pointer_type,
        $.array_type,
        $.existential_type,
        $.parenthesized_type,
        $.associated_type,
        $.inferred_type,
        $.never_type,
      ),

    simple_type: ($) => choice($.type_identifier, $.identifier),

    generic_type: ($) =>
      prec(PREC.MEMBER, seq($._type, "[", commaSep1($._type_arg), "]")),

    function_type: ($) =>
      seq("(", commaSep($._type), ")", "->", $._type),

    // Fn(T) -> U, AsyncFn(T) -> U
    callable_type: ($) =>
      seq(
        field("trait", choice($.type_identifier, $.identifier)),
        "(",
        commaSep($._type),
        ")",
        optional(seq("->", $._type)),
      ),

    reference_type: ($) => prec.right(PREC.UNARY + 1, seq("&", optional("mut"), $._type)),

    optional_type: ($) => prec.left(PREC.UNARY, seq($._type, "?")),

    pointer_type: ($) => prec.right(PREC.UNARY + 1, seq("*", optional("mut"), $._type)),

    array_type: ($) => seq("[", $._type, ";", $._expression, "]"),

    existential_type: ($) =>
      prec.right(PREC.UNARY + 1, seq("any", $._type, repeat(seq("&", $._type)))),

    parenthesized_type: ($) => seq("(", $._type, ")"),

    associated_type: ($) =>
      prec(PREC.MEMBER, seq($._type, ".", choice($.type_identifier, $.identifier))),

    inferred_type: ($) => "_",

    never_type: ($) => "!",

    // ──────────────────────────────────────────
    //  Statements
    // ──────────────────────────────────────────

    _statement: ($) =>
      choice(
        $.let_declaration,
        $.var_declaration,
        $.return_statement,
        $.break_statement,
        $.continue_statement,
        $.defer_statement,
        $.guard_statement,
        $.for_statement,
        $.while_statement,
        $.loop_statement,
        $.assignment_statement,
        $.compound_assignment,
        $.expression_statement,
      ),

    let_declaration: ($) =>
      prec.right(
        seq(
          "let",
          field("pattern", $._pattern),
          optional(seq(":", field("type", $._type))),
          optional(seq("=", field("value", $._expression))),
        ),
      ),

    var_declaration: ($) =>
      prec.right(
        seq(
          "var",
          field("name", $.identifier),
          optional(seq(":", field("type", $._type))),
          optional(seq("=", field("value", $._expression))),
        ),
      ),

    return_statement: ($) => prec.right(seq("return", optional($._expression))),

    break_statement: ($) => "break",
    continue_statement: ($) => "continue",

    defer_statement: ($) => seq("defer", $.block),

    guard_statement: ($) =>
      seq("guard", $._expression, "else", $.block),

    for_statement: ($) =>
      seq(
        "for",
        field("pattern", $._pattern),
        "in",
        field("iterable", $._expression),
        $.block,
      ),

    while_statement: ($) => seq("while", $._expression, $.block),

    loop_statement: ($) => seq("loop", $.block),

    assignment_statement: ($) =>
      prec.right(PREC.ASSIGN, seq($._expression, "=", $._expression)),

    compound_assignment: ($) =>
      prec.right(
        PREC.ASSIGN,
        seq(
          $._expression,
          choice("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="),
          $._expression,
        ),
      ),

    expression_statement: ($) => $._expression,

    // ──────────────────────────────────────────
    //  Expressions
    // ──────────────────────────────────────────

    _expression: ($) =>
      choice(
        $.identifier,
        $.type_identifier,
        $.self_expression,
        $.number_literal,
        $.string_literal,
        $.rune_literal,
        $.boolean_literal,
        $.nil_literal,
        $.binary_expression,
        $.unary_expression,
        $.call_expression,
        $.member_expression,
        $.index_expression,
        $.cast_expression,
        $.is_expression,
        $.range_expression,
        $.closure_expression,
        $.if_expression,
        $.match_expression,
        $.struct_literal_expression,
        $.array_literal,
        $.parenthesized_expression,
        $.block,
        $.pipe_expression,
        $.optional_chain,
        $.nil_coalesce,
        $.try_expression,
        $.deref_expression,
        $.mutable_reference_expression,
        $.unsafe_expression,
        $.compiler_directive,
      ),

    self_expression: ($) => "self",

    binary_expression: ($) =>
      choice(
        ...[
          ["+", PREC.ADD],
          ["-", PREC.ADD],
          ["*", PREC.MULTIPLY],
          ["/", PREC.MULTIPLY],
          ["%", PREC.MULTIPLY],
          ["==", PREC.COMPARE],
          ["!=", PREC.COMPARE],
          ["<", PREC.COMPARE],
          [">", PREC.COMPARE],
          ["<=", PREC.COMPARE],
          [">=", PREC.COMPARE],
          ["&&", PREC.AND],
          ["||", PREC.OR],
          ["&", PREC.BITWISE_AND],
          ["|", PREC.BITWISE_OR],
          ["^", PREC.BITWISE_XOR],
          ["<<", PREC.SHIFT],
          [">>", PREC.SHIFT],
        ].map(([op, p]) => prec.left(p, seq($._expression, op, $._expression))),
      ),

    unary_expression: ($) =>
      prec(PREC.UNARY, seq(choice("!", "-", "~", "*", "&"), $._expression)),

    mutable_reference_expression: ($) =>
      prec(PREC.UNARY, seq("&", "mut", $._expression)),

    call_expression: ($) =>
      prec(PREC.CALL, seq($._expression, optional($.generic_arguments), $.argument_list)),

    argument_list: ($) => seq("(", commaSep($.argument), ")"),

    argument: ($) =>
      choice(
        seq(field("label", $.identifier), ":", field("value", $._expression)),
        field("value", $._expression),
      ),

    member_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, ".", $.identifier)),

    index_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, "[", $._expression, "]")),

    cast_expression: ($) =>
      prec.left(PREC.CAST, seq($._expression, choice("as", "as?", "as!"), $._type)),

    is_expression: ($) =>
      prec.left(PREC.CAST, seq($._expression, "is", $._type)),

    range_expression: ($) =>
      choice(
        prec.right(PREC.PIPE, seq($._expression, "..", $._expression)),
        prec.right(PREC.PIPE, seq($._expression, "..=", $._expression)),
        prec.right(PREC.PIPE, seq($._expression, "..")),
        prec.right(PREC.PIPE, seq("..", $._expression)),
        "...",
      ),

    pipe_expression: ($) =>
      prec.left(PREC.PIPE, seq($._expression, "|>", $._expression)),

    optional_chain: ($) =>
      prec(PREC.MEMBER, seq($._expression, "?.", $.identifier)),

    nil_coalesce: ($) =>
      prec.right(PREC.OR, seq($._expression, "??", $._expression)),

    try_expression: ($) =>
      prec.left(PREC.CALL, seq($._expression, "?")),

    deref_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, ".*")),

    closure_expression: ($) =>
      prec.right(
        seq(
          "|",
          commaSep($.closure_parameter),
          "|",
          optional(seq("->", $._type)),
          $.block,
        ),
      ),

    closure_parameter: ($) =>
      seq(
        field("name", $.identifier),
        optional(seq(":", field("type", $._type))),
      ),

    if_expression: ($) =>
      prec.right(
        seq(
          "if",
          field("condition", $._expression),
          field("consequence", $.block),
          optional(
            seq("else", field("alternative", choice($.if_expression, $.block))),
          ),
        ),
      ),

    match_expression: ($) =>
      seq("match", field("value", $._expression), "{", repeat($.match_arm), "}"),

    match_arm: ($) =>
      prec.right(1, seq("case", $._pattern, "=>", choice($.block, $._expression))),

    struct_literal_expression: ($) =>
      prec(
        PREC.CALL,
        seq(
          field("type", $._type),
          "{",
          commaSep($.struct_literal_field),
          optional(","),
          "}",
        ),
      ),

    struct_literal_field: ($) =>
      seq(field("name", $.identifier), ":", field("value", $._expression)),

    array_literal: ($) =>
      choice(
        seq("[", commaSep($._expression), optional(","), "]"),
        seq("[", $._expression, ";", $._expression, "]"),
      ),

    parenthesized_expression: ($) => seq("(", $._expression, ")"),

    unsafe_expression: ($) => seq("unsafe", $.block),

    compiler_directive: ($) =>
      seq("#", $.identifier, "(", optional($._attribute_content), ")"),

    block: ($) => seq("{", repeat($._statement), "}"),

    // ──────────────────────────────────────────
    //  Patterns
    // ──────────────────────────────────────────

    _pattern: ($) =>
      choice(
        $.identifier_pattern,
        $.wildcard_pattern,
        $.enum_pattern,
        $.tuple_pattern,
        $.or_pattern,
        $.binding_pattern,
        $.literal_pattern,
      ),

    identifier_pattern: ($) => $.identifier,

    wildcard_pattern: ($) => "_",

    enum_pattern: ($) =>
      prec.left(
        choice(
          seq($._type, ".", $.identifier, optional($.tuple_pattern)),
          seq(".", $.identifier, optional($.tuple_pattern)),
        ),
      ),

    tuple_pattern: ($) => seq("(", commaSep($._pattern), ")"),

    or_pattern: ($) => prec.left(seq($._pattern, "|", $._pattern)),

    binding_pattern: ($) => prec(1, seq(choice("let", "var"), $._pattern)),

    literal_pattern: ($) =>
      choice(
        $.number_literal,
        $.string_literal,
        $.rune_literal,
        $.boolean_literal,
        $.nil_literal,
      ),

    // ──────────────────────────────────────────
    //  Literals
    // ──────────────────────────────────────────

    number_literal: ($) =>
      token(
        choice(
          // Hex
          seq("0", choice("x", "X"), /[0-9a-fA-F][0-9a-fA-F_]*/),
          // Binary
          seq("0", choice("b", "B"), /[01][01_]*/),
          // Octal
          seq("0", choice("o", "O"), /[0-7][0-7_]*/),
          // Float
          seq(/[0-9][0-9_]*/, ".", /[0-9][0-9_]*/),
          // Integer with optional type suffix
          seq(
            /[0-9][0-9_]*/,
            optional(choice(/[iI](8|16|32|64)/, /[uU](8|16|32|64)/)),
          ),
        ),
      ),

    string_literal: ($) =>
      seq('"', repeat(choice($.escape_sequence, /[^"\\]+/)), '"'),

    rune_literal: ($) =>
      seq("'", choice($.escape_sequence, /[^'\\]/), "'"),

    escape_sequence: ($) =>
      token.immediate(
        seq(
          "\\",
          choice(
            /[\\'"0nrt]/,
            seq("x", /[0-9a-fA-F]{2}/),
            seq("u", "{", /[0-9a-fA-F]+/, "}"),
          ),
        ),
      ),

    boolean_literal: ($) => choice("true", "false"),

    nil_literal: ($) => "nil",

    // ──────────────────────────────────────────
    //  Identifiers
    // ──────────────────────────────────────────

    // Uppercase-leading identifier used for type names
    type_identifier: ($) => /[A-Z][a-zA-Z0-9_]*/,

    // General identifier
    identifier: ($) => /[a-zA-Z_][a-zA-Z0-9_]*/,

    // ──────────────────────────────────────────
    //  Comments
    // ──────────────────────────────────────────

    line_comment: ($) => token(seq("//", /[^\/\n][^\n]*|[^\n\/]|/)),

    doc_comment: ($) => token(seq("///", /[^\n]*/)),
  },
});

function commaSep(rule) {
  return optional(commaSep1(rule));
}

function commaSep1(rule) {
  return seq(rule, repeat(seq(",", rule)), optional(","));
}

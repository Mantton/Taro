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
    [$.inferred_member_expression, $.enum_pattern],
    [$.inferred_type, $.wildcard_pattern],
    [$.simple_type, $.identifier_pattern],
    [$.generic_parameter, $.simple_type],
    [$.callable_type, $._expression],
    [$.callable_type, $.identifier_pattern],
    [$.callable_type, $.simple_type],
    [$.method_declaration, $.initializer_declaration],
    [$.method_declaration, $.initializer_declaration, $.subscript_declaration],
    [$.simple_type, $._expression, $.closure_parameter],
    [$.closure_expression, $.unit_expression],
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
        $.class_declaration,
        $.enum_declaration,
        $.interface_declaration,
        $.extension_declaration,
        $.conformance_declaration,
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
        optional("unsafe"),
        "func",
        field("name", $.identifier),
        optional($.generic_parameters),
        $.parameter_list,
        optional("async"),
        optional(seq("->", field("return_type", $._type))),
        optional("async"),
        optional($.where_clause),
        field("body", $.block),
      ),

    // Used inside interface/extension/conformance bodies — body is optional (for interface signatures)
    method_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        repeat(choice("final", "override")),
        optional("static"),
        optional("unsafe"),
        "func",
        field("name", $.identifier),
        optional($.generic_parameters),
        $.parameter_list,
        optional("async"),
        optional(seq("->", field("return_type", $._type))),
        optional("async"),
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
        optional(seq(":", commaSep1($._type))),
        optional($.where_clause),
        $.struct_body,
      ),

    class_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        optional("final"),
        "class",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional(seq(":", commaSep1($._type))),
        optional($.where_clause),
        $.struct_body,
      ),

    struct_body: ($) =>
      seq("{", repeat(seq($.struct_field, optional(";"))), "}"),

    struct_field: ($) =>
      seq(
        optional($.visibility_modifier),
        optional("readonly"),
        field("name", $.identifier),
        ":",
        field("type", $._type),
        optional(seq("=", field("default", $._expression))),
      ),

    enum_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "enum",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional(seq(":", commaSep1($._type))),
        optional($.where_clause),
        $.enum_body,
      ),

    enum_body: ($) => seq("{", repeat($.enum_case), "}"),

    enum_case: ($) => seq("case", commaSep1($.enum_variant), optional(";")),

    enum_variant: ($) =>
      seq(
        field("name", $.identifier),
        optional(choice(
          seq("(", commaSep($.enum_tuple_field), ")"),
          $.enum_payload_body,
        )),
        optional(seq("=", $._expression)),
      ),

    enum_tuple_field: ($) =>
      seq(optional("readonly"), optional(seq($.identifier, ":")), $._type),

    enum_payload_body: ($) =>
      seq("{", repeat(seq($.enum_struct_field, optional(choice(",", ";")))), "}"),

    enum_struct_field: ($) =>
      seq(optional("readonly"), field("name", $.identifier), ":", field("type", $._type)),

    interface_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        "interface",
        field("name", $.type_identifier),
        optional($.generic_parameters),
        optional(seq(":", commaSep1($._capability_bound))),
        optional($.where_clause),
        $.declaration_body,
      ),

    extension_declaration: ($) =>
      seq(repeat($.attribute), "extend", optional($.generic_parameters),
        field("type", $._type), optional($.where_clause), $.declaration_body),

    conformance_declaration: ($) =>
      seq(repeat($.attribute), "conform", optional($.generic_parameters),
        field("type", $._type), "to", field("interface", $._type),
        optional($.where_clause), $.declaration_body),

    declaration_body: ($) =>
      seq(
        "{",
        repeat(seq(choice($.method_declaration, $.initializer_declaration, $.computed_property_declaration, $.subscript_declaration, $.type_alias_declaration, $.const_declaration), optional(";"))),
        "}",
      ),

    initializer_declaration: ($) =>
      seq(
        repeat($.attribute),
        optional($.visibility_modifier),
        repeat(choice("required", "convenience", "override")),
        "init",
        optional($.generic_parameters),
        $.parameter_list,
        optional($.where_clause),
        field("body", $.block),
      ),

    computed_property_declaration: ($) =>
      seq(optional($.visibility_modifier), "var", field("name", $.identifier),
        ":", $._type, "{", "get", optional($.block), "}"),

    subscript_declaration: ($) =>
      seq(optional($.visibility_modifier), repeat(choice("final", "override")),
        "subscript", $.parameter_list, "->", $._type, "{",
        repeat1($.subscript_accessor), "}"),

    subscript_accessor: ($) =>
      seq(choice("get", "address", seq("set", optional(seq("(", $.identifier, ")")))),
        optional($.block)),

    type_alias_declaration: ($) =>
      seq(
        optional($.visibility_modifier),
        "type",
        field("name", choice($.type_identifier, $.identifier)),
        optional($.generic_parameters),
        optional(seq(":", $._type_bound)),
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
      seq(
        $.identifier,
        repeat(seq("::", $.identifier)),
        optional(seq("::", choice("*", seq("{", commaSep1($.import_item), "}")))),
        optional(seq("as", $.identifier)),
      ),

    import_item: ($) => seq($.identifier, optional(seq("as", $.identifier))),

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
        optional("async"),
        optional(seq("->", field("return_type", $._type))),
        optional("async"),
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

    visibility_modifier: ($) => choice("public", "private", "internal", "export"),

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

    _capability_bound: ($) => prec(1, $._type),

    _type_bound: ($) => seq($._capability_bound, repeat(seq("&", $._capability_bound))),

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
        $.span_type,
        $.list_type,
        $.dictionary_type,
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

    reference_type: ($) => prec.right(PREC.UNARY + 1, seq("&", $._type)),

    optional_type: ($) => prec.left(PREC.UNARY, seq($._type, "?")),

    pointer_type: ($) => prec.right(PREC.UNARY + 1, seq("*", optional(choice("const", "mut")), $._type)),

    array_type: ($) => seq("[", $._type, ";", $._expression, "]"),
    span_type: ($) => seq("[", $._type, ";", "..", "]"),
    list_type: ($) => seq("[", $._type, "]"),
    dictionary_type: ($) => seq("[", $._type, ":", $._type, "]"),

    existential_type: ($) =>
      prec.right(PREC.UNARY + 1, seq("any", $._type, repeat(seq("&", $._type)))),

    parenthesized_type: ($) => seq("(", $._type, ")"),

    associated_type: ($) =>
      prec(PREC.MEMBER, seq($._type, "::", choice($.type_identifier, $.identifier))),

    inferred_type: ($) => "_",

    never_type: ($) => "!",

    // ──────────────────────────────────────────
    //  Statements
    // ──────────────────────────────────────────

    _statement: ($) =>
      choice(
        $.var_declaration,
        $.short_declaration,
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

    var_declaration: ($) =>
      prec.right(
        seq(
          "var",
          field("pattern", $._pattern),
          optional(seq(":", field("type", $._type))),
          optional(seq("=", field("value", $._expression))),
        ),
      ),

    short_declaration: ($) =>
      seq(field("name", $.identifier), ":=", field("value", $._expression)),

    _condition: ($) => choice($._expression, $.binding_expression, $.condition_conjunction),

    condition_conjunction: ($) =>
      prec.left(PREC.AND, seq($._condition, "&&", $._condition)),

    binding_expression: ($) =>
      prec.right(PREC.COMPARE, choice(
        seq("var", field("name", $.identifier), optional(seq("=", field("value", $._expression)))),
        seq("case", optional("var"), field("pattern", $._pattern), "=", field("value", $._expression)),
      )),

    return_statement: ($) => prec.right(seq("return", optional($._expression))),

    break_statement: ($) => "break",
    continue_statement: ($) => "continue",

    defer_statement: ($) => prec.right(seq("defer", $._expression)),

    guard_statement: ($) =>
      seq("guard", $._condition, "else", $.block),

    for_statement: ($) =>
      seq(
        "for",
        field("pattern", $._pattern),
        "in",
        field("iterable", $._expression),
        $.block,
      ),

    while_statement: ($) => seq("while", $._condition, $.block),

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
        $.f_string_literal,
        $.rune_literal,
        $.boolean_literal,
        $.nil_literal,
        $.binary_expression,
        $.unary_expression,
        $.await_expression,
        $.call_expression,
        $.member_expression,
        $.inferred_member_expression,
        $.qualified_expression,
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
        $.tuple_expression,
        $.unit_expression,
        $.block,
        $.pipe_expression,
        $.optional_chain,
        $.nil_coalesce,
        $.try_expression,
        $.deref_expression,
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

    await_expression: ($) => prec(PREC.UNARY, seq("await", $._expression)),

    call_expression: ($) =>
      prec(PREC.CALL, seq($._expression, optional($.generic_arguments), $.argument_list)),

    argument_list: ($) => seq("(", commaSep($.argument), ")"),

    argument: ($) =>
      choice(
        seq(field("label", $.identifier), ":", field("value", $._expression)),
        field("value", $._expression),
      ),

    inferred_member_expression: ($) => seq(".", $.identifier),

    member_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, ".", $.identifier)),

    qualified_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, "::", $.identifier)),

    index_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, "[", commaSep1($._expression), "]")),

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
      prec.left(PREC.CALL, seq($._expression, "!")),

    deref_expression: ($) =>
      prec(PREC.MEMBER, seq($._expression, ".*")),

    closure_expression: ($) =>
      prec.right(
        seq(
          "(", commaSep($.closure_parameter), ")",
          choice(
            seq(optional("async"), optional(seq("->", $._type))),
            seq("->", $._type, "async"),
          ),
          "=>",
          $._expression,
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
          field("condition", $._condition),
          field("consequence", $.block),
          optional(
            seq("else", field("alternative", choice($.if_expression, $.block))),
          ),
        ),
      ),

    match_expression: ($) =>
      seq("match", field("value", $._expression), "{", repeat($.match_arm), "}"),

    match_arm: ($) =>
      prec.right(1, seq("case", $._pattern, optional(seq("if", $._expression)), "=>", choice($.block, $._expression))),

    struct_literal_expression: ($) =>
      prec(
        PREC.CALL,
        seq(
          field("type", choice($._type, $.inferred_member_expression)),
          "{",
          optional(choice(
            seq(commaSep1($.struct_literal_field), optional(seq(",", $.struct_update_base)), optional(",")),
            seq($.struct_update_base, optional(",")),
          )),
          "}",
        ),
      ),

    struct_update_base: ($) => seq("..", field("value", $._expression)),

    struct_literal_field: ($) =>
      seq(field("name", $.identifier), optional(seq(":", field("value", $._expression)))),

    array_literal: ($) =>
      choice(
        seq("[", commaSep($._expression), optional(","), "]"),
        seq("[", $._expression, ";", $._expression, "]"),
      ),

    tuple_expression: ($) => seq("(", $._expression, ",", optional(commaSep1($._expression)), ")"),

    unit_expression: ($) => seq("(", ")"),

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
        $.named_pattern,
        $.tuple_pattern,
        $.or_pattern,
        $.literal_pattern,
      ),

    identifier_pattern: ($) => $.identifier,

    wildcard_pattern: ($) => "_",

    enum_pattern: ($) =>
      prec.left(
        choice(
          seq($._type, "::", $.identifier, optional($.tuple_pattern)),
          seq(".", $.identifier, optional($.tuple_pattern)),
        ),
      ),

    named_pattern: ($) => seq(
      field("type", choice($._type, $.inferred_member_expression)), "{",
      commaSep(choice($.named_pattern_field, "..")), optional(","), "}"),

    named_pattern_field: ($) =>
      seq(field("name", $.identifier), optional(seq(":", field("pattern", $._pattern)))),

    tuple_pattern: ($) => seq("(", commaSep(choice($._pattern, "..")), ")"),

    or_pattern: ($) => prec.left(seq($._pattern, "|", $._pattern)),

    literal_pattern: ($) =>
      choice(
        seq(optional("-"), $.number_literal),
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

    f_string_literal: ($) =>
      seq('f"', repeat(choice($.f_string_escape, $.f_string_brace_escape, $.f_string_interpolation, $.f_string_text)), '"'),

    f_string_text: ($) =>
      token.immediate(/[^"\\{}]+/),

    f_string_escape: ($) =>
      $.escape_sequence,

    f_string_brace_escape: ($) =>
      token.immediate(choice("{{", "}}")),

    f_string_interpolation: ($) =>
      seq("{", $._expression, "}"),

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

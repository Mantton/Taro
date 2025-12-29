# Taro Language Grammar

This document describes the formal grammar of the Taro programming language in Extended BNF notation.

## Notation

```
<name>       ::=  rule definition
|                 alternation
[ ]               optional (0 or 1)
{ }               repetition (0 or more)
( )               grouping
'text'            literal terminal
/* comment */     comment
```

---

## Lexical Grammar

### Identifiers

```ebnf
<identifier>           ::= <letter> { <letter> | <digit> }
                         | '`' <escaped_identifier_char>+ '`'

<letter>               ::= 'a'..'z' | 'A'..'Z' | '_'
<digit>                ::= '0'..'9'
<hex_digit>            ::= <digit> | 'a'..'f' | 'A'..'F'
```

### Literals

```ebnf
<literal>              ::= <bool_literal>
                         | <nil_literal>
                         | <integer_literal>
                         | <float_literal>
                         | <string_literal>
                         | <rune_literal>

<bool_literal>         ::= 'true' | 'false'
<nil_literal>          ::= 'nil'

<integer_literal>      ::= <decimal_literal>
                         | <binary_literal>
                         | <octal_literal>
                         | <hex_literal>

<decimal_literal>      ::= <digit> { <digit> | '_' }
<binary_literal>       ::= '0b' ( '0' | '1' | '_' )+
<octal_literal>        ::= '0o' ( '0'..'7' | '_' )+
<hex_literal>          ::= '0x' ( <hex_digit> | '_' )+

<float_literal>        ::= <decimal_literal> '.' <decimal_literal> [ <exponent> ]
                         | <decimal_literal> <exponent>

<exponent>             ::= ( 'e' | 'E' ) [ '+' | '-' ] <decimal_literal>

<string_literal>       ::= '"' { <string_char> } '"'
<rune_literal>         ::= '\'' <rune_char> '\''
```

### Keywords

```
any         as          break       case        const       continue
defer       else        enum        export      extern      false
for         func        guard       if          extend      import
in          init        interface   let         loop        match
namespace   nil         operator    private     public      readonly
return      static      struct      true        type        var
where       while       mut
```

### Reserved Keywords

```
class       final       override    fileprivate protected
async       await       ref
```

### Operators and Punctuation

```ebnf
<operator>             ::= '+' | '-' | '*' | '/' | '%'
                         | '&' | '|' | '^' | '~' | '!'
                         | '<' | '>' | '<<' | '>>'
                         | '==' | '!=' | '<=' | '>=' | '==='
                         | '&&' | '||'
                         | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>='
                         | '->' | '=>'
                         | '..' | '..=' | '...'
                         | '?' | '?.' | '??'
                         | '|>'

<punctuation>          ::= '(' | ')' | '[' | ']' | '{' | '}'
                         | '.' | ',' | ':' | ';' | '@' | '_'
```

---

## Syntactic Grammar

### Modules and Files

```ebnf
<package>              ::= <module>

<module>               ::= { <file> } { <module> }

<file>                 ::= { <declaration> }
```

### Declarations

```ebnf
<declaration>          ::= { <attribute> } <visibility> <declaration_kind>

<declaration_kind>     ::= <import_declaration>
                         | <export_declaration>
                         | <struct_declaration>
                         | <enum_declaration>
                         | <interface_declaration>
                         | <function_declaration>
                         | <variable_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <extension_declaration>
                         | <extern_block>
                         | <namespace_declaration>

<visibility>           ::= [ 'public' | 'private' | 'protected' | 'fileprivate' ]
```

### Import and Export

```ebnf
<import_declaration>   ::= 'import' <use_tree>
<export_declaration>   ::= 'export' <use_tree>

<use_tree>             ::= <use_tree_path> <use_tree_kind>

<use_tree_path>        ::= <identifier> { '.' <identifier> }

<use_tree_kind>        ::= <use_tree_glob>
                         | <use_tree_simple>
                         | <use_tree_nested>

<use_tree_glob>        ::= '.' '*'
<use_tree_simple>      ::= [ 'as' <identifier> ]
<use_tree_nested>      ::= '.{' <use_tree_nested_list> '}'

<use_tree_nested_list> ::= <use_tree_nested_item> { ',' <use_tree_nested_item> } [ ',' ]
<use_tree_nested_item> ::= <identifier> [ 'as' <identifier> ]
```

### Struct Declaration

```ebnf
<struct_declaration>   ::= 'struct' <identifier> <generics> '{' <field_definitions> '}'

<field_definitions>    ::= { <field_definition> ';' }

<field_definition>     ::= { <attribute> } <visibility> <mutability> 
                           [ <label> ] <identifier> ':' <type>

<mutability>           ::= [ 'readonly' ]
<label>                ::= <identifier> ':'
```

### Enum Declaration

```ebnf
<enum_declaration>     ::= 'enum' <identifier> <generics> '{' { <enum_case> } '}'

<enum_case>            ::= 'case' <variant_list>

<variant_list>         ::= <variant> { ',' <variant> } [ ',' ]

<variant>              ::= <identifier> [ <variant_kind> ] [ '=' <expression> ]

<variant_kind>         ::= <tuple_variant>
<tuple_variant>        ::= '(' <tuple_variant_fields> ')'
<tuple_variant_fields> ::= <field_definition> { ',' <field_definition> } [ ',' ]
```

### Interface Declaration

```ebnf
<interface_declaration>::= 'interface' <identifier> <generics> [ <conformances> ]
                           '{' { <associated_declaration> } '}'

<associated_declaration>::= { <attribute> } <visibility> <associated_decl_kind>

<associated_decl_kind> ::= <function_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <operator_declaration>

<conformances>         ::= ':' <path_node> { '&' <path_node> }
```

### Extension Declaration

```ebnf
<extension_declaration>::= 'extend' <type> <generics> [ <conformances> ]
                           '{' { <associated_declaration> } '}'
```

### Function Declaration

```ebnf
<function_declaration> ::= 'func' <identifier> <generics> <function_signature> [ <block> ]

<function_signature>   ::= <function_prototype>

<function_prototype>   ::= '(' [ <function_parameters> ] ')' [ '->' <type> ]

<function_parameters>  ::= <function_parameter> { ',' <function_parameter> } [ ',' ]

<function_parameter>   ::= { <attribute> } [ <label> ] <identifier> ':' 
                           [ '...' ] <type> [ '=' <expression> ]
                         | <self_parameter>

<self_parameter>       ::= [ '&' [ 'const' ] ] 'self'
```

### Operator Declaration

```ebnf
<operator_declaration> ::= 'operator' <operator_kind> <generics> 
                           <function_signature> [ <block> ]

<operator_kind>        ::= '+' | '-' | '*' | '/' | '%'
                         | '<<' | '>>' | '&' | '|' | '^'
                         | '!' | '~'
                         | '+=' | '-=' | '*=' | '/=' | '%='
                         | '<<=' | '>>=' | '&=' | '|=' | '^='
                         | '&&' | '||'
                         | '<' | '>' | '<=' | '>=' | '==' | '!='
                         | '[' ']' | '[' ']' '='   /* index, index_assign */
```

### Variable and Constant Declarations

```ebnf
<variable_declaration> ::= ( 'let' | 'var' ) <pattern> [ ':' <type> ] [ '=' <expression> ]

<constant_declaration> ::= 'const' <identifier> ':' <type> [ '=' <expression> ]
```

### Type Alias Declaration

```ebnf
<type_alias_declaration> ::= 'type' <identifier> <generics> 
                             [ ':' <generic_bounds> ] 
                             [ '=' <type> ]
```

### Namespace Declaration

```ebnf
<namespace_declaration> ::= 'namespace' <identifier> '{' { <namespace_decl_item> } '}'

<namespace_decl_item>   ::= <function_declaration>
                          | <struct_declaration>
                          | <enum_declaration>
                          | <interface_declaration>
                          | <constant_declaration>
                          | <type_alias_declaration>
                          | <namespace_declaration>
                          | <import_declaration>
                          | <export_declaration>
```

### Extern Block

```ebnf
<extern_block>         ::= 'extern' <string_literal> '{' { <extern_declaration> } '}'

<extern_declaration>   ::= { <attribute> } <visibility> 'func' <identifier> 
                           <function_prototype>
```

### Attributes

```ebnf
<attribute_list>       ::= { <attribute> }
<attribute>            ::= '@' <identifier>
```

---

## Generics

```ebnf
<generics>             ::= [ <type_parameters> ] [ <where_clause> ]

<type_parameters>      ::= '<' <type_parameter_list> '>'
<type_parameter_list>  ::= <type_parameter> { ',' <type_parameter> } [ ',' ]

<type_parameter>       ::= <identifier> [ ':' <generic_bounds> ] [ '=' <type> ]
                         | 'const' <identifier> ':' <type> [ '=' <const_expression> ]

<where_clause>         ::= 'where' <requirement_list>
<requirement_list>     ::= <requirement> { ',' <requirement> }

<requirement>          ::= <conformance_requirement>
                         | <same_type_requirement>

<conformance_requirement> ::= <type> ':' <generic_bounds>
<same_type_requirement>   ::= <type> '==' <type>

<generic_bounds>       ::= <generic_bound> { '&' <generic_bound> }
<generic_bound>        ::= <path_node>

<type_arguments>       ::= '<' <type_argument_list> '>'
<type_argument_list>   ::= <type_argument> { ',' <type_argument> } [ ',' ]
<type_argument>        ::= <type> | <const_expression>
```

---

## Types

```ebnf
<type>                 ::= <type_kind> [ '?' ]   /* optional suffix */

<type_kind>            ::= <nominal_type>
                         | <pointer_type>
                         | <reference_type>
                         | <tuple_type>
                         | <function_type>
                         | <collection_type>
                         | <existential_type>
                         | <infer_type>
                         | <paren_type>

<nominal_type>         ::= <path>

<pointer_type>         ::= '*' [ 'const' ] <type>

<reference_type>       ::= '&' [ 'const' ] <type>

<tuple_type>           ::= '(' ')'
                         | '(' <type> ',' [ <type_list> ] ')'

<type_list>            ::= <type> { ',' <type> } [ ',' ]

<function_type>        ::= '(' <type_list> ')' '->' <type>

<collection_type>      ::= '[' <collection_type_inner> ']'

<collection_type_inner>::= <type>                        /* list: [T] */
                         | <type> ':' <type>             /* dict: [K:V] */
                         | <type> ';' <const_expression> /* array: [T;N] */

<existential_type>     ::= 'any' <path_node> { '&' <path_node> }

<infer_type>           ::= '_'

<paren_type>           ::= '(' <type> ')'
```

### Path

```ebnf
<path>                 ::= <path_segment> { '.' <path_segment> }

<path_segment>         ::= <identifier> [ <type_arguments> ]

<path_node>            ::= <path>
```

---

## Patterns

```ebnf
<pattern>              ::= <pattern_kind>

<pattern_kind>         ::= <wildcard_pattern>
                         | <rest_pattern>
                         | <identifier_pattern>
                         | <tuple_pattern>
                         | <path_pattern>
                         | <or_pattern>
                         | <literal_pattern>

<wildcard_pattern>     ::= '_'

<rest_pattern>         ::= '..'

<identifier_pattern>   ::= <identifier>

<tuple_pattern>        ::= '(' <pattern_list> ')'
<pattern_list>         ::= <pattern> { ',' <pattern> } [ ',' ]

<path_pattern>         ::= <pattern_path> [ <tuple_pattern> ]

<pattern_path>         ::= <path>                        /* qualified: Foo.Bar */
                         | '.' <identifier>              /* inferred: .Bar */

<or_pattern>           ::= <pattern> { '|' <pattern> }

<literal_pattern>      ::= <literal>
```

---

## Statements

```ebnf
<block>                ::= '{' { <statement> } '}'

<statement>            ::= <declaration_statement>
                         | <expression_statement>
                         | <variable_statement>
                         | <loop_statement>
                         | <while_statement>
                         | <for_statement>
                         | <return_statement>
                         | <break_statement>
                         | <continue_statement>
                         | <defer_statement>
                         | <guard_statement>

<declaration_statement>::= <function_declaration>

<expression_statement> ::= <expression> ';'

<variable_statement>   ::= <variable_declaration> ';'

<loop_statement>       ::= [ <label_def> ] 'loop' <block>

<while_statement>      ::= [ <label_def> ] 'while' <expression> <block>

<for_statement>        ::= [ <label_def> ] 'for' <pattern> 'in' <expression> 
                           [ 'where' <expression> ] <block>

<return_statement>     ::= 'return' [ <expression> ] ';'

<break_statement>      ::= 'break' [ <identifier> ] ';'

<continue_statement>   ::= 'continue' [ <identifier> ] ';'

<defer_statement>      ::= 'defer' <block>

<guard_statement>      ::= 'guard' <expression> 'else' <block>

<label_def>            ::= <identifier> ':'
```

---

## Expressions

### Expression Precedence (Lowest to Highest)

1. Assignment: `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`
2. Pipe: `|>`
3. Ternary: `? :`
4. Nil-coalescing: `??`
5. Range: `..`, `..=`
6. Logical OR: `||`
7. Logical AND: `&&`
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`, `===`
9. Bitwise OR: `|`
10. Bitwise XOR: `^`
11. Bitwise AND: `&`
12. Bit shift: `<<`, `>>`
13. Term: `+`, `-`
14. Factor: `*`, `/`, `%`
15. Cast: `as`
16. Prefix: `!`, `-`, `~`, `&`, `*`
17. Postfix: `.`, `()`, `[]`, `?`, `?.`
18. Primary

```ebnf
<expression>           ::= <assignment_expression>

<assignment_expression>::= <pipe_expression> [ <assignment_op> <expression> ]

<assignment_op>        ::= '=' | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>='

<pipe_expression>      ::= <ternary_expression> { '|>' <ternary_expression> }

<ternary_expression>   ::= <nil_coalesce_expr> [ '?' <expression> ':' <expression> ]

<nil_coalesce_expr>    ::= <range_expression> { '??' <range_expression> }

<range_expression>     ::= <or_expression> [ ( '..' | '..=' ) <or_expression> ]

<or_expression>        ::= <and_expression> { '||' <and_expression> }

<and_expression>       ::= <comparison_expr> { '&&' <comparison_expr> }

<comparison_expr>      ::= <bitor_expression> { <comparison_op> <bitor_expression> }

<comparison_op>        ::= '<' | '>' | '<=' | '>=' | '==' | '!=' | '==='

<bitor_expression>     ::= <bitxor_expression> { '|' <bitxor_expression> }

<bitxor_expression>    ::= <bitand_expression> { '^' <bitand_expression> }

<bitand_expression>    ::= <shift_expression> { '&' <shift_expression> }

<shift_expression>     ::= <term_expression> { ( '<<' | '>>' ) <term_expression> }

<term_expression>      ::= <factor_expression> { ( '+' | '-' ) <factor_expression> }

<factor_expression>    ::= <cast_expression> { ( '*' | '/' | '%' ) <cast_expression> }

<cast_expression>      ::= <prefix_expression> { 'as' <type> }

<prefix_expression>    ::= <prefix_op> <prefix_expression>
                         | <postfix_expression>

<prefix_op>            ::= '!' | '-' | '~' | '&' [ 'const' ] | '*'

<postfix_expression>   ::= <primary_expression> { <postfix_op> }

<postfix_op>           ::= '.' <identifier>                  /* member access */
                         | '.' <integer_literal>             /* tuple access */
                         | '(' <argument_list> ')'           /* call */
                         | '[' <expression> ']'              /* index */
                         | '<' <type_argument_list> '>'      /* specialization */
                         | '?'                               /* optional unwrap */
                         | '?.' <identifier>                 /* optional chain */

<argument_list>        ::= [ <argument> { ',' <argument> } [ ',' ] ]

<argument>             ::= [ <label> ] <expression>
```

### Primary Expressions

```ebnf
<primary_expression>   ::= <literal>
                         | <identifier>
                         | <tuple_expression>
                         | <array_expression>
                         | <dictionary_expression>
                         | <if_expression>
                         | <match_expression>
                         | <block_expression>
                         | <closure_expression>
                         | <struct_literal>
                         | <wildcard_expression>
                         | <binding_condition>
                         | <paren_expression>

<paren_expression>     ::= '(' <expression> ')'

<tuple_expression>     ::= '(' ')'
                         | '(' <expression> ',' [ <expression_list> ] ')'

<expression_list>      ::= <expression> { ',' <expression> } [ ',' ]

<array_expression>     ::= '[' ']'
                         | '[' <expression> { ',' <expression> } [ ',' ] ']'

<dictionary_expression>::= '[' <map_pair_list> ']'
                         | '[' ':' ']'

<map_pair_list>        ::= <map_pair> { ',' <map_pair> } [ ',' ]
<map_pair>             ::= <expression> ':' <expression>

<wildcard_expression>  ::= '_'
```

### Control Flow Expressions

```ebnf
<if_expression>        ::= 'if' <expression> <block_or_expr> 
                           [ 'else' <else_branch> ]

<else_branch>          ::= <if_expression>
                         | <block_or_expr>

<block_or_expr>        ::= <block>
                         | '=>' <expression>

<match_expression>     ::= 'match' <expression> '{' { <match_arm> } '}'

<match_arm>            ::= 'case' <pattern> [ 'if' <expression> ] 
                           ( <block_or_expr> | '=>' <expression> )

<block_expression>     ::= <block>
```

### Closure Expression

```ebnf
<closure_expression>   ::= <closure_params> [ '->' <type> ] <closure_body>

<closure_params>       ::= '|' [ <closure_param_list> ] '|'
                         | '||'

<closure_param_list>   ::= <closure_param> { ',' <closure_param> } [ ',' ]

<closure_param>        ::= <identifier> [ ':' <type> ]

<closure_body>         ::= <block>
                         | <expression>
```

### Struct Literal

```ebnf
<struct_literal>       ::= <path> '{' [ <field_init_list> ] '}'

<field_init_list>      ::= <field_init> { ',' <field_init> } [ ',' ]

<field_init>           ::= [ <label> ] <expression>
                         | <identifier>   /* shorthand: foo instead of foo: foo */

**Note on Disambiguation**: In control flow conditions (e.g., `if User { ... }`), a struct literal is disallowed if it is ambiguous with a block. The parser uses a heuristic to determine if a block-like structure is intended to be a struct literal:
- It is treated as a struct literal if it contains keys followed by newlines/commas (e.g., `{ key: val, }` or `{ key, }`).
- Otherwise, it is parsed as a block.
- If it looks like a struct literal but appears in a restricted context (like an `if` condition), a specific error is raised (`ParserError::DisallowedStructLiteral`).
```

### Binding Conditions

```ebnf
<binding_condition>    ::= 'case' <pattern> '=' <expression>
                         | 'let' <pattern> '=' <expression>
                         | 'let' <pattern>   /* shorthand optional binding */
```

---

## Automatic Semicolon Insertion

Taro uses automatic semicolon insertion (ASI). Semicolons are automatically inserted after tokens that can end a statement when followed by a newline, unless the next line begins with a continuation operator.

**Tokens that can end a statement:**
- Identifiers, literals (`true`, `false`, `nil`)
- `break`, `continue`, `return`
- `)`, `]`, `}`
- `?`, `.*`

**Line continuation starters (suppress ASI):**
- Binary operators: `+`, `-`, `/`, `%`, `|`, `^`, `&&`, `||`
  - Note: `&` and `*` are **not** treated as continuation starters because they have common unary uses (reference and dereference/pointer) that should start new statements
- Comparison operators: `<`, `>`, `<=`, `>=`, `==`, `!=`, `===`
- Shifts: `<<`, `>>`
- Assignment operators
- Member/range/optional: `.`, `..`, `...`, `?.`, `??`
- Pipe and arrows: `|>`, `->`, `=>`
- Keywords: `as`, `in`

---

## Comments

```ebnf
<line_comment>         ::= '//' { <any_char> } <newline>
<block_comment>        ::= '/*' { <any_char> } '*/'
```

---

## Reserved for Future

The following are reserved for future use:
- `class`, `final`, `override`
- `async`, `await`
- `ref`

---

## Edge Cases and Notes

### Separator and Trailing Comma Rules

Different constructs use different separators and have different trailing separator policies:

| Construct | Separator | Trailing Allowed? | ASI Risk |
|-----------|-----------|-------------------|----------|
| Struct fields | `;` | Yes | None (semicolons match ASI) |
| Enum cases | `;` | Yes | None |
| Enum variants (in a case) | `,` | **Yes** | Low |
| Function parameters | `,` | Yes | None |
| Type parameters | `,` | Yes | None |
| Type arguments | `,` | Yes | Low |
| Call arguments | `,` | **Yes** | **HIGH** - comma required on each line |
| Tuple expressions | `,` | **Yes** | **HIGH** - comma required on each line |
| Array literals | `,` | **Yes** | **HIGH** - comma required on each line |
| Dictionary literals | `,` | **Yes** | **HIGH** - comma required on each line |
| Struct literal fields | `,` | Yes | Trailing comma **required** for multiline |
| Import nested items | `,` | Yes | None |
| Closure parameters | `,` | Yes | None |
| Pattern lists | `,` | Yes | None |
| Match arms | implicit (newline/`;`) | N/A | None |

### Multiline Constructs and ASI Interaction

**Struct Fields**: Since struct fields use semicolons as separators and ASI inserts semicolons after identifiers and closing delimiters on newlines, multiline struct definitions work naturally:
```
struct Point {
    x: int       // ASI inserts `;` here
    y: int       // ASI inserts `;` here
}
```

**Call Arguments**: Call arguments do **not** allow trailing commas. For multiline calls, you must place the comma at the end of each line (before the newline):
```
foo(
    a,           // comma required
    b,           // comma required
    c            // no trailing comma
)
```

**Array/Dictionary Literals**: Similar to call arguments, trailing commas are **not** allowed:
```
let arr = [
    1,
    2,
    3              // no trailing comma
]
```

**Struct Literals**: Trailing commas **are** allowed, and in multiline struct literals, **commas are required after each field** to prevent ASI from inserting semicolons:
```
// WRONG - ASI inserts `;` after string literal
let user = User {
    id: 1,
    name: "John"       // ASI inserts `;` here, causing parse error
}

// CORRECT - comma prevents ASI
let user = User {
    id: 1,
    name: "John",      // comma required (also serves as trailing comma)
}
```

### Single-Element Tuples vs Parenthesized Expressions

A single expression in parentheses is parsed as a parenthesized expression, **not** a tuple:
```
(a)      // parenthesized expression, NOT a tuple
(a, b)   // two-element tuple
()       // empty tuple (unit)
```

Note: Single-element tuples are not currently supported in the grammar.

### Struct Literal Disambiguation

Struct literals (`Foo { ... }`) can be ambiguous with blocks in certain contexts. In expression positions where blocks are expected (like `if` conditions, `for` iterators), struct literals are disallowed:
```
if condition { ... }           // block, not struct literal
let x = Foo { field: value }   // struct literal OK here
```

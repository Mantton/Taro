# Taro Language Grammar

This reference describes the current Taro parser and supported language forms
in Extended BNF notation. Semantic constraints are stated alongside the rules;
parsing a form alone does not establish that it is well typed or that every
accepted form is an intentional language feature. Where implementation and
documented intent disagree, implementation limitations are identified explicitly.
The [syntax guide](guide/syntax/README.md) provides examples.

## Notation

```
<name>       ::=  rule definition
|                 alternation
[ ]               optional (0 or 1)
{ }               repetition (0 or more)
( )               grouping
'text'            literal terminal
/* comment */     comment
? description ?   terminal described in prose
item+             one or more occurrences
```

---

## Lexical Grammar

### Identifiers

```ebnf
<identifier>           ::= <letter> { <letter> | <digit> }
                         | '`' { <escaped_identifier_char> } '`'

<letter>               ::= 'a'..'z' | 'A'..'Z' | '_'
<digit>                ::= '0'..'9'
<hex_digit>            ::= <digit> | 'a'..'f' | 'A'..'F'
<escaped_identifier_char> ::= ? any character except backtick or newline ?
```

Unescaped keywords and the standalone `_` token are excluded from identifiers.

### Literals

```ebnf
<literal>              ::= <bool_literal>
                         | <nil_literal>
                         | <integer_literal>
                         | <float_literal>
                         | <string_literal>
                         | <f_string_literal>
                         | <rune_literal>

<bool_literal>         ::= 'true' | 'false'
<nil_literal>          ::= 'nil'

<integer_literal>      ::= ( <decimal_literal> | <binary_literal>
                           | <octal_literal> | <hex_literal> ) [ <integer_suffix> ]
<integer_suffix>       ::= '_' ( 'i' | 'I' | 'u' | 'U' ) ( '8' | '16' | '32' | '64' )

<decimal_literal>      ::= <digit> { <digit> | '_' }
<binary_literal>       ::= '0b' ( '0' | '1' | '_' )+
<octal_literal>        ::= '0o' ( '0'..'7' | '_' )+
<hex_literal>          ::= '0x' ( <hex_digit> | '_' )+

<float_literal>        ::= <decimal_literal> '.' [ <decimal_literal> [ <exponent> ] ]
                         | <decimal_literal> <exponent>

<exponent>             ::= ( 'e' | 'E' ) [ '+' | '-' ] <decimal_literal>

<string_literal>       ::= '"' { <string_char> } '"'
<f_string_literal>     ::= 'f"' { <f_string_item> } '"'
<f_string_item>        ::= <f_string_char>
                         | '{{'
                         | '}}'
                         | '{' <expression> '}'
<rune_literal>         ::= '\'' <rune_char> '\''

<string_char>          ::= <escape> | ? any character except quote, backslash, LF or CR ?
<f_string_char>        ::= <escape> | ? any character except quote, backslash, braces, LF or CR ?
<rune_char>            ::= <escape> | ? one Unicode scalar except quote, backslash, LF, CR or tab ?
<escape>               ::= '\\' ( 'n' | 'r' | 't' | '0' | '\\' | '"' | '\'' )
                         | '\\x' <hex_digit> <hex_digit>
                         | '\\u{' <hex_digit> { <hex_digit> | '_' } '}'
```

Digits must be valid for their base. Integer suffixes name fixed-width types.
Unicode escapes contain one to six hexadecimal digits (underscores do not
count) and must denote a Unicode scalar value; `\xNN` escapes are ASCII only.
Source files accept LF and CRLF line endings. Each CRLF pair is normalized
to LF once before tokenization. Remaining bare CR characters are whitespace
between tokens, not line breaks. Strings and f-strings occupy one source line.

### Keywords

```
any         as          is          break       case        const       continue
async       await       defer       else        enum        export      extern      false
for         func        guard       if          impl        import
in          init        interface   let         loop        match
mod         mut         namespace   nil         operator    private
public      readonly    return      static      struct      true
type        unsafe      var         where       while
```

### Reserved Keywords

```
class       final       override    fileprivate protected ref
```

### Contextual Keywords

`get` and `set` are interpreted as contextual keywords inside computed-property
accessor blocks. `move` introduces a move closure, and `some` introduces an
opaque return type. These words remain valid identifiers in other contexts.

### Operators and Punctuation

```ebnf
<operator>             ::= '+' | '-' | '*' | '/' | '%'
                         | '='
                         | '&' | '|' | '^' | '~' | '!'
                         | '<' | '>' | '<<' | '>>'
                         | '==' | '!=' | '<=' | '>='
                         | '&&' | '||'
                         | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>='
                         | '->' | '=>'
                         | '..' | '..=' | '...'
                         | '?' | '?.' | '??'
                         | '|>'

<punctuation>          ::= '(' | ')' | '[' | ']' | '{' | '}'
                         | '.' | ',' | ':' | ';' | '@' | '#' | '_'
```

---

## Syntactic Grammar

### Modules and Files

```ebnf
<package>              ::= <module>

<module>               ::= { <file> } { <module> }

<file>                 ::= { <declaration> | <module_metadata_declaration> }

<module_metadata_declaration>
                       ::= { <attribute> } <visibility> 'mod' <identifier> ';'
```

A `<module_metadata_declaration>` attaches metadata — visibility and
attributes such as `@cfg(...)` — to the enclosing implicit directory module.
It does not introduce a module. The following constraints apply:

- Only allowed at the top level of a non-root file.
- The identifier must match the enclosing directory's module name.
- At most one `mod` declaration per module (across all files in the
  directory). Duplicates are rejected.
- When omitted, the module is implicitly public.
- When the attached `@cfg(...)` evaluates to false, the module is removed
  from its parent's submodule list during configuration evaluation.

### Declarations

```ebnf
<declaration>          ::= { <attribute> } <visibility> <declaration_kind> ';'

<declaration_kind>     ::= <import_declaration>
                         | <export_declaration>
                         | <struct_declaration>
                         | <enum_declaration>
                         | <interface_declaration>
                         | <function_declaration>
                         | <static_variable_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <impl_declaration>
                         | <extern_block>
                         | <extern_function>
                         | <namespace_declaration>

<visibility>           ::= [ 'public' | 'private' ]
```

Omitted visibility is public. Declarations, including declarations with bodies,
need a terminating semicolon, which is normally supplied by ASI.

### Import and Export

```ebnf
<import_declaration>   ::= 'import' <use_tree>
<export_declaration>   ::= 'export' <use_tree>

<use_tree>             ::= <use_tree_path> <use_tree_kind>

<use_tree_path>        ::= <identifier> { '.' <identifier> }

<use_tree_kind>        ::= <use_tree_glob>
                         | <use_tree_simple>
                         | <use_tree_nested>

<use_tree_glob>        ::= '.*'
<use_tree_simple>      ::= [ 'as' <identifier> ]
<use_tree_nested>      ::= '.{' <use_tree_nested_list> '}'

<use_tree_nested_list> ::= <use_tree_nested_item> { ',' <use_tree_nested_item> } [ ',' ]
<use_tree_nested_item> ::= <identifier> [ 'as' <identifier> ]
```

### Struct Declaration

```ebnf
<struct_declaration>   ::= 'struct' <identifier> [ <type_parameters> ]
                           [ <conformances> ] [ <where_clause> ]
                           '{' <struct_fields> '}'

<struct_fields>        ::= [ <struct_field> { ';' <struct_field> } [ ';' ] ]

<struct_field>         ::= <visibility> [ 'readonly' ] <identifier> ':' <type>
```

### Enum Declaration

```ebnf
<enum_declaration>     ::= 'enum' <identifier> [ <type_parameters> ]
                           [ <conformances> ] [ <where_clause> ]
                           '{' [ <enum_case> { ';' <enum_case> } [ ';' ] ] '}'

<enum_case>            ::= 'case' <variant_list>

<variant_list>         ::= <variant> { ',' <variant> }

<variant>              ::= <identifier> [ <variant_kind> ] [ '=' <expression> ]

<variant_kind>         ::= <tuple_variant>
<tuple_variant>        ::= '(' <tuple_variant_fields> ')'
<tuple_variant_fields> ::= [ <tuple_field> { ',' <tuple_field> } [ ',' ] ]
<tuple_field>          ::= <visibility> [ 'readonly' ] [ <label> ] <type>
```

### Interface Declaration

```ebnf
<interface_declaration>::= 'interface' <identifier> [ <type_parameters> ]
                           [ <where_clause> ] [ <conformances> ]
                           '{' { <interface_associated_declaration> } '}'

<interface_associated_declaration>
                       ::= { <attribute> } <visibility> <interface_associated_decl_kind> ';'

<interface_associated_decl_kind>
                       ::= <function_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <interface_property_declaration>

<interface_property_declaration>
                       ::= 'var' <identifier> ':' <type>
                           '{' ( <getter_requirement> [ <setter_requirement> ]
                               | <setter_requirement> <getter_requirement> ) '}'

<getter_requirement>   ::= 'get' '(' <self_parameter> ')' [ 'async' ] [ '->' <type> ] [ <block> ]

<setter_requirement>   ::= 'set' '(' '&' 'mut' 'self' ',' <identifier> ':' <type> ')'
                           [ <block> ]

<conformances>         ::= ':' <path_node> { ',' <path_node> }
```

### Implementation Declaration

```ebnf
<impl_declaration>     ::= 'impl' [ <type_parameters> ] <type> [ 'for' <type> ]
                           [ <where_clause> ] '{' { <impl_associated_declaration> } '}'

<impl_associated_declaration>
                       ::= { <attribute> } <visibility> <impl_associated_decl_kind> ';'

<impl_associated_decl_kind>
                       ::= <function_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <computed_property_declaration>

<computed_property_declaration>
                       ::= 'var' <identifier> ':' <type>
                           '{' ( <getter_accessor> [ <setter_accessor> ]
                               | <setter_accessor> <getter_accessor> ) '}'

<getter_accessor>      ::= 'get' '(' <self_parameter> ')' [ 'async' ] [ '->' <type> ] <block>

<setter_accessor>      ::= 'set' '(' '&' 'mut' 'self' ',' <identifier> ':' <type> ')'
                           <block>
```

### Function Declaration

```ebnf
<function_declaration> ::= [ 'unsafe' ] 'func' <identifier> [ <type_parameters> ]
                           <function_signature> [ <where_clause> ] [ <block> ]

<function_signature>   ::= <function_prototype>

<function_prototype>   ::= '(' [ <function_parameters> ] ')' [ 'async' ] [ '->' <type> ]

<function_parameters>  ::= <function_parameter> { ',' <function_parameter> } [ ',' ]

<function_parameter>   ::= { <attribute> } <parameter_name> ':'
                           <type> [ '...' ] [ '=' <expression> ]
                         | <self_parameter>

<parameter_name>       ::= <identifier> [ <identifier> ]
                         | '_' [ <identifier> ]
<self_parameter>       ::= [ '&' [ 'const' | 'mut' ] ] 'self'
<label>                ::= <identifier> ':'
```

Function bodies are required outside interfaces and extern declarations.
`unsafe` precedes `func`, after visibility. Variadic parameters have `Span[T]`
inside the function.

`operator` is reserved and has no declaration form. Operator overloading uses
standard-library interfaces; see [Operator Overloading](guide/syntax/declarations.md#operator-overloading).

### Static Variable and Constant Declarations

```ebnf
<static_variable_declaration>
                       ::= 'static' ( 'let' | 'var' ) <identifier> ':' <type> '=' <expression>

<variable_declaration> ::= ( 'let' | 'var' ) <local_pattern> [ ':' <type> ] [ '=' <expression> ]
<local_pattern>        ::= <identifier_pattern> | <wildcard_pattern> | <tuple_pattern>
                         | <reference_pattern>

<constant_declaration> ::= 'const' <identifier> ':' <type> [ '=' <expression> ]
```

Local binding patterns must be irrefutable, including nested tuple and
reference patterns.

### Type Alias Declaration

```ebnf
<type_alias_declaration> ::= 'type' <identifier> [ <type_parameters> ]
                             [ ':' <generic_bounds> ]
                             [ '=' <type> { '&' <path_node> } ] [ <where_clause> ]
```

### Namespace Declaration

```ebnf
<namespace_declaration> ::= 'namespace' <identifier> [ '{' { <namespace_decl_item> } '}' ]

<namespace_decl_item>   ::= { <attribute> } <visibility> <namespace_decl_kind> ';'

<namespace_decl_kind>   ::= <function_declaration>
                          | <struct_declaration>
                          | <enum_declaration>
                          | <interface_declaration>
                          | <static_variable_declaration>
                          | <constant_declaration>
                          | <type_alias_declaration>
                          | <namespace_declaration>
                          | <import_declaration>
                          | <export_declaration>
```

### Extern Block

```ebnf
<extern_block>         ::= 'extern' <string_literal> '{' { <extern_declaration> } '}'

<extern_declaration>   ::= { <attribute> } <visibility> [ 'unsafe' ] 'func'
                           <identifier> [ <type_parameters> ] <function_prototype>
                           [ <where_clause> ] ';'
                         | 'type' <identifier>

<extern_function>      ::= 'extern' <string_literal> [ 'unsafe' ] 'func'
                           <identifier> [ <type_parameters> ] <function_prototype>
                           [ <where_clause> ]
```

### Attributes

```ebnf
<attribute_list>       ::= { <attribute> }
<attribute>            ::= '@' <identifier> [ '(' [ <attribute_args> ] ')' ]
                         | '@cfg' '(' <cfg_expression> ')'
<attribute_args>       ::= <attribute_arg> { ',' <attribute_arg> } [ ',' ]
<attribute_arg>        ::= <attribute_literal>
                         | <identifier> [ '=' <attribute_literal> ]
<attribute_literal>    ::= <bool_literal> | <nil_literal> | <integer_literal>
                         | <float_literal> | <string_literal> | <rune_literal>
```

---

## Generics

```ebnf
<type_parameters>      ::= '[' [ <type_parameter_list> ] ']'
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

<type_arguments>       ::= '[' [ <type_argument_list> ] ']'
<callable_type_arguments>
                       ::= '(' [ <type_list> ] ')' '->' <type>
<type_argument_list>   ::= <type_argument> { ',' <type_argument> } [ ',' ]
<type_argument>        ::= <type> | <const_expression> | <identifier> '=' <type>
<const_expression>     ::= <expression>
```

---

Const expressions are restricted by constant evaluation (see
[Constants](guide/syntax/declarations.md#constant-declaration)); general calls
and runtime values are not constant expressions. Associated bindings use
`Iterator[Element = int32]`. Function/impl `where` clauses follow the signature
or target; struct/enum clauses follow conformances. Interface clauses precede
superinterfaces.

Callable shorthand always packs its argument list into a tuple:
`Fn(A) -> R` means `Fn[(A,), R]`, while `Fn((A, B)) -> R` means
`Fn[((A, B),), R]`. See [Callable Interface Shorthand](guide/syntax/types.md#callable-interface-shorthand)
for legacy scalar spelling, generic argument packs, and existential calls.

## Types

```ebnf
<type>                 ::= <type_kind> { '?' }   /* optional suffix */

<type_kind>            ::= <nominal_type>
                         | <pointer_type>
                         | <reference_type>
                         | <tuple_type>
                         | <function_type>
                         | <collection_type>
                         | <existential_type>
                         | <opaque_return_type>
                         | <infer_type>
                         | <paren_type>
                         | <never_type>
                         | <qualified_type>

<nominal_type>         ::= <path>

<pointer_type>         ::= '*' [ 'const' | 'mut' ] <type>

<reference_type>       ::= '&' [ 'const' | 'mut' ] <type>

<tuple_type>           ::= '(' ')'
                         | '(' <type> ',' ')'                /* one-element tuple */
                         | '(' <type> ',' <type_list> ')'

<type_list>            ::= <type> { ',' <type> } [ ',' ]

<function_type>        ::= '(' [ <type_list> ] ')' '->' <type>

<collection_type>      ::= '[' <collection_type_inner> ']'

<collection_type_inner>::= <type>                        /* list: [T] */
                         | <type> ':' <type>             /* dict: [K:V] */
                         | <type> ';' <const_expression> /* array: [T;N] */

<existential_type>     ::= 'any' <path_node> { '&' <path_node> }

<opaque_return_type>   ::= 'some' <path_node> { '&' <path_node> }

<infer_type>           ::= '_'

<paren_type>           ::= '(' <type> ')'

<never_type>           ::= '!'
<qualified_type>       ::= '(' <type> 'as' <type> ')' '.' <identifier>
```

Unqualified `&T` and `*T` are immutable; `const` is an explicit synonym and
`mut` requests mutable access. `some` is restricted to supported return-type
positions. `(T as Interface).Member` selects an associated type explicitly.

### Path

```ebnf
<path>                 ::= <path_segment> { '.' <path_segment> }

<path_segment>         ::= <identifier> [ <type_arguments> ]
                         | <callable_name> <callable_type_arguments>
<callable_name>        ::= 'Fn' | 'FnMut' | 'FnOnce'
                         | 'AsyncFn' | 'AsyncFnMut' | 'AsyncFnOnce'

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
                         | <literal_pattern>
                         | <reference_pattern>

<wildcard_pattern>     ::= '_'

<rest_pattern>         ::= '..'

<identifier_pattern>   ::= <identifier>

<tuple_pattern>        ::= '(' [ <pattern_list> ] ')'
<pattern_list>         ::= <pattern> { ',' <pattern> } [ ',' ]

<path_pattern>         ::= <pattern_path> [ <tuple_pattern> ]

<pattern_path>         ::= <path>                        /* qualified: Foo.Bar */
                         | '.' <identifier>              /* inferred: .Bar */

<match_pattern>        ::= <pattern> { '|' <pattern> }

<literal_pattern>      ::= <literal>
                         | '-' ( <integer_literal> | <float_literal> )

<reference_pattern>    ::= '&' [ 'const' | 'mut' ] <pattern>
```

---

Or-patterns belong at the top level of match arms. Rest patterns are accepted
inside tuple and variant-payload patterns. Explicit `&pattern` removes a
reference layer; it does not itself make inner bindings references. Qualified
path patterns resolve enum variants, not arbitrary constants. Numeric literal
patterns may have a leading minus sign, and integer patterns must fit their
type. Arbitrary expressions and f-strings with interpolation are rejected;
use a guard for those comparisons. Local reference bindings are described in
[Reference Pattern](guide/syntax/patterns.md#reference-pattern).

## Statements

```ebnf
<block>                ::= '{' { <statement> ';' } [ <statement> ] '}'

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

<declaration_statement>::= { <attribute> } <visibility> <function_declaration>

<expression_statement> ::= <expression>

<variable_statement>   ::= <variable_declaration>

<loop_statement>       ::= [ <label_def> ] 'loop' <block>

<while_statement>      ::= [ <label_def> ] 'while' <expression> <block>

<for_statement>        ::= [ <label_def> ] 'for' [ 'await' ] <pattern> 'in' <expression>
                           [ 'where' <expression> ] <block>

<return_statement>     ::= 'return' [ <expression> ]

<break_statement>      ::= 'break' [ <identifier> ]

<continue_statement>   ::= 'continue' [ <identifier> ]

<defer_statement>      ::= 'defer' <block>

<guard_statement>      ::= 'guard' <expression> 'else' <block>

<label_def>            ::= <identifier> ':'
```

---

A final non-declaration statement may omit its semicolon before `}`. A local
function declaration still requires one. `guard` and `if`/`while` conditions
are boolean; binding conditions produce a boolean and introduce bindings.
`for await` is restricted to async contexts.

## Expressions

### Expression Precedence (Lowest to Highest)

1. Assignment: `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`
2. Pipe: `|>`
3. Ternary: `? :`
4. Nil-coalescing: `??`
5. Range: `..`, `..=`
6. Logical OR: `||`
7. Logical AND: `&&`
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`
9. Bitwise OR: `|`
10. Bitwise XOR: `^`
11. Bitwise AND: `&`
12. Bit shift: `<<`, `>>`
13. Term: `+`, `-`
14. Factor: `*`, `/`, `%`
15. Cast / Type Assertion: `as`, `as?`, `is`
16. Prefix: `!`, `-`, `~`, `&`, `*`
17. Postfix: `.`, `()`, `[]`, `!`, `?.`
18. Primary

```ebnf
<expression>           ::= <assignment_expression>

<assignment_expression>::= <pipe_expression> [ <assignment_op> <pipe_expression> ]

<assignment_op>        ::= '=' | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>='

<pipe_expression>      ::= <ternary_expression> { '|>' <ternary_expression> }

<ternary_expression>   ::= <nil_coalesce_expr> [ '?' <ternary_expression> ':' <ternary_expression> ]

<nil_coalesce_expr>    ::= <range_expression> [ '??' <nil_coalesce_expr> ]

<range_expression>     ::= <or_expression> [ ( '..' | '..=' ) <or_expression> ]

<or_expression>        ::= <and_expression> { '||' <and_expression> }

<and_expression>       ::= <comparison_expr> { '&&' <comparison_expr> }

<comparison_expr>      ::= <bitor_expression> { <comparison_op> <bitor_expression> }

<comparison_op>        ::= '<' | '>' | '<=' | '>=' | '==' | '!='

<bitor_expression>     ::= <bitxor_expression> { '|' <bitxor_expression> }

<bitxor_expression>    ::= <bitand_expression> { '^' <bitand_expression> }

<bitand_expression>    ::= <shift_expression> { '&' <shift_expression> }

<shift_expression>     ::= <term_expression> { ( '<<' | '>>' ) <term_expression> }

<term_expression>      ::= <factor_expression> { ( '+' | '-' ) <factor_expression> }

<factor_expression>    ::= <cast_expression> { ( '*' | '/' | '%' ) <cast_expression> }

<cast_expression>      ::= <prefix_expression> { ( 'as' [ '?' ] | 'is' ) <type> }

<prefix_expression>    ::= <prefix_op> <prefix_expression>
                         | <postfix_expression>

<prefix_op>            ::= '!' | '-' | '~' | '&' [ 'const' | 'mut' ] | '*'

<postfix_expression>   ::= <primary_expression> { <postfix_op> }

<postfix_op>           ::= '.' <identifier>                  /* member access */
                         | '.' <integer_literal>             /* tuple access */
                         | '(' <argument_list> ')'           /* call */
                         | '[' <type_argument_list> ']'      /* specialization */
                         | '!'                               /* Optional/Result propagation */
                         | '?.' <identifier>                 /* optional chain */

<argument_list>        ::= [ <argument> { ',' <argument> } [ ',' ] ]

<argument>             ::= [ <label> ] <pipe_expression>
```

Postfix `!` propagates only `Optional[T]` and `Result[T, E]`. `await` remains a
keyword that consumes the following expression, so propagation of an awaited
value is written as `(await expr)!`. Likewise use `(await expr) + value` to
operate on the result. Assignments do not chain without explicit grouping.
Nil coalescing is right-associative.

### Primary Expressions

```ebnf
<primary_expression>   ::= <literal>
                         | <identifier>
                         | '.' <identifier>                /* inferred member */
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
                         | <unsafe_expression>
                         | <await_expression>
                         | <cfg_check>
                         | <return_statement>
                         | <break_statement>
                         | <continue_statement>

<paren_expression>     ::= '(' <expression> ')'

<tuple_expression>     ::= '(' ')'
                         | '(' <expression> ',' ')'                /* one-element tuple */
                         | '(' <expression> ',' <expression_list> ')'

<expression_list>      ::= <expression> { ',' <expression> } [ ',' ]

<array_expression>     ::= '[' ']'
                         | '[' <expression> { ',' <expression> } [ ',' ] ']'
                         | '[' <expression> ';' <const_expression> ']'   /* repeat */

<dictionary_expression>::= '[' <map_pair_list> ']'
                         | '[' ':' ']'

<map_pair_list>        ::= <map_pair> { ',' <map_pair> } [ ',' ]
<map_pair>             ::= <expression> ':' <expression>

<wildcard_expression>  ::= '_'
<unsafe_expression>    ::= 'unsafe' <block>
<await_expression>     ::= 'await' <expression>
<cfg_check>            ::= '#cfg' '(' <cfg_expression> ')'
```

`_` expressions are restricted to one direct argument placeholder in a pipe
call. Binding conditions are restricted to `if`/`while`/`guard` conditions.
Repeat literals require a compile-time count and construct fixed-size arrays.

### Control Flow Expressions

```ebnf
<if_expression>        ::= 'if' <expression> <block> [ 'else' <else_branch> ]

<else_branch>          ::= <if_expression> | <block>

<match_expression>     ::= 'match' <expression> '{' { <match_arm> } '}'

<match_arm>            ::= 'case' <match_pattern> [ 'if' <expression> ]
                           '=>' <expression> ';'
                         | '_' '=>' <expression> ';'

<block_expression>     ::= <block>
```

### Closure Expression

```ebnf
<closure_expression>   ::= [ 'move' ] <closure_params>
                           ( 'async' [ '->' <type> ] <block>
                           | '->' <type> 'async' <block>
                           | [ '->' <type> ] <closure_body> )

<closure_params>       ::= '|' [ <closure_param_list> ] '|'
                         | '||'

<closure_param_list>   ::= <closure_param> { ',' <closure_param> } [ ',' ]

<closure_param>        ::= { <attribute> } <identifier> [ ':' <type> [ '...' ] ]

<closure_body>         ::= <block>
                         | <expression>
```

### Struct Literal

```ebnf
<struct_literal>       ::= <path> '{' [ <field_init_list> ] '}'

<field_init_list>      ::= <field_init> { ',' <field_init> } [ ',' ]

<field_init>           ::= [ <label> ] <expression>
                         | <identifier>   /* shorthand: foo instead of foo: foo */
```

Bare struct literals are restricted in `if`/`while`/`guard` conditions,
`for` iterators/filters, and `match` scrutinees. Parentheses, call arguments,
collection literals, block expressions, and f-string interpolations permit
struct literals inside their delimiters. The surrounding restriction resumes
after the closing delimiter.

### Binding Conditions

```ebnf
<binding_condition>    ::= 'case' <pattern> '=' <expression>
                         | 'let' <identifier> '=' <expression>
                         | 'let' <identifier>   /* shorthand optional binding */
```

---

## Conditional Compilation

```ebnf
<cfg_expression>       ::= <cfg_and> { '||' <cfg_and> }
<cfg_and>              ::= <cfg_unary> { '&&' <cfg_unary> }
<cfg_unary>            ::= '!' <cfg_unary> | '(' <cfg_expression> ')'
                         | <identifier> [ '(' <string_literal> ')' ]
```

`@cfg(...)` controls declaration inclusion; `#cfg(...)` is a compile-time
boolean expression. Supported flags are `debug`, `test`, and `bench`; valued
predicates are `os`, `arch`, `family`, and `profile`. Unknown predicates evaluate
to false. The legacy attribute form `@cfg(target_os = "linux")` is also
accepted. A file can start with `//+cfg os("linux")`; file-level predicates
support valued predicates and boolean operators, but not the bare flags.

---

## Automatic Semicolon Insertion

Taro uses automatic semicolon insertion (ASI). Semicolons are automatically inserted after tokens that can end a statement at a newline or end of file, unless the next line begins with a continuation operator.

**Tokens that can end a statement:**
- Identifiers, literals (`true`, `false`, `nil`)
- `break`, `continue`, `return`
- `)`, `]`, `}`
- `?`, `!`, `.*`

**Line continuation starters (suppress ASI):**
- Binary operators: `+`, `-`, `/`, `%`, `|`, `^`, `&&`, `||`
  - Note: `&` and `*` are **not** treated as continuation starters because they have common unary uses (reference and dereference/pointer) that should start new statements
- Comparison operators: `<`, `>`, `<=`, `>=`, `==`, `!=`
- Shifts: `<<`, `>>`
- Assignment operators
- Member/range/optional: `.`, `..`, `..=`, `...`, `?.`, `??`
- Pipe and arrows: `|>`, `->`, `=>`
- Keywords: `as`, `is`, `in`

---

## Comments

```ebnf
<line_comment>         ::= '//' { <line_comment_char> } [ <newline> ]
<line_comment_char>    ::= ? any character except LF ?
<newline>              ::= ? LF ?
<block_comment>        ::= '/*' { <block_comment> | <block_comment_char> } '*/'
<block_comment_char>   ::= ? a character not starting /* or */ ?
```

---

Block comments nest. Every opening delimiter must be closed, including those
inside apparent quoted text within a comment. An unterminated comment is an
error. The comment grammar operates after CRLF normalization.

## Reserved for Future

The following are reserved for future use:
- `class`, `final`, `override`
- `ref`
- `fileprivate`, `protected`

---

## Comma and Semicolon Rules

### Semicolon-Separated Lists

Constructs that use semicolons as separators work naturally with ASI:

| Construct | Separator |
|-----------|-----------|
| Struct fields | `;` |
| Enum cases | `;` |
| Match arms | implicit (newline inserts `;`) |

### Comma-Separated Lists and ASI

For delimited comma-separated lists, **commas are required before newlines**,
including after the final element when the closing delimiter is on the next
line. A trailing comma is optional only when the delimiter follows on the same
line. Enum variants within one `case` do not accept a trailing comma.

| Construct | Separator | Trailing Comma |
|-----------|-----------|----------------|
| Enum variants (in a case) | `,` | Not accepted |
| Function parameters | `,` | Optional |
| Type parameters | `,` | Optional |
| Type arguments | `,` | Optional |
| Call arguments | `,` | Optional |
| Tuple expressions | `,` | Optional |
| Array literals | `,` | Optional |
| Dictionary literals | `,` | Optional |
| Struct literal fields | `,` | Optional |
| Import nested items | `,` | Optional |
| Closure parameters | `,` | Optional |
| Pattern lists | `,` | Optional |

**Important**: If you write a multiline comma-separated list without commas at the end of lines, ASI will insert semicolons and the parser rejects the inserted semicolon (the exact diagnostic depends on
the list form).

---

## Multiline Constructs and ASI Interaction

**Struct Fields**: Since struct fields use semicolons as separators and ASI inserts semicolons after identifiers and closing delimiters on newlines, multiline struct definitions work naturally:
```
struct Point {
    x: int32       // ASI inserts `;` here
    y: int32       // ASI inserts `;` here
}
```

**Comma-Separated Lists**: Commas are **required** after every element whose delimiter or next element
starts on a new line:
```
// WRONG - ASI inserts `;` after `a`, causing error
foo(
    a
    b
)

// CORRECT - comma prevents ASI
foo(
    a,
    b,
)

// ALSO CORRECT - closing delimiter on the final element's line
foo(
    a,
    b)
```

More examples:
```
let arr = [
    1,          // comma required
    2,          // comma required
    3,          // comma required before closing delimiter on next line
]

let user = User {
    id: 1,          // comma required
    name: "John",   // comma required before closing delimiter on next line
}
```

### Single-Element Tuples vs Parenthesized Expressions

A trailing comma disambiguates a one-element tuple from a parenthesized
expression or type:
```
(a)      // parenthesized expression (equivalent to `a`)
(a,)     // one-element tuple, type `(T,)` if `a: T`
(a, b)   // two-element tuple
()       // empty tuple (unit)

(T)      // parenthesized type
(T,)     // one-element tuple type
(T) -> U // single-argument function type (NOT a tuple-return trick)
```

The same rule applies to patterns: `(p,)` is a one-element tuple pattern and
`(p)` is a parenthesized pattern equivalent to `p`.

### Struct Literal Disambiguation

Struct literals (`Foo { ... }`) can be ambiguous with blocks in control-flow
heads. Bare literals are disallowed there; enclosing delimiters remove the
ambiguity:
```
if condition { ... }           // block, not struct literal
let x = Foo { field: value }   // struct literal OK here
if (Flag { enabled: true }).enabled { } // parentheses distinguish the literal
```

Keep `else` on the same line as the preceding `}`. It does not suppress ASI.
An `if` without `else` has unit type; it does not implicitly produce an optional.

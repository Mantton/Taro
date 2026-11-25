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

<string_literal>       ::= '"' { <string_item> } '"'
                         | '"""' LF <multiline_body> '"""'
                         | HASHES '"' <raw_body> '"' HASHES
                         | HASHES '"""' LF <raw_multiline_body> '"""' HASHES
<string_item>          ::= <string_char> | '${' <expression> [ ':' <format_spec> ] '}'
<multiline_body>       ::= { <multiline_char> | '${' <expression> [ ':' <format_spec> ] '}' }
<raw_body>             ::= { <raw_char> | <raw_interpolation> }
<raw_multiline_body>   ::= { <raw_multiline_char> | <raw_interpolation> }
<raw_interpolation>    ::= '$' HASHES '{' <expression> [ ':' <format_spec> ] '}'
<format_spec>          ::= [ [ <fill_char> ] ( '<' | '>' | '^' ) ] [ '0' ] [ <decimal_digits> ] [ '.' <decimal_digits> ] [ 'x' | 'b' | 'e' | '?' ]
<multiline_char>       ::= <escape> | '\${' | ? character not beginning an escape, interpolation or triple delimiter, except CR ?
<raw_char>             ::= ? character not beginning a matched marker or delimiter, except LF or CR ?
<raw_multiline_char>   ::= ? character not beginning a matched marker or delimiter, except CR ?
<rune_literal>         ::= '\'' <rune_char> '\''

<string_char>          ::= <escape> | '\${' | ? character not beginning an escape, interpolation or delimiter, except LF or CR ?
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
between tokens, not line breaks. Bare CR is rejected in literal text.

`HASHES` is one or more `#` characters; the opening and closing counts match.
Raw text preserves backslashes and recognizes only `$` + the exact hash count +
`{ expression }` as interpolation. Nonmatching interpolation markers are literal.
Ordinary quoted strings (including interpolations) occupy one source line.
Multiline closing delimiters occupy their own line. Boundary newlines and the
closing delimiter's indentation are excluded; nonblank literal lines must have
the same indentation prefix. Interpolation expression lines are exempt, and
inserted values are not reindented. Ordinary multiline text processes escapes;
raw multiline text does not. Backslash line continuation is unsupported.

Strings without active interpolation remain literal tokens in all literal-only
contexts. Interpolation uses normal expression lexing, and values are never
rescanned. See [strings](guide/syntax/lexical.md#string-literals) for examples.

### Keywords

```
any         as          is          break       case        conform     const       continue
async       await       class       defer                   else        enum        export      extern      false
final       for         func        guard       if          extend      import
in          init        interface   loop        match
mod         mut         namespace   nil         operator    private
override    public      readonly    return      static      struct      true
type        unsafe      var         where       while
```

### Reserved Keywords

```
fileprivate let protected ref
```

`let` is reserved so that its removal can be diagnosed; locals use `var` or
`:=`.

### Contextual Keywords

`get`, `set`, `address`, and `subscript` are contextual accessor/declaration
keywords. Computed properties support `get`; native subscripts support all three
accessors. `some` introduces an
opaque return type. `required`/`convenience` modify initializers. These words
remain valid identifiers in other contexts; `weak` is an ordinary identifier.

### Operators and Punctuation

```ebnf
<operator>             ::= '+' | '-' | '*' | '/' | '%'
                         | '=' | ':='
                         | '&' | '|' | '^' | '~' | '!' | '!in'
                         | '<' | '>' | '<<' | '>>'
                         | '==' | '!=' | '<=' | '>='
                         | '&&' | '||'
                         | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>=' | '??='
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
                         | <class_declaration>
                         | <enum_declaration>
                         | <interface_declaration>
                         | <function_declaration>
                         | <static_variable_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <implementation_declaration>
                         | <extern_block>
                         | <extern_function>
                         | <namespace_declaration>

<visibility>           ::= [ 'public' | 'private' | 'internal' ]
```

Omitted visibility is public, except initializers, which default to package
visibility. Declarations, including declarations with bodies,
need a terminating semicolon, which is normally supplied by ASI.

Class declarations represent GC handles with separate object storage. Source
initialization, inheritance, designated/convenience initializer
inheritance and virtual method dispatch are supported; a class is never lowered
as an inline struct. Required initializers and class interface conformances
are supported. Configuration-disabled declarations are
removed before availability checks.

```ebnf
<class_declaration>    ::= [ 'final' ] 'class' <identifier> [ <type_parameters> ]
                           [ <conformances> ] [ <where_clause> ]
                           '{' <struct_fields> '}'
```

Class header types are retained in source order for later base/interface
classification. Methods and initializers belong in owning-package `extend` blocks; language
destructors are removed. Use explicit resource close operations or `defer`.

### Import and Export

```ebnf
<import_declaration>   ::= 'import' <use_tree>
<export_declaration>   ::= 'export' <use_tree>

<use_tree>             ::= <use_tree_path> <use_tree_kind>

<use_tree_path>        ::= <identifier> { '::' <identifier> }

<use_tree_kind>        ::= <use_tree_glob>
                         | <use_tree_simple>
                         | <use_tree_nested>

<use_tree_glob>        ::= '::' '*'
<use_tree_simple>      ::= [ 'as' <identifier> ]
<use_tree_nested>      ::= '::' '{' <use_tree_nested_list> '}'

<use_tree_nested_list> ::= <use_tree_nested_item> { ',' <use_tree_nested_item> } [ ',' ]
<use_tree_nested_item> ::= <identifier> [ 'as' <identifier> ]
```

### Struct Declaration

```ebnf
<struct_declaration>   ::= 'struct' <identifier> [ <type_parameters> ]
                           ( [ <conformances> ] [ <where_clause> ] '{' <struct_fields> '}'
                           | '(' [ <type> { ',' <type> } [ ',' ] ] ')'
                             [ <conformances> ] [ <where_clause> ] )

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

<variant_kind>         ::= <tuple_variant> | <named_variant>
<named_variant>        ::= '{' [ <named_variant_field> { ( ',' | ';' ) <named_variant_field> } [ ',' | ';' ] ] '}'
<named_variant_field>  ::= [ 'readonly' ] <identifier> ':' <type>
<tuple_variant>        ::= '(' <tuple_variant_fields> ')'
<tuple_variant_fields> ::= [ <tuple_field> { ',' <tuple_field> } [ ',' ] ]
<tuple_field>          ::= [ 'readonly' ] [ <label> ] <type>
```

### Interface Declaration

```ebnf
<interface_declaration>::= 'interface' <identifier> [ <type_parameters> ]
                           [ <where_clause> ] [ <conformances> ]
                           '{' { <interface_associated_declaration> } '}'

<interface_associated_declaration>
                       ::= { <attribute> } <visibility> <interface_associated_decl_kind> ';'

<interface_associated_decl_kind>
                       ::= { 'final' | 'override' } [ 'static' ] <function_declaration>
                         | <initializer_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <interface_property_declaration>
                         | <subscript_requirement>

<interface_property_declaration>
                       ::= 'var' <identifier> ':' <type>
                           '{' <getter_requirement> '}'

<getter_requirement>   ::= 'get' [ <block> ]

<conformances>         ::= ':' <generic_bound> { ',' <generic_bound> }
```

### Extensions and Conformances

```ebnf
<implementation_declaration>     ::= ( 'extend' [ <type_parameters> ] <type>
                           | 'conform' [ <type_parameters> ] <type> 'to' <type> )
                           [ <where_clause> ] '{' { <implementation_associated_declaration> } '}'

<implementation_associated_declaration>
                       ::= { <attribute> } <visibility> <implementation_associated_decl_kind> ';'

<implementation_associated_decl_kind>
                       ::= { 'final' | 'override' } [ 'static' ] <function_declaration>
                         | <constant_declaration>
                         | <type_alias_declaration>
                         | <computed_property_declaration>
                         | <subscript_declaration>
                         | <initializer_declaration>

<initializer_declaration>
                       ::= { 'required' | 'convenience' | 'override' } 'init'
                           [ <type_parameters> ] '(' [ <parameter_list> ] ')'
                           [ '->' <type> ] [ <where_clause> ] <block>
<computed_property_declaration>
                       ::= 'var' <identifier> ':' <type>
                           '{' <getter_accessor> '}'

<getter_accessor>      ::= 'get' <block>

<subscript_declaration>::= { 'final' | 'override' } 'subscript'
                           '(' <index_parameter_list> ')' '->' <type>
                           '{' { <subscript_accessor> } '}'
<subscript_requirement>::= 'subscript' '(' <index_parameter_list> ')' '->' <type>
                           '{' { <subscript_accessor_requirement> } '}'
<index_parameter_list>::= <index_parameter> { ',' <index_parameter> }
<index_parameter>      ::= [ <identifier> | '_' ] <identifier> ':' <type>
<subscript_accessor>   ::= 'get' <block> | 'set' '(' <identifier> ')' <block>
                         | 'address' <block>
<subscript_accessor_requirement>
                       ::= 'get' [ <block> ]
                         | 'set' | 'set' '(' <identifier> ')' [ <block> ]
                         | 'address' [ <block> ]
```

Native subscript accessors are synchronous and share their declaration's
implicit receiver. Index parameters have fixed arity, no defaults or variadics,
and are unlabeled unless an external label is explicitly provided. Accessor
order is unrestricted; duplicates are rejected. An ordinary declaration must
provide `get` or `address`. `address` returns a reference to the element and
supplies omitted get/set bodies; explicit accessors replace their corresponding
defaults. Read, set and address selection is static. Interface witnesses resolve
individual accessors, which implementations may override independently.

### Function Declaration

```ebnf
<function_declaration> ::= [ 'const' ] [ 'unsafe' ] 'func' <identifier> [ <type_parameters> ]
                           <function_signature> [ <where_clause> ] [ <block> ]

<function_signature>   ::= <function_prototype>

<function_prototype>   ::= '(' [ <parameter_list> ] ')' [ 'async' ] [ '->' <type> ]

<parameter_list>  ::= <function_parameter> { ',' <function_parameter> } [ ',' ]

<function_parameter>   ::= { <attribute> } <parameter_name> ':'
                           <type> [ '...' ] [ '=' <expression> ]

<parameter_name>       ::= <identifier> [ <identifier> ]
                         | '_' [ <identifier> ]
<label>                ::= <identifier> ':'
```

Instance functions have an implicit `self` with the declared target type.
Explicit receiver parameters are rejected in functions and accessors. Computed
getters are synchronous and use the same target-directed implicit receiver.

Function bodies are required outside interfaces and extern declarations.
`unsafe` precedes `func`, after visibility. Variadic parameters have `Span[T]`
inside the function.

`operator` is reserved and has no declaration form. Operator overloading uses
standard-library interfaces; see [Operator Overloading](guide/syntax/declarations.md#operator-overloading).

### Static Variable and Constant Declarations

```ebnf
<static_variable_declaration>
                       ::= 'static' 'var' <identifier> ':' <type> '=' <expression>

<variable_declaration> ::= 'var' <local_pattern> [ ':' <type> ] [ '=' <expression> ]
                         | <shorthand_pattern> ':=' <expression>
<local_pattern>        ::= <identifier_pattern> | <wildcard_pattern> | <tuple_pattern>
<shorthand_pattern>    ::= <identifier_pattern> | <wildcard_pattern> | <shorthand_tuple_pattern>
<shorthand_tuple_pattern>
                       ::= '(' ')'
                         | '(' <shorthand_tuple_elem> ',' [ <shorthand_tuple_elem> { ',' <shorthand_tuple_elem> } [ ',' ] ] ')'
<shorthand_tuple_elem> ::= <identifier_pattern> | <wildcard_pattern> | <rest_pattern> | <shorthand_tuple_pattern>

<constant_declaration> ::= 'const' <identifier> ':' <type> [ '=' <expression> ]
```

Local binding patterns must be irrefutable, including nested tuple patterns.

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
`Iterator[Element = int32]`. Function/extension/conformance `where` clauses follow the signature
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

<reference_type>       ::= '&' <type>

<tuple_type>           ::= '(' ')'
                         | '(' <type> ',' ')'                /* one-element tuple */
                         | '(' <type> ',' <type_list> ')'

<type_list>            ::= <type> { ',' <type> } [ ',' ]

<function_type>        ::= '(' [ <type_list> ] ')' '->' <type>

<collection_type>      ::= '[' <collection_type_inner> ']'

<collection_type_inner>::= <type>                        /* list: [T] */
                         | <type> ':' <type>             /* dict: [K:V] */
                         | <type> ';' <const_expression> /* array: [T;N] */
                         | <type> ';' '..'               /* Span: [T;..] */

<existential_type>     ::= 'any' <path_node> { '&' <path_node> }

<opaque_return_type>   ::= 'some' <path_node> { '&' <path_node> }

<infer_type>           ::= '_'

<paren_type>           ::= '(' <type> ')'

<never_type>           ::= '!'
<qualified_type>       ::= '(' <type> 'as' <type> ')' '.' <identifier>
```

`&T` is a writable GC reference; `&mut` and `&const` are rejected.
Raw pointers retain `*const T` (also `*T`) and `*mut T`. `some` is restricted to supported return-type
positions. `(T as Interface).Member` selects an associated type explicitly.

### Path

```ebnf
<path>                 ::= <path_segment> { '::' <path_segment> }

<path_segment>         ::= <identifier> [ <type_arguments> ]
                         | <callable_name> <callable_type_arguments>
<callable_name>        ::= 'Fn' | 'AsyncFn'

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
                         | <range_pattern>
                         | <type_pattern>

<wildcard_pattern>     ::= '_'

<rest_pattern>         ::= '..'

<identifier_pattern>   ::= <identifier>

<tuple_pattern>        ::= '(' [ <pattern_list> ] ')'
<pattern_list>         ::= <pattern> { ',' <pattern> } [ ',' ]

<path_pattern>         ::= <pattern_path> [ <tuple_pattern> | <named_pattern_fields> ]
<named_pattern_fields> ::= '{' [ ( <named_pattern_field> { ',' <named_pattern_field> }
                                 [ ',' '..' ] | '..' ) [ ',' ] ] '}'
<named_pattern_field>  ::= <identifier> [ ':' <pattern> ]

<pattern_path>         ::= <path>                        /* qualified: Foo::Bar */
                         | '.' <identifier>              /* inferred: .Bar */

<match_pattern>        ::= <pattern> { '|' <pattern> }

<type_pattern>         ::= 'is' <type> | <identifier> 'as' <type>

<range_pattern>        ::= <range_bound> ( '..' | '..=' ) <range_bound>
<range_bound>          ::= [ '-' ] <integer_literal> | <rune_literal> | <path>

<literal_pattern>      ::= <literal>
                         | '-' ( <integer_literal> | <float_literal> )

```

---

Or-patterns belong at the top level of match arms. Rest patterns are accepted
inside tuple and variant-payload patterns. Reference patterns are removed.
Structural match/if-case patterns automatically dereference reference targets;
plain identifier bindings copy references as values. Explicit `*` remains
available, and all bindings are writable value copies. Qualified path
patterns resolve enum variants, not arbitrary constants. Numeric literal
patterns may have a leading minus sign, and integer patterns must fit their
type. Arbitrary expressions and interpolated strings are rejected;
use a guard for those comparisons. See
[Value Bindings and References](guide/syntax/patterns.md#value-bindings-and-references).

## Statements

```ebnf
<block>                ::= '{' { <statement> ';' } [ <statement> ] '}'

<statement>            ::= <declaration_statement>
                         | <expression_statement>
                         | <variable_statement>
                         | <while_statement>
                         | <for_statement>
                         | <return_statement>
                         | <loop_expression>
                         | <break_statement>
                         | <continue_statement>
                         | <using_statement>
                         | <async_variable_statement>
                         | <defer_statement>
                         | <errdefer_statement>
                         | <guard_statement>
                         | <comptime_for_statement>
                         | <comptime_if_statement>

<declaration_statement>::= { <attribute> } <visibility> <function_declaration>

<expression_statement> ::= <expression>

<variable_statement>   ::= <variable_declaration>

<loop_expression>      ::= [ <label_def> ] 'loop' <block>

<while_statement>      ::= [ <label_def> ] 'while' <expression> <block>

<for_statement>        ::= [ <label_def> ] 'for' [ 'await' ] <pattern> 'in' <expression>
                           [ 'where' <expression> ] <block>

<return_statement>     ::= 'return' [ <expression> ]

<break_statement>      ::= 'break' [ <expression> ]

<continue_statement>   ::= 'continue' [ <identifier> ]

<using_statement>      ::= 'using' <identifier> '=' <expression>

<async_variable_statement> ::= 'async' 'var' <identifier> [ ':' <type> ] '=' <expression>

<defer_statement>      ::= 'defer' ( <block> | <expression> )

<errdefer_statement>   ::= 'errdefer' ( <block> | <expression> )

<guard_statement>      ::= 'guard' <expression> 'else' <block>

<comptime_for_statement> ::= '#for' <identifier> 'in' '#fields' '(' <type> ')' <block>

<comptime_if_statement>  ::= '#if' <expression> <block> [ 'else' ( <comptime_if_statement> | <block> ) ]

<label_def>            ::= <identifier> ':'
```

---

A final non-declaration statement may omit its semicolon before `}`. A local
function declaration still requires one. `guard` and `if`/`while` conditions
are boolean; binding conditions produce a boolean and introduce bindings.
`for await` is restricted to async contexts.

## Expressions

### Expression Precedence (Lowest to Highest)

1. Assignment: `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`, `??=`
2. Pipe: `|>`
3. Ternary: `? :`
4. Nil-coalescing: `??`
5. Range: `..`, `..=`
6. Logical OR: `||`
7. Logical AND: `&&`
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`
9. Membership: `in`, `!in` (non-associative)
10. Bitwise OR: `|`
11. Bitwise XOR: `^`
12. Bitwise AND: `&`
13. Bit shift: `<<`, `>>`
14. Term: `+`, `-`
15. Factor: `*`, `/`, `%`
16. Cast / Type Assertion: `as`, `as?`, `is`
17. Prefix: `!`, `-`, `~`, `&`, `*`
18. Postfix: `.`, `()`, `[]`, `!`, `?.`
19. Primary

```ebnf
<expression>           ::= <assignment_expression>

<assignment_expression>::= <pipe_expression> [ <assignment_op> <pipe_expression> ]

<assignment_op>        ::= '=' | '+=' | '-=' | '*=' | '/=' | '%='
                         | '&=' | '|=' | '^=' | '<<=' | '>>=' | '??='

<pipe_expression>      ::= <ternary_expression> { '|>' <ternary_expression> }

<ternary_expression>   ::= <nil_coalesce_expr> [ '?' <ternary_expression> ':' <ternary_expression> ]

<nil_coalesce_expr>    ::= <range_expression> [ '??' <nil_coalesce_expr> ]

<range_expression>     ::= <or_expression> [ '..' [ <or_expression> ] | '..=' <or_expression> ]
                         | '..' [ <or_expression> ]
                         | '..=' <or_expression>

<or_expression>        ::= <and_expression> { '||' <and_expression> }

<and_expression>       ::= <comparison_expr> { '&&' <comparison_expr> }

<comparison_expr>      ::= <membership_expr> { <comparison_op> <membership_expr> }

<comparison_op>        ::= '<' | '>' | '<=' | '>=' | '==' | '!='

<membership_expr>      ::= <bitor_expression>
                           [ ( 'in' | '!in' )
                             ( <bitor_expression> [ '..' [ <bitor_expression> ] | '..=' <bitor_expression> ]
                             | '..' [ <bitor_expression> ]
                             | '..=' <bitor_expression> ) ]

<bitor_expression>     ::= <bitxor_expression> { '|' <bitxor_expression> }

<bitxor_expression>    ::= <bitand_expression> { '^' <bitand_expression> }

<bitand_expression>    ::= <shift_expression> { '&' <shift_expression> }

<shift_expression>     ::= <term_expression> { ( '<<' | '>>' ) <term_expression> }

<term_expression>      ::= <factor_expression> { ( '+' | '-' ) <factor_expression> }

<factor_expression>    ::= <cast_expression> { ( '*' | '/' | '%' ) <cast_expression> }

<cast_expression>      ::= <prefix_expression> { 'as' [ '?' ] <type> | 'is' ( <type> | <nonbinding_pattern> ) }
<nonbinding_pattern>   ::= <pattern>  (* without variable bindings *)

<prefix_expression>    ::= <prefix_op> <prefix_expression>
                         | <postfix_expression>

<prefix_op>            ::= '!' | '-' | '~' | '&' | '*'

<postfix_expression>   ::= <primary_expression> { <postfix_op> }

<postfix_op>           ::= '.' <identifier>                  /* instance member access */
                         | '::' <identifier>                 /* namespace/type member */
                         | '.' <integer_literal>             /* tuple access */
                         | '(' <argument_list> ')'           /* call */
                         | '[' <type_argument_list> ']'      /* specialization */
                         | '[' <argument> { ',' <argument> } [ ',' ] ']' /* native indexing */
                         | '!'                               /* Optional/Result propagation */
                         | '?.' ( <identifier>
                                | <integer_literal>
                                | '[' <argument> { ',' <argument> } [ ',' ] ']'
                                | '(' <argument_list> ')' )        /* optional chain */

<argument_list>        ::= [ <call_argument> { ',' <call_argument> } [ ',' ] ]
<call_argument>        ::= <argument> [ '...' ]

<argument>             ::= [ <label> ] <pipe_expression>
```

Postfix `!` propagates only `Optional[T]` and `Result[T, E]`. `await` scopes the
following expression: each resolved async call suspends before its result is
used. Thus `await expr!`, `await operation() + value`, and chained calls are
valid; parentheses may still narrow the scope. Closure bodies require their
own markers. Assignments do not chain without explicit grouping. Nil coalescing
is right-associative. `target ??= value` assigns only when the optional target is
nil; `T??=` in a type annotation still reads as `T??` followed by `=`.

`a in b` calls `b.contains(&a)` through `std::ops::Contains[Element]`, and
`a !in b` negates it. The container side may be a range, so `x + 1 in 0..n`
reads as `(x + 1) in (0..n)`, while `&&`, `||`, `==` and `!=` bind more
loosely. Membership does not chain: `a in b in c` is an error, so group it as
`(a in b) in c`. `!in` is one token only when `!` touches a whole-word `in`:
`value !in set` and `value!in set` are negated membership, `value! in set`
propagates `value` and then tests it, and `!inside` negates an identifier.

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
                         | <select_expression>
                         | <block_expression>
                         | <closure_expression>
                         | <struct_literal>
                         | <wildcard_expression>
                         | <binding_condition>
                         | <paren_expression>
                         | <unsafe_expression>
                         | <await_expression>
                         | <yield_expression>
                         | <embed_expression>
                         | <source_location>
                         | <cfg_check>
                         | <type_name_expression>
                         | <return_statement>
                         | <loop_expression>
                         | <break_statement>
                         | <continue_statement>

<paren_expression>     ::= '(' <expression> ')'

<tuple_expression>     ::= '(' ')'
                         | '(' <expression> ',' ')'                /* one-element tuple */
                         | '(' <expression> ',' <expression_list> ')'

<expression_list>      ::= <expression> { ',' <expression> } [ ',' ]

<array_expression>     ::= '[' ']'
                         | '[' <array_element> { ',' <array_element> } [ ',' ] ']'
                         | '[' <expression> ';' <const_expression> ']'   /* repeat */

<array_element>        ::= <expression> [ '...' ]

<dictionary_expression>::= '[' <map_pair_list> ']'
                         | '[' ':' ']'

<map_pair_list>        ::= <map_pair> { ',' <map_pair> } [ ',' ]
<map_pair>             ::= <expression> ':' <expression>

<wildcard_expression>  ::= '_'
<unsafe_expression>    ::= 'unsafe' <block>
<await_expression>     ::= 'await' <expression>
<yield_expression>     ::= 'yield' <expression>   /* contextual keyword */
<embed_expression>     ::= ( '#embed' | '#embedBytes' ) '(' <string_literal> ')'
<source_location>      ::= '#file' | '#line' | '#function'
<cfg_check>            ::= '#cfg' '(' <cfg_expression> ')'
<type_name_expression> ::= '#typeName' '(' <type> ')'
```

`_` expressions are restricted to one direct argument placeholder in a pipe
call, an assignment destination (`_ = value`, which evaluates and discards the
value), and the leaves of a tuple assignment destination (`(a, _) = pair`).
Compound assignments (`_ += 1`) still require a place. Binding conditions are
restricted to `if`/`while`/`guard` conditions.
Repeat literals require a compile-time count and construct fixed-size arrays.

`yield` is parsed contextually: `yield <expression>` parses as a generator yield
when followed on the same line by an expression starter (such as a literal,
identifier, unary operator with no space before `-`, parenthesized expression
preceded by whitespace, array/tuple, or leading dot), while ordinary identifier
uses (`yield := 1`, `yield(x)`, `yield.field`, `yield[i]`, `yield - 1`) remain
valid identifiers. Calling a synchronous generator allocates its suspended frame
without running the body; side effects begin on the first call to `next()`.
Stopping iteration early without calling `close()` leaves subsequent yields
unexecuted and lets the GC reclaim the frame; calling `close()` (directly or via
`using`) runs active `defer` cleanups once and marks the generator exhausted.
Async generators return `some AsyncIterator[Element = T]` or
`some AsyncIterable[Element = T]` (without the `async` function modifier) and
may use both `await` and `yield` in their bodies; `for await` automatically
closes its iterator on scope exit, and cancellation while blocked on an inner
`await` cancels the pending operation and runs active `defer` cleanups once.

### Control Flow Expressions

```ebnf
<if_expression>        ::= 'if' <expression> <block> [ 'else' <else_branch> ]

<else_branch>          ::= <if_expression> | <block>

<match_expression>     ::= 'match' <expression> '{' { <match_arm> } '}'

<match_arm>            ::= 'case' <match_pattern> [ 'if' <expression> ]
                           '=>' <expression> ';'
                         | '_' '=>' <expression> ';'

<select_expression>    ::= 'select' '{' { <select_arm> } '}'

<select_arm>           ::= 'case' <pattern> '=' 'await' <expression>
                           '=>' <expression> [ ',' | ';' ]

<block_expression>     ::= <block>
```

### Closure Expression

```ebnf
<closure_expression>   ::= <closure_params>
                           ( 'async' [ '->' <type> ] '=>' <block>
                           | '->' <type> 'async' '=>' <block>
                           | [ '->' <type> ] '=>' <closure_body> )

<closure_params>       ::= '(' [ <closure_param_list> ] ')'

<closure_param_list>   ::= <closure_param> { ',' <closure_param> } [ ',' ]

<closure_param>        ::= { <attribute> } <identifier> [ ':' <type> [ '...' ] ]

<closure_body>         ::= <block>
                         | <expression>
```

### Struct Literal

```ebnf
<struct_literal>       ::= <pattern_path> '{' [ <field_init_list> ] '}'

<field_init_list>      ::= <field_init> { ',' <field_init> } [ ',' <update_base> ] [ ',' ]
                         | <update_base> [ ',' ]
<field_init>           ::= <identifier> [ ':' <expression> ]
<update_base>          ::= '..' <expression>
```

Struct-style enum variants use named brace fields and patterns; tuple variants
use positional patterns. Enum payload fields inherit variant visibility and
reject field visibility modifiers. Update bases are allowed only for structs
without `init`; classes and enum variants reject updates. Explicit fields run
in written order before one evaluation of the exact-typed base. A redundant base
warns and still evaluates. See the
[expression guide](guide/syntax/expressions.md#struct-and-named-variant-literals).

Bare struct literals and bare trailing closures are restricted in
`if`/`while`/`guard` conditions, `for` iterators/filters, and `match`
scrutinees. Parentheses, call arguments, collection literals, block
expressions, and string interpolations permit them inside their delimiters.
The surrounding restriction resumes after the closing delimiter.

A trailing closure `{ [ <closure_params> '=>' ] <block_body> }` on the same
line as a call supplies the call's final argument and drops that parameter's
label; a sole trailing closure may omit empty `()`. Headerless trailing
closures synthesize a single `it` parameter when the body references free `it`
and zero parameters otherwise. `Name { ... }` retains struct literal
recognition for explicit field lists, update bases, and uppercase empty or
single-identifier constructors.

### Binding Conditions

```ebnf
<binding_condition>    ::= 'case' [ 'var' ] <pattern> '=' <binding_initializer>
                         | 'var' <identifier> [ '=' <binding_initializer> ]

<binding_initializer>  ::= <expression> /* excluding unparenthesized outer && and || */
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

Taro uses automatic semicolon insertion (ASI). Semicolons are automatically inserted after tokens that can end a statement at a newline or end of file, unless the next line begins with a continuation token or the newline is directly inside `( )` or `[ ]`.

**Tokens that can end a statement:**
- Identifiers, literals (`true`, `false`, `nil`)
- `break`, `continue`, `return`
- `)`, `]`, `}`
- `?`, `!`, `.*`, `..`

**Line continuation starters (suppress ASI):**
- Binary operators: `+`, `-`, `/`, `%`, `|`, `^`, `&&`, `||`
  - Note: `&` and `*` are **not** treated as continuation starters because they have common unary uses (reference and dereference/pointer) that should start new statements
- Comparison operators: `<`, `>`, `<=`, `>=`, `==`, `!=`
- Shifts: `<<`, `>>`
- Assignment operators
- Member/optional/spread: `.`, `...`, `?.`, `??`
  - Note: `..` and `..=` are **not** line continuation starters so a new line beginning with `..end` or `..=end` outside `()` / `[]` starts a fresh statement rather than continuing the previous line
- Pipe and arrows: `|>`, `->`, `=>`
- Keywords: `as`, `is`, `in`, `!in`, `else`, `where`

`else` appears only after an `if` block or a `guard` condition, and `where`
only opens a where clause or a `for` filter, so neither can start a statement:

```
if ready {
    start()
}
else {
    stop()
}

guard value > 0
else { return }

func largest[T](_ values: [T]) -> T
    where T: Ord {
    ...
}
```

A `{` at the start of a line is not a continuation starter: a newline before it
still inserts a semicolon, so keep the opening brace of a body on the line that
ends its header.

**Grouping delimiters:** ASI tracks the innermost open delimiter.
- Directly inside `( )` or `[ ]`, a newline never inserts a semicolon.
- Directly inside `{ }`, including braces nested inside parentheses or brackets
  (blocks, closure bodies, `match` bodies, struct literals), ASI works as
  described above. String interpolations `${ ... }` follow the same rule as
  braces.
- After a closing delimiter, the rule of the enclosing delimiter applies again.

```
result := compute(
    base
        + offset,
    items.map(item => {
        log(item)       // statements inside braces still end at newlines
        item * 2
    })
)
```

Explicit semicolons are unaffected, so `[0; 20]` and `[uint8; 20]` keep
working. The `;` of a repeat literal or array type must be written; a newline
does not stand in for it.

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

The following remain reserved for future use:
- `ref`
- `fileprivate`, `protected`

---

## Comma and Semicolon Rules

### Semicolon-Separated Lists

Constructs inside braces that use semicolons as separators work naturally with
ASI:

| Construct | Separator |
|-----------|-----------|
| Struct fields | `;` |
| Enum cases | `;` |
| Match arms | implicit (newline inserts `;`) |

### Comma-Separated Lists and ASI

Inside `( )` and `[ ]`, newlines do not insert semicolons, so a multi-line list
needs commas only between elements; a trailing comma is optional whether the
closing delimiter is on the same line or the next one. Inside `{ }` (struct
literal fields, import groups), ASI still runs, so **a comma is required before
every newline**, including after the final element when the `}` is on the next
line. Enum variants within one `case` do not accept a trailing comma.

| Construct | Delimiter | Separator | Trailing Comma |
|-----------|-----------|-----------|----------------|
| Enum variants (in a case) | none | `,` | Not accepted |
| Function parameters | `( )` | `,` | Optional |
| Type parameters | `[ ]` | `,` | Optional |
| Type arguments | `[ ]` | `,` | Optional |
| Call arguments | `( )` | `,` | Optional |
| Tuple expressions and types | `( )` | `,` | Optional |
| Function type parameters | `( )` | `,` | Optional |
| Attribute arguments | `( )` | `,` | Optional |
| Array literals | `[ ]` | `,` | Optional |
| Dictionary literals | `[ ]` | `,` | Optional |
| Closure parameters | `( )` | `,` | Optional |
| Pattern lists | `( )` | `,` | Optional |
| Struct literal fields | `{ }` | `,` | Optional; required before a newline |
| Import nested items | `{ }` | `,` | Optional; required before a newline |

**Important**: Inside `( )` and `[ ]`, a missing comma between elements on
separate lines is reported as ``expected `,` or `)` `` (or `]`) at the second
element. Inside `{ }`, a missing comma before a newline lets ASI insert a
semicolon, which the parser rejects.

---

## Multiline Constructs and ASI Interaction

**Struct Fields**: Since struct fields use semicolons as separators and ASI inserts semicolons after identifiers and closing delimiters on newlines, multiline struct definitions work naturally:
```
struct Point {
    x: int32       // ASI inserts `;` here
    y: int32       // ASI inserts `;` here
}
```

**Comma-Separated Lists**: Inside `( )` and `[ ]`, commas separate elements and
newlines are ignored. Inside `{ }`, a comma is **required** after every element
whose next element or closing `}` starts on a new line:
```
// WRONG - elements need a separator
foo(
    a
    b
)

// CORRECT - the trailing comma is optional
foo(
    a,
    b
)

arr := [
    1,
    2,
    3
]

user := User {
    id: 1,          // comma required
    name: "John",   // comma required before `}` on the next line
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
x := Foo { field: value }   // struct literal OK here
if (Flag { enabled: true }).enabled { } // parentheses distinguish the literal
```

`else` may begin a line after the preceding `}`; it continues the `if`.
An `if` without `else` has unit type; it does not implicitly produce an optional.

Instance functions use an implicit `self` of exactly their declared target
type: `extend T` copies a value receiver, while `extend &T` receives a reference.
Explicit receiver parameters are rejected. Use `static func` for receiver-free
associated functions, including interface requirements. Free and namespace
functions are receiver-free without `static`.

Local `name := expression` and tuple destructuring `(a, b) := expression` create
new mutable bindings with inferred types (evaluating the right-hand side before
shadowing any outer names). They cannot carry type annotations and do not update
earlier bindings of the same name; use assignment (`=` / `(a, b) = expr`) for
updates. Shorthand declarations are unavailable in declaration scopes outside
function/block bodies and in conditions.

Binding conditions are valid directly in the condition or as unparenthesized
positive `&&` conjuncts. Each
binding is visible to subsequent conjuncts and the successful body (or after
a successful guard). Bindings under `||`, negation, or ordinary call arguments
are rejected. Nested closure and block bodies establish their own contexts.
`var` makes an optional binding. All case bindings are writable, with or
without the optional `var` spelling.

Initializer signatures have no explicit receiver or result type, and
initializers cannot be async. `required` and `convenience` are
contextual modifiers; they remain valid identifiers outside declaration prefixes.
`final`/`override` on ordinary methods require instance functions; static functions
cannot use those modifiers. Repeated modifiers are rejected.

Fields support synchronous `= expression` defaults. Defaults and initializers
establish every field before use. References to self fields, whole-self escape
and instance calls are rejected during construction. `readonly` prevents direct
field assignment after construction; it does not freeze a shared referent.
Use `std::weak::Weak[T]` for explicit weak references; `weak var`, weak fields
and `deinit` are removed.

### Removed capability markers

Every value copies and every type may escape, so the `Copy`, `NoCopy`,
`Sendable` and `Escapable` markers and `!Bound` relaxations no longer exist.
`@NoCopy` is a separate, no-argument type declaration attribute for advisory
`taro vet` checks; it is not a type, field or ownership bound.

`internal` is a visibility modifier for declarations and stored fields. It allows
access from the defining package, including sibling modules; `private` retains
its narrower owner/owned-extension boundary.

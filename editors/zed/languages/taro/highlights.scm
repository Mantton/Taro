; Comments
(line_comment) @comment
(block_comment) @comment
(doc_comment) @comment.documentation

; Literals
(string_literal) @string
(escape_sequence) @string.escape
(string_escape) @string.escape
(rune_literal) @string.special
(string_interpolation_start) @punctuation.special
(interpolation_format) @string.special
(string_interpolation_end) @punctuation.special
(number_literal) @number
(boolean_literal) @constant.builtin
(nil_literal) @constant.builtin
(source_location_literal) @constant.builtin
(embed_expression directive: _ @function.builtin)

; Type identifiers
(type_identifier) @type
(simple_type) @type

; Function declarations
(function_declaration
  name: (identifier) @function)
(method_declaration
  name: (identifier) @function)
(extern_function
  name: (identifier) @function)

; Function calls
(call_expression
  (identifier) @function.call)
(call_expression
  (member_expression
    (identifier) @function.call))

(call_expression
  (qualified_expression
    (identifier) @function.call))

; Parameters
(parameter "@lazy" @attribute)
(parameter
  label: (identifier) @variable.parameter)
(parameter
  name: (identifier) @variable.parameter)
(closure_parameter
  name: (identifier) @variable.parameter)
(closure_expression
  parameter: (identifier) @variable.parameter)

; Call argument labels
(argument
  label: (identifier) @variable.parameter)

; Struct fields
(struct_field
  name: (identifier) @property)
(struct_literal_field
  name: (identifier) @property)
(member_expression
  (identifier) @property .)

(enum_struct_field
  name: (identifier) @property)
(named_pattern_field
  name: (identifier) @property)

; Enum variants
(enum_variant
  name: (identifier) @constant)

; Self
(self_expression) @variable.builtin

; Attributes
(attribute
  (identifier) @attribute)
"@" @attribute

; Operators
"+" @operator
"-" @operator
"*" @operator
"/" @operator
"%" @operator
"==" @operator
"!=" @operator
"<" @operator
">" @operator
"<=" @operator
">=" @operator
"&&" @operator
"||" @operator
"&" @operator
"|" @operator
"^" @operator
"<<" @operator
">>" @operator
"!" @operator
"!in" @keyword
"~" @operator
"=" @operator
"+=" @operator
"-=" @operator
"*=" @operator
"/=" @operator
"%=" @operator
"&=" @operator
"|=" @operator
"^=" @operator
"<<=" @operator
">>=" @operator
"->" @operator
"=>" @operator
"|>" @operator
"?." @operator
"??" @operator
"??=" @operator
".." @operator
"..=" @operator
"..." @operator
".*" @operator

; Punctuation
"(" @punctuation.bracket
")" @punctuation.bracket
"[" @punctuation.bracket
"]" @punctuation.bracket
"{" @punctuation.bracket
"}" @punctuation.bracket
"," @punctuation.delimiter
":" @punctuation.delimiter
"::" @punctuation.delimiter
"." @punctuation.delimiter

; Keywords — declarations
"func" @keyword.function
"struct" @keyword
"enum" @keyword
"interface" @keyword
"extend" @keyword
"conform" @keyword
"to" @keyword
"type" @keyword
"const" @keyword
"readonly" @keyword
"static" @keyword
"namespace" @keyword
"extern" @keyword

; Keywords — control flow
"if" @keyword.control
"else" @keyword.control
"match" @keyword.control
"case" @keyword.control
"for" @keyword.control
"while" @keyword.control
"loop" @keyword.control
(break_statement) @keyword.control
(continue_statement) @keyword.control
"return" @keyword.control
(using_statement "using" @keyword.control)
(errdefer_statement "errdefer" @keyword.control)
"defer" @keyword.control
"guard" @keyword.control

; Keywords — bindings
"var" @keyword
":=" @operator
"async" @keyword
"await" @keyword
"subscript" @keyword
"get" @keyword
"set" @keyword
"address" @keyword
"mut" @keyword

; Keywords — visibility
"public" @keyword
"private" @keyword
"internal" @keyword
"export" @keyword

; Keywords — other
"import" @keyword.control.import
"as" @keyword
"as?" @keyword
"as!" @keyword
"is" @keyword
"in" @keyword
(delegation_clause "by" @keyword field: (identifier) @property)
"where" @keyword
"any" @keyword
"unsafe" @keyword

; Callable types (Fn, AsyncFn)
(callable_type
  trait: (type_identifier) @type)
(callable_type
  trait: (identifier) @type)

; Never type
(never_type) @type.builtin

; Compiler directives
(compiler_directive
  (identifier) @keyword.directive)
"#" @keyword.directive

"class" @keyword
"final" @keyword
"override" @keyword

"init" @keyword
"required" @keyword
"convenience" @keyword

; Comments
(line_comment) @comment
(doc_comment) @comment.documentation

; Literals
(string_literal) @string
(escape_sequence) @string.escape
(rune_literal) @string.special
(number_literal) @number
(boolean_literal) @constant.builtin
(nil_literal) @constant.builtin

; Type identifiers
(type_identifier) @type
(simple_type) @type

; Function declarations
(function_declaration
  name: (identifier) @function)
(associated_function_declaration
  name: (identifier) @function)
(extern_function
  name: (identifier) @function)

; Function calls
(call_expression
  (identifier) @function.call)
(call_expression
  (member_expression
    (identifier) @function.call))

; Parameters
(parameter
  label: (identifier) @variable.parameter)
(parameter
  name: (identifier) @variable.parameter)
(closure_parameter
  name: (identifier) @variable.parameter)

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

; Enum variants
(enum_variant
  name: (identifier) @constant)

; Self
(self_expression) @variable.builtin
"self" @variable.builtin

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
"." @punctuation.delimiter

; Keywords — declarations
"func" @keyword.function
"struct" @keyword
"enum" @keyword
"interface" @keyword
"impl" @keyword
"type" @keyword
"const" @keyword
"static" @keyword
"namespace" @keyword
"extern" @keyword
"operator" @keyword

; Keywords — control flow
"if" @keyword.control
"else" @keyword.control
"match" @keyword.control
"case" @keyword.control
"for" @keyword.control
"while" @keyword.control
"loop" @keyword.control
"break" @keyword.control
"continue" @keyword.control
"return" @keyword.control
"defer" @keyword.control
"guard" @keyword.control

; Keywords — bindings
"let" @keyword
"var" @keyword
"mut" @keyword

; Keywords — visibility
"public" @keyword
"private" @keyword
"export" @keyword

; Keywords — other
"import" @keyword.control.import
"as" @keyword
"as?" @keyword
"as!" @keyword
"is" @keyword
"in" @keyword
"where" @keyword
"any" @keyword
"unsafe" @keyword
"for" @keyword.control
"readonly" @keyword

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

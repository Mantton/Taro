(function_declaration) @function.around
(function_declaration
  body: (block) @function.inside)

(method_declaration) @function.around
(method_declaration
  body: (block) @function.inside)

(struct_declaration) @class.around
(struct_body) @class.inside

(enum_declaration) @class.around
(enum_body) @class.inside

(interface_declaration) @class.around

(impl_declaration) @class.around
(declaration_body) @class.inside

(block) @block.around

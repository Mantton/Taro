(function_declaration) @function.around
(function_declaration
  body: (block) @function.inside)

(associated_function_declaration) @function.around
(associated_function_declaration
  body: (block) @function.inside)

(struct_declaration) @class.around
(struct_body) @class.inside

(enum_declaration) @class.around
(enum_body) @class.inside

(interface_declaration) @class.around
(interface_body) @class.inside

(impl_declaration) @class.around
(impl_body) @class.inside

(block) @block.around

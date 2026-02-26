
abbrev string_indirection : Type := String
abbrev alloc.string.String : Type := string_indirection

@[spec]
def rust_primitives.string.leak_string (s : String) : String := s

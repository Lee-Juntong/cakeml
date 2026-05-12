import Lake
open Lake DSL

package lean_type_sound where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib LeanTypeSound where
  roots := #[`LeanTypeSound]

require "leanprover-community" / mathlib @ git "v4.28.0"

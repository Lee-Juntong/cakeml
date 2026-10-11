/-
  Translation of fpSemScript.sml
  Definitions of the floating point operations used in CakeML.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast

open HOL4

/- HOL4:
Datatype:
  fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
End
-/
inductive fp_cmp where
  | FP_Less
  | FP_LessEqual
  | FP_Greater
  | FP_GreaterEqual
  | FP_Equal
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Datatype:
  fp_uop = FP_Abs | FP_Neg | FP_Sqrt
End
-/
inductive fp_uop where
  | FP_Abs
  | FP_Neg
  | FP_Sqrt
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Datatype:
  fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
End
-/
inductive fp_bop where
  | FP_Add
  | FP_Sub
  | FP_Mul
  | FP_Div
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Datatype:
  fp_top = FP_Fma
End
-/
inductive fp_top where
  | FP_Fma
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Definition fp_cmp_def:
  fp_cmp cmp =
  case cmp of
  | Lt  => fp64_lessThan
  | Leq => fp64_lessEqual
  | Gt  => fp64_greaterThan
  | Geq => fp64_greaterEqual
End
-/
def fp_cmp_fun : opb → word64 → word64 → Bool
  | .Lt  => fp64_lessThan
  | .Gt  => fp64_greaterThan
  | .Leq => fp64_lessEqual
  | .Geq => fp64_greaterEqual

/-
  Translation of locationScript.sml
  Defines location types for CakeML source positions.
-/
import LeanTypeSound.HOL4Prelude

open HOL4

/- HOL4:
Datatype: locn = UNKNOWNpt | EOFpt | POSN num num
End
-/
inductive locn where
  | UNKNOWNpt : locn
  | EOFpt : locn
  | POSN : Nat → Nat → locn
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Definition locnrow_def:
  locnrow (POSN r c) = r
End
-/
def locnrow : locn → Nat
  | .POSN r _ => r
  | _ => 0

/- HOL4:
Definition locn_rowupdate_def:
  locn_rowupdate f (POSN r c) = POSN (f r) c
End
-/
def locn_rowupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN (f r) c
  | l => l

/- HOL4:
Definition locncol_def:
  locncol (POSN r c) = c
End
-/
def locncol : locn → Nat
  | .POSN _ c => c
  | _ => 0

/- HOL4:
Definition locn_colupdate_def:
  locn_colupdate f (POSN r c) = POSN r (f c)
End
-/
def locn_colupdate (f : Nat → Nat) : locn → locn
  | .POSN r c => .POSN r (f c)
  | l => l

/- HOL4:
Datatype: locs = Locs locn locn
End
-/
inductive locs where
  | Locs : locn → locn → locs
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

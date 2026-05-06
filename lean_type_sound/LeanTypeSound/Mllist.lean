/-
  Translation of mllistScript.sml
  Pure functions for the List module.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Misc

open HOL4

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End
-/
def sort {α : Type} (cmp : α → α → ordering) (l : List α) : List α :=
  l.mergeSort (fun a b => cmp a b != .GREATER)

/- HOL4:
Definition nth_def:
  nth l i = EL i l
End
-/
def nth {α : Type} [Inhabited α] (l : List α) (i : Nat) : α :=
  EL i l

/- HOL4:
Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End
-/
def collate {α : Type} (f : α → α → ordering) : List α → List α → ordering
  | [], [] => .EQUAL
  | [], _ :: _ => .LESS
  | _ :: _, [] => .GREATER
  | h1 :: t1, h2 :: t2 =>
    if f h1 h2 == .EQUAL then collate f t1 t2
    else f h1 h2

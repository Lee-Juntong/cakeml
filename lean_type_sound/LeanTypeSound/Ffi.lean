/-
  Translation of ffiScript.sml
  Definition of the FFI type.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Misc
import LeanTypeSound.Mlstring

open HOL4

/- HOL4:
Datatype:
  ffi_outcome = FFI_failed | FFI_diverged
End
-/
inductive ffi_outcome where
  | FFI_failed
  | FFI_diverged
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
End
-/
inductive oracle_result (ffi : Type) where
  | Oracle_return : ffi → List word8 → oracle_result ffi
  | Oracle_final : ffi_outcome → oracle_result ffi

/- HOL4:
Datatype:
  shmem_op = MappedRead | MappedWrite
End
-/
inductive shmem_op where
  | MappedRead
  | MappedWrite
deriving Repr, BEq, Inhabited, DecidableEq

instance : LawfulBEq shmem_op where
  eq_of_beq := by
    intros a b h
    cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
  rfl := by intro a; cases a <;> rfl

/- HOL4:
Datatype:
  ffiname = ExtCall mlstring | SharedMem shmem_op
End
-/
inductive ffiname where
  | ExtCall : mlstring → ffiname
  | SharedMem : shmem_op → ffiname
deriving Repr, BEq, Inhabited

instance : LawfulBEq ffiname where
  eq_of_beq := by
    intros a b h
    cases a <;> cases b <;>
      first
      | (rename_i x y;
         have : x = y := LawfulBEq.eq_of_beq (show _ = true from h);
         subst this; rfl)
      | contradiction
  rfl := by
    intro a
    cases a with
    | ExtCall s => show (s == s) = true; simp
    | SharedMem o => show (o == o) = true; simp

/- HOL4:
Type oracle_function = ":'ffi -> word8 list -> word8 list -> 'ffi oracle_result"
-/
abbrev oracle_function (ffi : Type) := ffi → List word8 → List word8 → oracle_result ffi

/- HOL4:
Type oracle = ":ffiname -> 'ffi oracle_function"
-/
abbrev oracle (ffi : Type) := ffiname → oracle_function ffi

/- HOL4:
Datatype:
  io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
End
-/
inductive io_event where
  | IO_event : ffiname → List word8 → List (word8 × word8) → io_event
deriving Repr, BEq, Inhabited


/- HOL4:
Datatype:
  final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
End
-/
inductive final_event where
  | Final_event : ffiname → List word8 → List word8 → ffi_outcome → final_event
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  ffi_state =
  <| oracle      : 'ffi oracle
   ; ffi_state   : 'ffi
   ; io_events   : io_event list
   |>
End
-/
structure ffi_state (ffi : Type) where
  oracle_field : oracle ffi
  ffi_state_field : ffi
  io_events : List io_event

/- HOL4:
Datatype:
  ffi_result = FFI_return ('ffi ffi_state) (word8 list)
             | FFI_final final_event
End
-/
inductive ffi_result (ffi : Type) where
  | FFI_return : ffi_state ffi → List word8 → ffi_result ffi
  | FFI_final : final_event → ffi_result ffi

/- HOL4:
Definition call_FFI_def:
  call_FFI (st:'ffi ffi_state) s conf bytes = ...
End
-/
def call_FFI {ffi : Type} (st : ffi_state ffi) (s : ffiname) (conf : List word8)
    (bytes : List word8) : ffi_result ffi :=
  if s != ffiname.ExtCall (mlstring.strlit "") then
    match st.oracle_field s st.ffi_state_field conf bytes with
    | .Oracle_return ffi' bytes' =>
      if bytes'.length == bytes.length then
        .FFI_return
          { st with
            ffi_state_field := ffi'
            io_events := st.io_events ++ [io_event.IO_event s conf (bytes.zip bytes')] }
          bytes'
      else .FFI_final (final_event.Final_event s conf bytes .FFI_failed)
    | .Oracle_final outcome =>
      .FFI_final (final_event.Final_event s conf bytes outcome)
  else .FFI_return st bytes

/- HOL4:
Datatype:
  outcome = Success | Resource_limit_hit | FFI_outcome final_event
End
-/
inductive outcome where
  | Success
  | Resource_limit_hit
  | FFI_outcome : final_event → outcome
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  behaviour =
    Diverge (io_event llist)
  | Terminate outcome (io_event list)
  | Fail
End
-/
inductive behaviour where
  | Diverge : LazyList io_event → behaviour
  | Terminate : outcome → List io_event → behaviour
  | Fail : behaviour

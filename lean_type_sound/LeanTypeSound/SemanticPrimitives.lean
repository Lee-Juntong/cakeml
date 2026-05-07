/-
  Translation of semanticPrimitivesScript.sml
  Definitions of semantic primitives (values, operations, etc.)
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Misc
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.Ffi
import LeanTypeSound.FpSem
import LeanTypeSound.Mlstring

open HOL4

/- HOL4:
Datatype:
  stamp = TypeStamp conN num | ExnStamp num
End
-/
inductive stamp where
  | TypeStamp : conN → Nat → stamp
  | ExnStamp : Nat → stamp
deriving Repr, BEq, Inhabited

/- HOL4:
-- v and sem_env are mutually recursive
Datatype:
  sem_env = <| v : (modN, varN, 'v) namespace ; c : (modN, conN, (num # stamp)) namespace |>
End
Datatype:
  v = Litv lit | Conv (stamp option) (v list) | Closure (v sem_env) varN exp
    | Recclosure (v sem_env) ((varN # varN # exp) list) varN
    | Loc bool num | Vectorv (v list) | Env (v sem_env) (num # num)
End
-/
mutual
inductive v where
  | Litv : lit → v
  | Conv : Option stamp → List v → v
  | Closure : sem_env → varN → exp → v
  | Recclosure : sem_env → List (varN × varN × exp) → varN → v
  | Loc : Bool → Nat → v
  | Vectorv : List v → v
  | Env : sem_env → Nat × Nat → v

inductive sem_env where
  | mk : «namespace» modN varN v →
         «namespace» modN conN (Nat × stamp) → sem_env
end

-- Generic BEq for namespace via structural equality
def beq_namespace {m n v : Type} [BEq m] [BEq n] [BEq v] :
    «namespace» m n v → «namespace» m n v → Bool
  | .Bind vs1 ms1, .Bind vs2 ms2 =>
    beq_alist_inner vs1 vs2 && beq_mod_inner ms1 ms2
  termination_by ns _ => sizeOf ns
where
  beq_alist_inner : List (n × v) → List (n × v) → Bool
    | [], [] => true
    | (k1, v1) :: rest1, (k2, v2) :: rest2 =>
      k1 == k2 && v1 == v2 && beq_alist_inner rest1 rest2
    | _, _ => false
  beq_mod_inner : List (m × «namespace» m n v) →
      List (m × «namespace» m n v) → Bool
    | [], [] => true
    | (k1, n1) :: rest1, (k2, n2) :: rest2 =>
      k1 == k2 && beq_namespace n1 n2 && beq_mod_inner rest1 rest2
    | _, _ => false
  termination_by ms _ => sizeOf ms

instance {m n v : Type} [BEq m] [BEq n] [BEq v] : BEq («namespace» m n v) :=
  ⟨beq_namespace⟩

mutual
def beq_v : v → v → Bool
  | .Litv l1, .Litv l2 => l1 == l2
  | .Conv s1 vs1, .Conv s2 vs2 => s1 == s2 && beq_v_list vs1 vs2
  | .Closure e1 n1 ex1, .Closure e2 n2 ex2 =>
    beq_sem_env e1 e2 && n1 == n2 && ex1 == ex2
  | .Recclosure e1 fs1 n1, .Recclosure e2 fs2 n2 =>
    beq_sem_env e1 e2 && fs1 == fs2 && n1 == n2
  | .Loc b1 l1, .Loc b2 l2 => b1 == b2 && l1 == l2
  | .Vectorv vs1, .Vectorv vs2 => beq_v_list vs1 vs2
  | .Env e1 p1, .Env e2 p2 => beq_sem_env e1 e2 && p1 == p2
  | _, _ => false
  termination_by x _ => sizeOf x

def beq_v_list : List v → List v → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq_v x y && beq_v_list xs ys
  | _, _ => false
  termination_by xs _ => sizeOf xs

def beq_sem_env : sem_env → sem_env → Bool
  | .mk v1 c1, .mk v2 c2 => beq_namespace_v v1 v2 && beq_namespace_c c1 c2
  termination_by e _ => sizeOf e

def beq_namespace_v : «namespace» modN varN v → «namespace» modN varN v → Bool
  | .Bind vs1 ms1, .Bind vs2 ms2 =>
    beq_alist_v vs1 vs2 && beq_modlist_v ms1 ms2
  termination_by ns _ => sizeOf ns

def beq_alist_v : List (varN × v) → List (varN × v) → Bool
  | [], [] => true
  | (k1, v1) :: rest1, (k2, v2) :: rest2 =>
    k1 == k2 && beq_v v1 v2 && beq_alist_v rest1 rest2
  | _, _ => false
  termination_by xs _ => sizeOf xs

def beq_modlist_v : List (modN × «namespace» modN varN v) →
    List (modN × «namespace» modN varN v) → Bool
  | [], [] => true
  | (k1, n1) :: rest1, (k2, n2) :: rest2 =>
    k1 == k2 && beq_namespace_v n1 n2 && beq_modlist_v rest1 rest2
  | _, _ => false
  termination_by xs _ => sizeOf xs

def beq_namespace_c : «namespace» modN conN (Nat × stamp) →
    «namespace» modN conN (Nat × stamp) → Bool
  | .Bind vs1 ms1, .Bind vs2 ms2 =>
    vs1 == vs2 && beq_modlist_c ms1 ms2
  termination_by ns _ => sizeOf ns

def beq_modlist_c : List (modN × «namespace» modN conN (Nat × stamp)) →
    List (modN × «namespace» modN conN (Nat × stamp)) → Bool
  | [], [] => true
  | (k1, n1) :: rest1, (k2, n2) :: rest2 =>
    k1 == k2 && beq_namespace_c n1 n2 && beq_modlist_c rest1 rest2
  | _, _ => false
  termination_by xs _ => sizeOf xs
end

instance : BEq v := ⟨beq_v⟩
instance : BEq sem_env := ⟨beq_sem_env⟩
instance : Inhabited v := ⟨.Litv (.IntLit 0)⟩
instance : Inhabited sem_env := ⟨.mk (.Bind [] []) (.Bind [] [])⟩

namespace sem_env
def v_ (e : sem_env) : «namespace» modN varN v :=
  match e with | .mk v _ => v
def c (e : sem_env) : «namespace» modN conN (Nat × stamp) :=
  match e with | .mk _ c => c
end sem_env

def sem_env_v (e : sem_env) := e.v_
def sem_env_c (e : sem_env) := e.c

/- HOL4:
Type env_ctor = ``: (modN, conN, (num # stamp)) namespace``
-/
abbrev env_ctor := «namespace» modN conN (Nat × stamp)

/- HOL4:
Type env_val = ``: (modN, varN, v) namespace``
-/
abbrev env_val := «namespace» modN varN v

-- Exception stamps
/- HOL4:
Definition bind_stamp_def: bind_stamp = ExnStamp 0
End
-/
def bind_stamp : stamp := .ExnStamp 0
def chr_stamp : stamp := .ExnStamp 1
def div_stamp : stamp := .ExnStamp 2
def subscript_stamp : stamp := .ExnStamp 3

def bind_exn_v : v := .Conv (some bind_stamp) []
def chr_exn_v : v := .Conv (some chr_stamp) []
def div_exn_v : v := .Conv (some div_stamp) []
def sub_exn_v : v := .Conv (some subscript_stamp) []

def bool_type_num : Nat := 0
def list_type_num : Nat := 1

-- Result types
/- HOL4:
Datatype:
  abort = Rtype_error | Rtimeout_error | Rffi_error final_event
End
-/
inductive abort where
  | Rtype_error : abort
  | Rtimeout_error : abort
  | Rffi_error : final_event → abort
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  error_result = Rraise 'a | Rabort abort
End
-/
inductive error_result (α : Type) where
  | Rraise : α → error_result α
  | Rabort : abort → error_result α
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  result = Rval 'a | Rerr ('b error_result)
End
-/
inductive result (α β : Type) where
  | Rval : α → result α β
  | Rerr : error_result β → result α β
deriving Repr, BEq, Inhabited

-- Store types
/- HOL4:
Datatype:
  store_v = Refv 'a | W8array (word8 list) | Varray ('a list) | Thunk thunk_mode 'a
End
-/
inductive store_v (α : Type) where
  | Refv : α → store_v α
  | W8array : List word8 → store_v α
  | Varray : List α → store_v α
  | Thunk : thunk_mode → α → store_v α
deriving Repr, BEq, Inhabited

def store_v_same_type {α : Type} : store_v α → store_v α → Bool
  | .Refv _, .Refv _ => true
  | .W8array _, .W8array _ => true
  | .Varray _, .Varray _ => true
  | .Thunk .NotEvaluated _, .Thunk _ _ => true
  | _, _ => false

abbrev store (α : Type) := List (store_v α)

def store_lookup {α : Type} (l : Nat) (st : List (store_v α)) : Option (store_v α) :=
  if l < st.length then some (EL l st) else none

def store_alloc {α : Type} (val_ : store_v α) (st : List (store_v α)) :
    List (store_v α) × Nat :=
  (st ++ [val_], st.length)

def store_assign {α : Type} (n : Nat) (val_ : store_v α) (st : List (store_v α)) :
    Option (List (store_v α)) :=
  if n < st.length && store_v_same_type (EL n st) val_ then
    some (LUPDATE val_ n st)
  else none

-- Eval state types
abbrev compiler_args := (Nat × Nat) × v × List dec
abbrev compiler_fun := compiler_args → Option (v × List word8 × List word64)

structure eval_decs_state where
  compiler : compiler_fun
  compiler_state : v
  env_id_counter : Nat × Nat × Nat
  decode_decs : v → Option (List dec)

abbrev eval_oracle_fun := Nat → compiler_args

structure eval_oracle_state where
  oracle_field : eval_oracle_fun
  custom_do_eval : List v → eval_oracle_fun →
    Option ((Nat × Nat) × eval_oracle_fun × List dec)
  envs : List (List sem_env)
  generation : Nat

inductive eval_state where
  | EvalDecs : eval_decs_state → eval_state
  | EvalOracle : eval_oracle_state → eval_state

-- The main state type
/- HOL4:
Datatype:
  state = <| clock : num ; refs : v store ; ffi : 'ffi ffi_state
           ; next_type_stamp : num ; next_exn_stamp : num
           ; eval_state : eval_state option |>
End
-/
structure cml_state (ffi : Type) where
  clock : Nat
  refs : store v
  ffi : ffi_state ffi
  next_type_stamp : Nat
  next_exn_stamp : Nat
  eval_state_field : Option eval_state

-- Pattern matching result
/- HOL4:
Datatype:
  match_result = No_match | Match_type_error | Match 'a
End
-/
inductive match_result (α : Type) where
  | No_match : match_result α
  | Match_type_error : match_result α
  | Match : α → match_result α
deriving Repr, BEq, Inhabited

-- Constructor operations
def do_con_check (cenv : env_ctor) (n_opt : Option (cml_id modN conN)) (l : Nat) : Bool :=
  match n_opt with
  | none => true
  | some n => match nsLookup cenv n with
    | none => false
    | some (l', _) => l == l'

def one_con_check (envc : env_ctor) : exp → Bool
  | .Con cn es => do_con_check envc cn es.length
  | _ => true

def build_conv (envC : env_ctor) (cn : Option (cml_id modN conN)) (vs : List v) :
    Option v :=
  match cn with
  | none => some (.Conv none vs)
  | some id_ =>
    match nsLookup envC id_ with
    | none => none
    | some (_, stmp) => some (.Conv (some stmp) vs)

def lit_same_type : lit → lit → Bool
  | .IntLit _, .IntLit _ => true
  | .Char _, .Char _ => true
  | .StrLit _, .StrLit _ => true
  | .Word8 _, .Word8 _ => true
  | .Word64 _, .Word64 _ => true
  | .Float64 _, .Float64 _ => true
  | _, _ => false

def same_type : stamp → stamp → Bool
  | .TypeStamp _ n1, .TypeStamp _ n2 => n1 == n2
  | .ExnStamp _, .ExnStamp _ => true
  | _, _ => false

def same_ctor (s1 s2 : stamp) : Bool := s1 == s2

def ctor_same_type : Option stamp → Option stamp → Bool
  | none, none => true
  | some s1, some s2 => same_type s1 s2
  | _, _ => false

def Boolv (b : Bool) : v :=
  if b then .Conv (some (.TypeStamp (mlstring.strlit "True") bool_type_num)) []
  else .Conv (some (.TypeStamp (mlstring.strlit "False") bool_type_num)) []

-- Pattern matching
/- HOL4:
Definition pmatch_def: ...
End
-/
mutual
def pmatch (envC : env_ctor) (s : store v) : pat → v → alist varN v →
    match_result (alist varN v)
  | .Pany, _, env => .Match env
  | .Pvar x, v', env => .Match ((x, v') :: env)
  | .Plit l, .Litv l', env =>
    if l == l' then .Match env
    else if lit_same_type l l' then .No_match
    else .Match_type_error
  | .Pcon (some n) ps, .Conv (some stamp') vs, env =>
    match nsLookup envC n with
    | none => .Match_type_error
    | some (l, stmp) =>
      if same_type stmp stamp' && ps.length == l then
        if same_ctor stmp stamp' then
          if vs.length == l then pmatch_list envC s ps vs env
          else .Match_type_error
        else .No_match
      else .Match_type_error
  | .Pcon none ps, .Conv none vs, env =>
    if ps.length == vs.length then pmatch_list envC s ps vs env
    else .Match_type_error
  | .Pref p, .Loc _ lnum, env =>
    match store_lookup lnum s with
    | none => .Match_type_error
    | some (.Refv v') => pmatch envC s p v' env
    | some _ => .Match_type_error
  | .Pas p i, v', env => pmatch envC s p v' ((i, v') :: env)
  | .Ptannot p _, v', env => pmatch envC s p v' env
  | _, _, _ => .Match_type_error
  termination_by p _ _ => sizeOf p

def pmatch_list (envC : env_ctor) (s : store v) :
    List pat → List v → alist varN v → match_result (alist varN v)
  | [], [], env => .Match env
  | p :: ps, v' :: vs, env =>
    match pmatch envC s p v' env with
    | .No_match =>
      match pmatch_list envC s ps vs env with
      | .No_match => .No_match
      | .Match_type_error => .Match_type_error
      | .Match _ => .No_match
    | .Match_type_error => .Match_type_error
    | .Match env' => pmatch_list envC s ps vs env'
  | _, _, _ => .Match_type_error
  termination_by ps _ _ => sizeOf ps
end

def can_pmatch_all (envC : env_ctor) (refs : store v) : List pat → v → Bool
  | [], _ => true
  | p :: ps, v' =>
    if (match pmatch envC refs p v' [] with | .Match_type_error => true | _ => false) then false
    else can_pmatch_all envC refs ps v'

-- Recursive env building
def build_rec_env (funs : List (varN × varN × exp)) (cl_env : sem_env)
    (add_to_env : «namespace» modN varN v) : «namespace» modN varN v :=
  funs.foldr (fun (f, _, _) env' => nsBind f (.Recclosure cl_env funs f) env') add_to_env

def find_recfun (n : varN) : List (varN × varN × exp) → Option (varN × exp)
  | [] => none
  | (f, x, e) :: funs' => if f == n then some (x, e) else find_recfun n funs'

-- Equality
/- HOL4:
Datatype:
  eq_result = Eq_val bool | Eq_type_error
End
-/
inductive eq_result where
  | Eq_val : Bool → eq_result
  | Eq_type_error : eq_result
deriving Repr, BEq, Inhabited

mutual
def do_eq : v → v → eq_result
  | .Litv l1, .Litv l2 =>
    if lit_same_type l1 l2 then .Eq_val (l1 == l2) else .Eq_type_error
  | .Loc b1 l1, .Loc b2 l2 =>
    if b1 && b2 then .Eq_val (l1 == l2) else .Eq_type_error
  | .Conv cn1 vs1, .Conv cn2 vs2 =>
    if cn1 == cn2 && vs1.length == vs2.length then do_eq_list vs1 vs2
    else if ctor_same_type cn1 cn2 then .Eq_val false
    else .Eq_type_error
  | .Vectorv vs1, .Vectorv vs2 =>
    if vs1.length == vs2.length then do_eq_list vs1 vs2 else .Eq_val false
  | .Closure _ _ _, .Closure _ _ _ => .Eq_val true
  | .Closure _ _ _, .Recclosure _ _ _ => .Eq_val true
  | .Recclosure _ _ _, .Closure _ _ _ => .Eq_val true
  | .Recclosure _ _ _, .Recclosure _ _ _ => .Eq_val true
  | .Env _ (gen1, id1), .Env _ (gen2, id2) => .Eq_val (gen1 == gen2 && id1 == id2)
  | _, _ => .Eq_type_error
  termination_by v1 _ => sizeOf v1

def do_eq_list : List v → List v → eq_result
  | [], [] => .Eq_val true
  | v1 :: vs1, v2 :: vs2 =>
    match do_eq v1 v2 with
    | .Eq_val r => if !r then .Eq_val false else do_eq_list vs1 vs2
    | .Eq_type_error => .Eq_type_error
  | _, _ => .Eq_val false
  termination_by vs1 _ => sizeOf vs1
end

-- Function application
def do_opapp (vs : List v) : Option (sem_env × exp) :=
  match vs with
  | [.Closure env n e, val_] =>
    some (.mk (nsBind n val_ env.v_) env.c, e)
  | [.Recclosure env' funs n', val_] =>
    if ALL_DISTINCT (funs.map fun (f, _, _) => f) then
      match find_recfun n' funs with
      | none => none
      | some (n, e) =>
        some (.mk (nsBind n val_ (build_rec_env funs env' env'.v_)) env'.c, e)
    else none
  | _ => none

-- Value/list conversions
def v_to_list : v → Option (List v)
  | .Conv (some stmp) [] =>
    if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
  | .Conv (some stmp) [v1, v2] =>
    if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
      match v_to_list v2 with
      | none => none
      | some vs => some (v1 :: vs)
    else none
  | _ => none
  termination_by val => sizeOf val

def list_to_v : List v → v
  | [] => .Conv (some (.TypeStamp (mlstring.strlit "[]") list_type_num)) []
  | x :: xs => .Conv (some (.TypeStamp (mlstring.strlit "::") list_type_num)) [x, list_to_v xs]

def v_to_char_list : v → Option (List Char)
  | .Conv (some stmp) [] =>
    if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
  | .Conv (some stmp) [.Litv (.Char c), v'] =>
    if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
      match v_to_char_list v' with
      | none => none
      | some cs => some (c :: cs)
    else none
  | _ => none
  termination_by val => sizeOf val

def vs_to_string : List v → Option mlstring
  | [] => some (mlstring.strlit "")
  | .Litv (.StrLit s1) :: vs =>
    match vs_to_string vs with
    | none => none
    | some s2 => some (strcat s1 s2)
  | _ :: _ => none

def nat_to_v (n : Nat) : v := .Litv (.IntLit (Int.ofNat n))

def maybe_all_list {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: vs =>
    match maybe_all_list vs with
    | none => none
    | some xs => some (x :: xs)

def v_to_word8 : v → Option word8
  | .Litv (.Word8 w) => some w
  | _ => none

def v_to_word8_list (val_ : v) : Option (List word8) :=
  match v_to_list val_ with
  | none => none
  | some xs => maybe_all_list (xs.map v_to_word8)

def v_to_word64 : v → Option word64
  | .Litv (.Word64 w) => some w
  | _ => none

def v_to_word64_list (val_ : v) : Option (List word64) :=
  match v_to_list val_ with
  | none => none
  | some xs => maybe_all_list (xs.map v_to_word64)

-- Shift lookups
def shift8_lookup : shift → word8 → Nat → word8
  | .Lsl => word_lsl_8
  | .Lsr => word_lsr_8
  | .Asr => word_asr_8
  | .Ror => word_ror_8

def shift64_lookup : shift → word64 → Nat → word64
  | .Lsl => word_lsl_64
  | .Lsr => word_lsr_64
  | .Asr => word_asr_64
  | .Ror => word_ror_64

/- HOL4: Type store_ffi = ": 'v store # 'ffi ffi_state" -/
abbrev store_ffi (α : Type) (ffi : Type) := store α × ffi_state ffi

/- HOL4:
Definition thunk_op_def:
  thunk_op (s: v store_v list, t: 'ffi ffi_state) th_op vs =
    case (th_op,vs) of
    | (AllocThunk m, [v]) =>
        (let (s',n) = store_alloc (Thunk m v) s in
           SOME ((s',t), Rval (Loc F n)))
    | (UpdateThunk m, [Loc _ lnum; v]) =>
        (case store_assign lnum (Thunk m v) s of
         | SOME s' => SOME ((s',t), Rval (Conv NONE []))
         | NONE => NONE)
    | _ => NONE
End
-/
def thunk_op_fun {ffi : Type} (st : store v × ffi_state ffi) (th_op : thunk_op) (vs : List v) :
    Option ((store v × ffi_state ffi) × result v v) :=
  match th_op, vs with
  | .AllocThunk m, [val_] =>
    let (s', n) := store_alloc (.Thunk m val_) st.1
    some ((s', st.2), .Rval (.Loc false n))
  | .UpdateThunk m, [.Loc _ lnum, val_] =>
    match store_assign lnum (.Thunk m val_) st.1 with
    | some s' => some ((s', st.2), .Rval (.Conv none []))
    | none => none
  | _, _ => none

/- HOL4:
Definition check_type_def:
  check_type BoolT v = (v = Boolv T ∨ v = Boolv F) ∧
  check_type IntT v = (∃i. v = Litv (IntLit i)) ∧
  check_type CharT v = (∃c. v = Litv (Char c)) ∧
  check_type StrT v = (∃s. v = Litv (StrLit s)) ∧
  check_type (WordT W8) v = (∃w. v = Litv (Word8 w)) ∧
  check_type (WordT W64) v = (∃w. v = Litv (Word64 w)) ∧
  check_type Float64T v = (∃w. v = Litv (Float64 w))
End
-/
def check_type (ty : prim_type) (val_ : v) : Bool :=
  match ty, val_ with
  | .BoolT, val_ => val_ == Boolv true || val_ == Boolv false
  | .IntT, .Litv (.IntLit _) => true
  | .CharT, .Litv (.Char _) => true
  | .StrT, .Litv (.StrLit _) => true
  | .WordT .W8, .Litv (.Word8 _) => true
  | .WordT .W64, .Litv (.Word64 _) => true
  | .Float64T, .Litv (.Float64 _) => true
  | _, _ => false

/- HOL4:
Definition dest_Litv_def[simp]:
  dest_Litv (Litv v) = SOME v ∧
  dest_Litv _ = NONE
End
-/
def dest_Litv : v → Option lit
  | .Litv l => some l
  | _ => none

/- HOL4:
Definition the_Litv_IntLit_def[simp]:
  the_Litv_IntLit (Litv (IntLit i)) = i
End
-/
def the_Litv_IntLit : v → Int
  | .Litv (.IntLit i) => i
  | _ => default

/- HOL4:
Definition the_Litv_Word8_def[simp]:
  the_Litv_Word8 (Litv (Word8 w)) = w
End
-/
def the_Litv_Word8 : v → word8
  | .Litv (.Word8 w) => w
  | _ => default

/- HOL4:
Definition the_Litv_Word64_def[simp]:
  the_Litv_Word64 (Litv (Word64 w)) = w
End
-/
def the_Litv_Word64 : v → word64
  | .Litv (.Word64 w) => w
  | _ => default

/- HOL4:
Definition the_Litv_Float64_def[simp]:
  the_Litv_Float64 (Litv (Float64 w)) = w
End
-/
def the_Litv_Float64 : v → word64
  | .Litv (.Float64 w) => w
  | _ => default

/- HOL4:
Definition the_Litv_Char_def[simp]:
  the_Litv_Char (Litv (Char c)) = c
End
-/
def the_Litv_Char : v → Char
  | .Litv (.Char c) => c
  | _ => default

/- HOL4:
Definition the_Boolv_def[simp]:
  the_Boolv v = (v = Boolv T)
End
-/
def the_Boolv (val_ : v) : Bool := val_ == Boolv true

/- HOL4:
Definition num_cmp_def[simp]:
  num_cmp Lt  i j = (i <  j:num) ∧
  num_cmp Leq i j = (i <= j) ∧
  num_cmp Gt  i j = (i >  j) ∧
  num_cmp Geq i j = (i >= j)
End
-/
def num_cmp : opb → Nat → Nat → Bool
  | .Lt,  i, j => i < j
  | .Leq, i, j => i <= j
  | .Gt,  i, j => i > j
  | .Geq, i, j => i >= j

/- HOL4:
Definition int_cmp_def[simp]:
  int_cmp Lt  i j = (i <  j:int) ∧
  int_cmp Leq i j = (i <= j) ∧
  int_cmp Gt  i j = (i >  j) ∧
  int_cmp Geq i j = (i >= j)
End
-/
def int_cmp : opb → Int → Int → Bool
  | .Lt,  i, j => i < j
  | .Leq, i, j => decide (i ≤ j)
  | .Gt,  i, j => j < i
  | .Geq, i, j => decide (j ≤ i)

/- HOL4:
Datatype:
  exp_or_val = Exp exp | Val v
End
-/
inductive exp_or_val where
  | Exp : exp → exp_or_val
  | Val : v → exp_or_val

-- Logical operations
def do_log (l : lop) (val_ : v) (e : exp) : Option exp_or_val :=
  if (l == .Andalso && val_ == Boolv true) || (l == .Orelse && val_ == Boolv false) then
    some (.Exp e)
  else if (l == .Andalso && val_ == Boolv false) || (l == .Orelse && val_ == Boolv true) then
    some (.Val val_)
  else none

def do_if (val_ : v) (e1 e2 : exp) : Option exp :=
  if val_ == Boolv true then some e1
  else if val_ == Boolv false then some e2
  else none

-- Type definition building
def build_constrs (stmp : Nat) (condefs : List (conN × List ast_t)) :
    List (conN × Nat × stamp) :=
  condefs.map fun (cn, ts) => (cn, ts.length, stamp.TypeStamp cn stmp)

def build_tdefs (next_stamp : Nat) : type_def → «namespace» modN conN (Nat × stamp)
  | [] => alist_to_ns []
  | (_, _, condefs) :: tds =>
    nsAppend (build_tdefs (next_stamp + 1) tds)
      (alist_to_ns ((build_constrs next_stamp condefs).reverse))

def check_dup_ctors : List tvarN × typeN × List (conN × List ast_t) → Bool
  | (_, _, condefs) =>
    ALL_DISTINCT (condefs.map fun (n, _) => n)

def combine_dec_result {α : Type} (env : sem_env) :
    result sem_env α → result sem_env α
  | .Rval env' => .Rval (.mk (nsAppend env'.v_ env.v_) (nsAppend env'.c env.c))
  | .Rerr e => .Rerr e

def extend_dec_env (new_env env : sem_env) : sem_env :=
  .mk (nsAppend new_env.v_ env.v_) (nsAppend new_env.c env.c)

/- HOL4:
Datatype:
  dest_thunk_ret = BadRef | NotThunk | IsThunk thunk_mode v
End
-/
inductive dest_thunk_ret where
  | BadRef : dest_thunk_ret
  | NotThunk : dest_thunk_ret
  | IsThunk : thunk_mode → v → dest_thunk_ret

def dest_thunk : List v → store v → dest_thunk_ret
  | [.Loc _ n], st =>
    match store_lookup n st with
    | none => .BadRef
    | some (.Thunk .Evaluated val_) => .IsThunk .Evaluated val_
    | some (.Thunk .NotEvaluated val_) => .IsThunk .NotEvaluated val_
    | some _ => .NotThunk
  | _, _ => .NotThunk

def update_thunk : List v → store v → List v → Option (store v)
  | [.Loc _ n], st, [val_] =>
    match dest_thunk [val_] st with
    | .NotThunk => store_assign n (.Thunk .Evaluated val_) st
    | _ => none
  | _, _, _ => none

-- Eval-related (complex, stubbed out for brevity of key parts)

def lookup_env (s : eval_oracle_state) (ij : Nat × Nat) : Option sem_env :=
  match oEL ij.1 s.envs with
  | none => none
  | some gen_envs => oEL ij.2 gen_envs

def add_decs_generation (s : eval_decs_state) : eval_decs_state :=
  match s.env_id_counter with
  | (_, _, next_gen) =>
    { s with env_id_counter := (next_gen, 0, next_gen + 1) }

def add_env_generation (s : eval_oracle_state) : eval_oracle_state :=
  { s with generation := s.envs.length, envs := s.envs ++ [[]] }

def declare_env (es : Option eval_state) (env : sem_env) :
    Option (v × Option eval_state) :=
  match es with
  | none => none
  | some (.EvalDecs s) =>
    match s.env_id_counter with
    | (cur_gen, next_id, next_gen) =>
      some (.Env env (cur_gen, next_id),
            some (.EvalDecs { s with env_id_counter := (cur_gen, next_id + 1, next_gen) }))
  | some (.EvalOracle s') =>
    match oEL s'.generation s'.envs with
    | none => none
    | some gen_envs =>
      some (.Conv none [nat_to_v s'.generation, nat_to_v gen_envs.length],
            some (.EvalOracle
              { s' with envs := LUPDATE (gen_envs ++ [env]) s'.generation s'.envs }))

/- HOL4:
Definition concrete_v_def:
  concrete_v v ⇔ case v of
                 | Loc _ _ => T | Litv _ => T
                 | Conv v_ vs => concrete_v_list vs
                 | Vectorv vs => concrete_v_list vs
                 | _ => F ∧
  concrete_v_list [] ⇔ T ∧
  concrete_v_list (v::vs) ⇔ concrete_v v ∧ concrete_v_list vs
End
-/
mutual
def concrete_v : v → Bool
  | .Loc _ _ => true
  | .Litv _ => true
  | .Conv _ vs => concrete_v_list vs
  | .Vectorv vs => concrete_v_list vs
  | _ => false
  termination_by val => sizeOf val

def concrete_v_list : List v → Bool
  | [] => true
  | val_ :: vs => concrete_v val_ && concrete_v_list vs
  termination_by vs => sizeOf vs
end

/- HOL4:
Definition compiler_agrees_def:
  compiler_agrees f args (st_v, bs_v, ws_v) ⇔
    case (f args, args, v_to_word8_list bs_v, v_to_word64_list ws_v) of
    | (SOME (st, c_bs, c_ws), (_, prev_st_v, _), SOME bs, SOME ws) =>
        st = st_v ∧ c_bs = bs ∧ c_ws = ws ∧ concrete_v st_v ∧ concrete_v prev_st_v
    | _ => F
End
-/
def compiler_agrees (f : compiler_fun) (args : compiler_args)
    (triple : v × v × v) : Bool :=
  let (st_v, bs_v, ws_v) := triple
  let prev_st_v := args.2.1
  match f args, v_to_word8_list bs_v, v_to_word64_list ws_v with
  | some (st, c_bs, c_ws), some bs, some ws =>
      st == st_v && c_bs == bs && c_ws == ws &&
      concrete_v st_v && concrete_v prev_st_v
  | _, _, _ => false

/- HOL4:
Definition do_eval_def:
  do_eval vs es =
    case (es, vs) of
    | (SOME (EvalDecs s), [Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) =>
      (case s.decode_decs decs_v of
        NONE => NONE
       | SOME decs =>
         if st_v = s.compiler_state ∧ concrete_v decs_v ∧
            compiler_agrees s.compiler (id, st_v, decs) (st_v2, bs_v, ws_v)
         then SOME (env, decs,
                    SOME (EvalDecs (add_decs_generation
                            (s with compiler_state := st_v2))))
         else NONE)
    | (SOME (EvalOracle s'), vs) =>
      (case s'.custom_do_eval vs s'.oracle of
        NONE => NONE
       | SOME (env_id, oracle, decs) =>
           case lookup_env s' env_id of
             NONE => NONE
           | SOME env =>
             SOME (env, decs,
                   SOME (EvalOracle (add_env_generation
                           (s' with oracle := oracle)))))
    | _ => NONE
End
-/
def do_eval (vs : List v) (es : Option eval_state) :
    Option (sem_env × List dec × Option eval_state) :=
  match es, vs with
  | some (.EvalDecs s), [.Env env id_, st_v, decs_v, st_v2, bs_v, ws_v] =>
    match s.decode_decs decs_v with
    | none => none
    | some decs =>
      if st_v == s.compiler_state ∧ concrete_v decs_v ∧
         compiler_agrees s.compiler (id_, st_v, decs) (st_v2, bs_v, ws_v) then
        some (env, decs,
              some (.EvalDecs (add_decs_generation
                      { s with compiler_state := st_v2 })))
      else none
  | some (.EvalOracle s'), vs =>
    match s'.custom_do_eval vs s'.oracle_field with
    | none => none
    | some (env_id, oracle, decs) =>
      match lookup_env s' env_id with
      | none => none
      | some env =>
        some (env, decs,
              some (.EvalOracle (add_env_generation
                      { s' with oracle_field := oracle })))
  | _, _ => none

/- HOL4:
Definition reset_env_generation_def:
  reset_env_generation prior_es es =
    case (prior_es, es) of
    | (SOME (EvalDecs prior_s'), SOME (EvalDecs s')) =>
      (case (prior_s'.env_id_counter, s'.env_id_counter) of
        ((cur_gen, next_id, _), (_, _, next_gen)) =>
          SOME (EvalDecs (s' with env_id_counter := (cur_gen, next_id, next_gen))))
    | (SOME (EvalOracle prior_s), SOME (EvalOracle s)) =>
      SOME (EvalOracle (s with generation := prior_s.generation))
    | _ => es
End
-/
def reset_env_generation (prior_es es : Option eval_state) : Option eval_state :=
  match prior_es, es with
  | some (.EvalDecs prior_s'), some (.EvalDecs s') =>
    let (cur_gen, next_id, _) := prior_s'.env_id_counter
    let (_, _, next_gen) := s'.env_id_counter
    some (.EvalDecs { s' with env_id_counter := (cur_gen, next_id, next_gen) })
  | some (.EvalOracle prior_s), some (.EvalOracle s) =>
    some (.EvalOracle { s with generation := prior_s.generation })
  | _, _ => es

/- HOL4:
Definition copy_array_def:
  copy_array (src, srcoff) len d =
    if srcoff < 0 ∨ len < 0 ∨ LENGTH src < Num (ABS (srcoff + len))
    then NONE
    else
      let copied = TAKE (Num (ABS len)) (DROP (Num (ABS srcoff)) src)
      in case d of
         | NONE => SOME copied
         | SOME (dst, dstoff) =>
           if dstoff < 0 ∨ LENGTH dst < Num (ABS (dstoff + len)) then NONE
           else SOME (TAKE (Num (ABS dstoff)) dst ⧺ copied ⧺
                       DROP (Num (ABS (dstoff + len))) dst)
End
-/
def copy_array {α : Type} (src_off : List α × Int) (len : Int)
    (d : Option (List α × Int)) : Option (List α) :=
  let (src, srcoff) := src_off
  if srcoff < 0 ∨ len < 0 ∨ (src.length : Int) < (srcoff + len).natAbs then
    none
  else
    let copied := TAKE len.natAbs (DROP srcoff.natAbs src)
    match d with
    | none => some copied
    | some (dst, dstoff) =>
      if dstoff < 0 ∨ (dst.length : Int) < (dstoff + len).natAbs then none
      else
        some (TAKE dstoff.natAbs dst ++ copied ++
              DROP (dstoff + len).natAbs dst)

/- HOL4:
Definition ws_to_chars_def:
  ws_to_chars (ws:word8 list) = MAP (λw. CHR (w2n w)) ws
End
-/
def ws_to_chars (ws : List word8) : List Char :=
  ws.map fun w => CHR (w2n_8 w)

/- HOL4:
Definition chars_to_ws_def:
  chars_to_ws cs = MAP (λc. i2w (&ORD c)) cs :word8 list
End
-/
def chars_to_ws (cs : List Char) : List word8 :=
  cs.map fun c => i2w_8 (Int.ofNat (ORD c))

/- HOL4:
Definition xor_bytes_def:
  xor_bytes [] bs2 = SOME (bs2:word8 list) ∧
  xor_bytes bs1 [] = NONE ∧
  xor_bytes (b1::bs1) (b2::bs2) =
    case xor_bytes bs1 bs2 of
    | NONE => NONE
    | SOME rest => SOME (word_xor b1 b2 :: rest)
End
-/
def xor_bytes : List word8 → List word8 → Option (List word8)
  | [], bs2 => some bs2
  | _, [] => none
  | b1 :: bs1, b2 :: bs2 =>
    match xor_bytes bs1 bs2 with
    | none => none
    | some rest => some (word_xor_8 b1 b2 :: rest)

/- HOL4:
Definition do_test_def:
  do_test Equal ty v1 v2 =
    (if check_type ty v1 ∧ check_type ty v2 then
       (if ty = Float64T
        then Eq_val (fp64_equal (the_Litv_Float64 v1) (the_Litv_Float64 v2))
        else do_eq v1 v2)
     else Eq_type_error) ∧
  do_test (Compare cmp) ty v1 v2 =
    (case (ty, dest_Litv v1, dest_Litv v2) of
     | (IntT,     SOME (IntLit i),  SOME (IntLit j))  => Eq_val (int_cmp cmp i j)
     | (CharT,    SOME (Char c),    SOME (Char d))    => Eq_val (num_cmp cmp (ORD c) (ORD d))
     | (WordT W8, SOME (Word8 w),   SOME (Word8 v))   => Eq_val (num_cmp cmp (w2n w) (w2n v))
     | (Float64T, SOME (Float64 w), SOME (Float64 v)) => Eq_val (fp_cmp cmp w v)
     | _ => Eq_type_error) ∧
  do_test _ ty v1 v2 = Eq_type_error
End
-/
def do_test : test → prim_type → v → v → eq_result
  | .Equal, ty, v1, v2 =>
    if check_type ty v1 && check_type ty v2 then
      if ty == .Float64T then
        .Eq_val (fp64_equal (the_Litv_Float64 v1) (the_Litv_Float64 v2))
      else do_eq v1 v2
    else .Eq_type_error
  | .Compare cmp, ty, v1, v2 =>
    match ty, dest_Litv v1, dest_Litv v2 with
    | .IntT, some (.IntLit i), some (.IntLit j) => .Eq_val (int_cmp cmp i j)
    | .CharT, some (.Char c), some (.Char d) => .Eq_val (num_cmp cmp (ORD c) (ORD d))
    | .WordT .W8, some (.Word8 w), some (.Word8 u) => .Eq_val (num_cmp cmp (w2n_8 w) (w2n_8 u))
    | .Float64T, some (.Float64 w), some (.Float64 u) => .Eq_val (fp_cmp_fun cmp w u)
    | _, _, _ => .Eq_type_error
  | _, _, _, _ => .Eq_type_error

/- HOL4:
Definition do_arith_def:
  (do_arith a Float64T vals = ...) ∧
  (do_arith a IntT vals = ...) ∧
  (do_arith a (WordT W8) vals = ...) ∧
  (do_arith a (WordT W64) vals = ...) ∧
  (do_arith a BoolT vals = ...) ∧
  (do_arith a _ vals = NONE)
End
-/
def do_arith : arith → prim_type → List v → Option (v ⊕ v)
  | a, .Float64T, vals =>
    match a, vals.map the_Litv_Float64 with
    | .Abs,  [v1]       => some (.inr (.Litv (.Float64 (fp64_abs v1))))
    | .Neg,  [v1]       => some (.inr (.Litv (.Float64 (fp64_negate v1))))
    | .Sqrt, [v1]       => some (.inr (.Litv (.Float64 (fp64_sqrt roundTiesToEven v1))))
    | .Add,  [v1, v2]   => some (.inr (.Litv (.Float64 (fp64_add roundTiesToEven v1 v2))))
    | .Sub,  [v1, v2]   => some (.inr (.Litv (.Float64 (fp64_sub roundTiesToEven v1 v2))))
    | .Mul,  [v1, v2]   => some (.inr (.Litv (.Float64 (fp64_mul roundTiesToEven v1 v2))))
    | .Div,  [v1, v2]   => some (.inr (.Litv (.Float64 (fp64_div roundTiesToEven v1 v2))))
    | .FMA,  [v1, v2, v3] => some (.inr (.Litv (.Float64 (fp64_mul_add roundTiesToEven v2 v3 v1))))
    | _, _ => none
  | a, .IntT, vals =>
    match a, vals.map the_Litv_IntLit with
    | .Add, [v1, v2] => some (.inr (.Litv (.IntLit (v1 + v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.IntLit (v1 - v2))))
    | .Mul, [v1, v2] => some (.inr (.Litv (.IntLit (v1 * v2))))
    | .Div, [v1, v2] => some (if v2 == 0 then .inl div_exn_v
                               else .inr (.Litv (.IntLit (v1 / v2))))
    | .Mod, [v1, v2] => some (if v2 == 0 then .inl div_exn_v
                               else .inr (.Litv (.IntLit (v1 % v2))))
    | _, _ => none
  | a, .WordT .W8, vals =>
    match a, vals.map the_Litv_Word8 with
    | .Add, [v1, v2] => some (.inr (.Litv (.Word8 (word_add_8 v1 v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.Word8 (word_sub_8 v1 v2))))
    | .And, [v1, v2] => some (.inr (.Litv (.Word8 (word_and_8 v1 v2))))
    | .Or,  [v1, v2] => some (.inr (.Litv (.Word8 (word_or_8 v1 v2))))
    | .Xor, [v1, v2] => some (.inr (.Litv (.Word8 (word_xor_8 v1 v2))))
    | _, _ => none
  | a, .WordT .W64, vals =>
    match a, vals.map the_Litv_Word64 with
    | .Add, [v1, v2] => some (.inr (.Litv (.Word64 (word_add_64 v1 v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.Word64 (word_sub_64 v1 v2))))
    | .And, [v1, v2] => some (.inr (.Litv (.Word64 (word_and_64 v1 v2))))
    | .Or,  [v1, v2] => some (.inr (.Litv (.Word64 (word_or_64 v1 v2))))
    | .Xor, [v1, v2] => some (.inr (.Litv (.Word64 (word_xor_64 v1 v2))))
    | _, _ => none
  | a, .BoolT, vals =>
    match a, vals with
    | .Not, [v1] => some (.inr (Boolv (!(the_Boolv v1))))
    | _, _ => none
  | _, _, _ => none

/- HOL4:
Definition do_conversion_def:
  (do_conversion v (WordT W8) IntT = SOME (INR $ Litv $ IntLit $ & (w2n (the_Litv_Word8 v)))) ∧
  (do_conversion v (WordT W64) IntT = SOME (INR $ Litv $ IntLit $ & (w2n (the_Litv_Word64 v)))) ∧
  (do_conversion v IntT (WordT W8) = SOME (INR $ Litv $ Word8 $ i2w (the_Litv_IntLit v))) ∧
  (do_conversion v IntT (WordT W64) = SOME (INR $ Litv $ Word64 $ i2w (the_Litv_IntLit v))) ∧
  (do_conversion v CharT IntT = SOME (INR $ Litv $ IntLit $ & (ORD (the_Litv_Char v)))) ∧
  (do_conversion v IntT CharT = ...) ∧
  (do_conversion v CharT (WordT W8) = SOME (INR $ Litv $ Word8 $ char_to_word8 (the_Litv_Char v))) ∧
  (do_conversion v (WordT W8) CharT = SOME (INR $ Litv $ Char $ word8_to_char (the_Litv_Word8 v))) ∧
  (do_conversion v Float64T (WordT W64) = SOME (INR $ Litv $ Word64 $ the_Litv_Float64 v)) ∧
  (do_conversion v (WordT W64) Float64T = SOME (INR $ Litv $ Float64 $ the_Litv_Word64 v)) ∧
  (do_conversion _ _ _ = NONE)
End
-/
def do_conversion : v → prim_type → prim_type → Option (v ⊕ v)
  | val_, .WordT .W8, .IntT => some (.inr (.Litv (.IntLit (Int.ofNat (w2n_8 (the_Litv_Word8 val_))))))
  | val_, .WordT .W64, .IntT => some (.inr (.Litv (.IntLit (Int.ofNat (w2n_64 (the_Litv_Word64 val_))))))
  | val_, .IntT, .WordT .W8 => some (.inr (.Litv (.Word8 (i2w_8 (the_Litv_IntLit val_)))))
  | val_, .IntT, .WordT .W64 => some (.inr (.Litv (.Word64 (i2w_64 (the_Litv_IntLit val_)))))
  | val_, .CharT, .IntT => some (.inr (.Litv (.IntLit (Int.ofNat (ORD (the_Litv_Char val_))))))
  | val_, .IntT, .CharT =>
    let i := the_Litv_IntLit val_
    if i < 0 || i > 255 then some (.inl chr_exn_v)
    else some (.inr (.Litv (.Char (CHR (Int.toNat (Int.natAbs i))))))
  | val_, .CharT, .WordT .W8 => some (.inr (.Litv (.Word8 (char_to_word8 (the_Litv_Char val_)))))
  | val_, .WordT .W8, .CharT => some (.inr (.Litv (.Char (word8_to_char (the_Litv_Word8 val_)))))
  | val_, .Float64T, .WordT .W64 => some (.inr (.Litv (.Word64 (the_Litv_Float64 val_))))
  | val_, .WordT .W64, .Float64T => some (.inr (.Litv (.Float64 (the_Litv_Word64 val_))))
  | _, _, _ => none

/- HOL4:
Definition do_app_def:
  do_app (s, t) op vs = ...   (* ~200-line case analysis *)
End
-/
def do_app {ffi : Type} (st : store v × ffi_state ffi) (o_ : op) (vs : List v) :
    Option ((store v × ffi_state ffi) × result v v) :=
  let s := st.1
  let t := st.2
  match o_, vs with
  | .ListAppend, [x1, x2] =>
    match v_to_list x1, v_to_list x2 with
    | some xs, some ys => some ((s, t), .Rval (list_to_v (xs ++ ys)))
    | _, _ => none
  | .Shift .W8 sh n, [.Litv (.Word8 w)] =>
    some ((s, t), .Rval (.Litv (.Word8 (shift8_lookup sh w n))))
  | .Shift .W64 sh n, [.Litv (.Word64 w)] =>
    some ((s, t), .Rval (.Litv (.Word64 (shift64_lookup sh w n))))
  | .Equality, [v1, v2] =>
    match do_eq v1 v2 with
    | .Eq_type_error => none
    | .Eq_val b => some ((s, t), .Rval (Boolv b))
  | .Opassign, [.Loc _ lnum, val_] =>
    match store_assign lnum (.Refv val_) s with
    | some s' => some ((s', t), .Rval (.Conv none []))
    | none => none
  | .Opref, [val_] =>
    let (s', n) := store_alloc (.Refv val_) s
    some ((s', t), .Rval (.Loc true n))
  | .Opderef, [.Loc _ n] =>
    match store_lookup n s with
    | some (.Refv val_) => some ((s, t), .Rval val_)
    | _ => none
  | .Aw8alloc, [.Litv (.IntLit n), .Litv (.Word8 w)] =>
    if n < 0 then
      some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let (s', lnum) := store_alloc (.W8array (REPLICATE n.natAbs w)) s
      some ((s', t), .Rval (.Loc true lnum))
  | .Aw8sub, [.Loc _ lnum, .Litv (.IntLit i)] =>
    match store_lookup lnum s with
    | some (.W8array ws) =>
      if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else
        let n := i.natAbs
        if n ≥ ws.length then some ((s, t), .Rerr (.Rraise sub_exn_v))
        else some ((s, t), .Rval (.Litv (.Word8 (EL n ws))))
    | _ => none
  | .Aw8sub_unsafe, [.Loc _ lnum, .Litv (.IntLit i)] =>
    match store_lookup lnum s with
    | some (.W8array ws) =>
      if i < 0 then none
      else
        let n := i.natAbs
        if n ≥ ws.length then none
        else some ((s, t), .Rval (.Litv (.Word8 (EL n ws))))
    | _ => none
  | .Aw8length, [.Loc _ n] =>
    match store_lookup n s with
    | some (.W8array ws) =>
      some ((s, t), .Rval (.Litv (.IntLit (Int.ofNat ws.length))))
    | _ => none
  | .Aw8update, [.Loc _ lnum, .Litv (.IntLit i), .Litv (.Word8 w)] =>
    match store_lookup lnum s with
    | some (.W8array ws) =>
      if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else
        let n := i.natAbs
        if n ≥ ws.length then some ((s, t), .Rerr (.Rraise sub_exn_v))
        else
          match store_assign lnum (.W8array (LUPDATE w n ws)) s with
          | none => none
          | some s' => some ((s', t), .Rval (.Conv none []))
    | _ => none
  | .Aw8update_unsafe, [.Loc _ lnum, .Litv (.IntLit i), .Litv (.Word8 w)] =>
    match store_lookup lnum s with
    | some (.W8array ws) =>
      if i < 0 then none
      else
        let n := i.natAbs
        if n ≥ ws.length then none
        else
          match store_assign lnum (.W8array (LUPDATE w n ws)) s with
          | none => none
          | some s' => some ((s', t), .Rval (.Conv none []))
    | _ => none
  | .CopyStrStr, [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] =>
    some ((s, t),
      match copy_array (explode strng, off) len none with
      | none => .Rerr (.Rraise sub_exn_v)
      | some cs => .Rval (.Litv (.StrLit (implode (String.mk cs)))))
  | .CopyStrAw8,
      [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
       .Loc _ dst, .Litv (.IntLit dstoff)] =>
    match store_lookup dst s with
    | some (.W8array ws) =>
      match copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) with
      | none => some ((s, t), .Rerr (.Rraise sub_exn_v))
      | some cs =>
        match store_assign dst (.W8array (chars_to_ws cs)) s with
        | some s' => some ((s', t), .Rval (.Conv none []))
        | _ => none
    | _ => none
  | .CopyAw8Str, [.Loc _ src, .Litv (.IntLit off), .Litv (.IntLit len)] =>
    match store_lookup src s with
    | some (.W8array ws) =>
      some ((s, t),
        match copy_array (ws, off) len none with
        | none => .Rerr (.Rraise sub_exn_v)
        | some ws' => .Rval (.Litv (.StrLit (implode (String.mk (ws_to_chars ws'))))))
    | _ => none
  | .CopyAw8Aw8,
      [.Loc _ src, .Litv (.IntLit off), .Litv (.IntLit len),
       .Loc _ dst, .Litv (.IntLit dstoff)] =>
    match store_lookup src s, store_lookup dst s with
    | some (.W8array ws), some (.W8array ds) =>
      match copy_array (ws, off) len (some (ds, dstoff)) with
      | none => some ((s, t), .Rerr (.Rraise sub_exn_v))
      | some ws' =>
        match store_assign dst (.W8array ws') s with
        | some s' => some ((s', t), .Rval (.Conv none []))
        | _ => none
    | _, _ => none
  | .XorAw8Str_unsafe, [.Loc _ dst, .Litv (.StrLit str_arg)] =>
    match store_lookup dst s with
    | some (.W8array bs) =>
      match xor_bytes ((explode str_arg).map (fun c => n2w_8 (ORD c))) bs with
      | none => none
      | some new_bs =>
        match store_assign dst (.W8array new_bs) s with
        | none => none
        | some s' => some ((s', t), .Rval (.Conv none []))
    | _ => none
  | .Implode, [val_] =>
    match v_to_char_list val_ with
    | some ls => some ((s, t), .Rval (.Litv (.StrLit (implode (String.mk ls)))))
    | none => none
  | .Explode, [.Litv (.StrLit strng)] =>
    some ((s, t), .Rval (list_to_v ((explode strng).map (fun c => .Litv (.Char c)))))
  | .Strsub, [.Litv (.StrLit strng), .Litv (.IntLit i)] =>
    if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let n := i.natAbs
      if n ≥ strlen strng then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else some ((s, t), .Rval (.Litv (.Char (EL n (explode strng)))))
  | .Strlen, [.Litv (.StrLit strng)] =>
    some ((s, t), .Rval (.Litv (.IntLit (Int.ofNat (strlen strng)))))
  | .Strcat, [val_] =>
    match v_to_list val_ with
    | some vs =>
      match vs_to_string vs with
      | some strng => some ((s, t), .Rval (.Litv (.StrLit strng)))
      | _ => none
    | _ => none
  | .VfromList, [val_] =>
    match v_to_list val_ with
    | some vs => some ((s, t), .Rval (.Vectorv vs))
    | none => none
  | .Vsub_unsafe, [.Vectorv vs, .Litv (.IntLit i)] =>
    if 0 ≤ i ∧ i.natAbs < vs.length then
      some ((s, t), .Rval (EL i.natAbs vs))
    else none
  | .Vsub, [.Vectorv vs, .Litv (.IntLit i)] =>
    if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let n := i.natAbs
      if n ≥ vs.length then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else some ((s, t), .Rval (EL n vs))
  | .Vlength, [.Vectorv vs] =>
    some ((s, t), .Rval (.Litv (.IntLit (Int.ofNat vs.length))))
  | .Aalloc, [.Litv (.IntLit n), val_] =>
    if n < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let (s', lnum) := store_alloc (.Varray (REPLICATE n.natAbs val_)) s
      some ((s', t), .Rval (.Loc true lnum))
  | .AallocEmpty, [.Conv none []] =>
    let (s', lnum) := store_alloc (.Varray []) s
    some ((s', t), .Rval (.Loc true lnum))
  | .AallocFixed, vs =>
    let (s', lnum) := store_alloc (.Varray vs) s
    some ((s', t), .Rval (.Loc true lnum))
  | .Asub, [.Loc _ lnum, .Litv (.IntLit i)] =>
    match store_lookup lnum s with
    | some (.Varray vs) =>
      if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else
        let n := i.natAbs
        if n ≥ vs.length then some ((s, t), .Rerr (.Rraise sub_exn_v))
        else some ((s, t), .Rval (EL n vs))
    | _ => none
  | .Asub_unsafe, [.Loc _ lnum, .Litv (.IntLit i)] =>
    match store_lookup lnum s with
    | some (.Varray vs) =>
      if i < 0 then none
      else
        let n := i.natAbs
        if n ≥ vs.length then none
        else some ((s, t), .Rval (EL n vs))
    | _ => none
  | .Alength, [.Loc _ n] =>
    match store_lookup n s with
    | some (.Varray ws) =>
      some ((s, t), .Rval (.Litv (.IntLit (Int.ofNat ws.length))))
    | _ => none
  | .Aupdate, [.Loc _ lnum, .Litv (.IntLit i), val_] =>
    match store_lookup lnum s with
    | some (.Varray vs) =>
      if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else
        let n := i.natAbs
        if n ≥ vs.length then some ((s, t), .Rerr (.Rraise sub_exn_v))
        else
          match store_assign lnum (.Varray (LUPDATE val_ n vs)) s with
          | none => none
          | some s' => some ((s', t), .Rval (.Conv none []))
    | _ => none
  | .Aupdate_unsafe, [.Loc _ lnum, .Litv (.IntLit i), val_] =>
    match store_lookup lnum s with
    | some (.Varray vs) =>
      if i < 0 then none
      else
        let n := i.natAbs
        if n ≥ vs.length then none
        else
          match store_assign lnum (.Varray (LUPDATE val_ n vs)) s with
          | none => none
          | some s' => some ((s', t), .Rval (.Conv none []))
    | _ => none
  | .ConfigGC, [.Litv (.IntLit _), .Litv (.IntLit _)] =>
    some ((s, t), .Rval (.Conv none []))
  | .FFI n, [.Litv (.StrLit conf), .Loc _ lnum] =>
    match store_lookup lnum s with
    | some (.W8array ws) =>
      match call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws with
      | .FFI_return t' ws' =>
        match store_assign lnum (.W8array ws') s with
        | some s' => some ((s', t'), .Rval (.Conv none []))
        | none => none
      | .FFI_final outcome =>
        some ((s, t), .Rerr (.Rabort (.Rffi_error outcome)))
    | _ => none
  | .Env_id, [.Env _ (gen, id_)] =>
    some ((s, t), .Rval (.Conv none [nat_to_v gen, nat_to_v id_]))
  | .Env_id, [.Conv none [gen, id_]] =>
    some ((s, t), .Rval (.Conv none [gen, id_]))
  | .ThunkOp th_op, vs => thunk_op_fun (s, t) th_op vs
  | .Arith a ty, vs =>
    if EVERY (check_type ty) vs then
      match do_arith a ty vs with
      | some (.inr res) => some ((s, t), .Rval res)
      | some (.inl exn) => some ((s, t), .Rerr (.Rraise exn))
      | none => none
    else none
  | .FromTo ty1 ty2, [val_] =>
    if check_type ty1 val_ then
      match do_conversion val_ ty1 ty2 with
      | some (.inr res) => some ((s, t), .Rval res)
      | some (.inl exn) => some ((s, t), .Rerr (.Rraise exn))
      | none => none
    else none
  | .Test test_ test_ty, [v1, v2] =>
    match do_test test_ test_ty v1 v2 with
    | .Eq_type_error => none
    | .Eq_val b => some ((s, t), .Rval (Boolv b))
  | _, _ => none

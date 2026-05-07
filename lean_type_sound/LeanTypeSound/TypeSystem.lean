/-
  Translation of typeSystemScript.sml
  Specification of CakeML's type system.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.SemanticPrimitives

open HOL4

-- ============================================================
-- Types
-- ============================================================

/- HOL4: Type type_ident = ":num" -/
abbrev type_ident := Nat

/- HOL4:
Datatype:
  t = Tvar tvarN | Tvar_db num | Tapp (t list) type_ident
End
-/
inductive sem_t where
  | Tvar : tvarN → sem_t
  | Tvar_db : Nat → sem_t
  | Tapp : List sem_t → type_ident → sem_t
deriving Repr, BEq, Inhabited

-- ============================================================
-- Type number constants
-- ============================================================

/- HOL4: Definition Tarray_num_def: Tarray_num = 0 End -/
def Tarray_num : type_ident := 0
def Tbool_num : type_ident := 1
def Tchar_num : type_ident := 2
def Texn_num : type_ident := 3
def Tfn_num : type_ident := 4
def Tint_num : type_ident := 5
def Tlist_num : type_ident := 6
def Tref_num : type_ident := 7
def Tstring_num : type_ident := 8
def Ttup_num : type_ident := 9
def Tvector_num : type_ident := 10
def Tword64_num : type_ident := 11
def Tword8_num : type_ident := 12
def Tword8array_num : type_ident := 13
def Tdouble_num : type_ident := 14

/- HOL4:
Definition prim_type_nums_def:
  prim_type_nums = [Tarray_num; Tchar_num; ...]
End
-/
def prim_type_nums : List type_ident :=
  [Tarray_num, Tchar_num, Texn_num, Tfn_num, Tint_num, Tref_num, Tstring_num,
   Ttup_num, Tvector_num, Tword64_num, Tword8_num, Tword8array_num, Tdouble_num]

-- ============================================================
-- Type abbreviations
-- ============================================================

def Tarray (t : sem_t) : sem_t := .Tapp [t] Tarray_num
def Tbool : sem_t := .Tapp [] Tbool_num
def Tchar : sem_t := .Tapp [] Tchar_num
def Texn : sem_t := .Tapp [] Texn_num
def Tfn (t1 t2 : sem_t) : sem_t := .Tapp [t1, t2] Tfn_num
def Tint : sem_t := .Tapp [] Tint_num
def Tlist (t : sem_t) : sem_t := .Tapp [t] Tlist_num
def Tref (t : sem_t) : sem_t := .Tapp [t] Tref_num
def Tstring : sem_t := .Tapp [] Tstring_num
def Ttup (ts : List sem_t) : sem_t := .Tapp ts Ttup_num
def Tvector (t : sem_t) : sem_t := .Tapp [t] Tvector_num
def Tword64 : sem_t := .Tapp [] Tword64_num
def Tword8 : sem_t := .Tapp [] Tword8_num
def Tword8array : sem_t := .Tapp [] Tword8array_num
def Tdouble : sem_t := .Tapp [] Tdouble_num

-- ============================================================
-- Free variable checking
-- ============================================================

/- HOL4:
Definition check_freevars_def: ...
End
-/
def check_freevars : Nat → List mlstring → sem_t → Bool
  | _, tvs, .Tvar tv => tvs.any (· == tv)
  | dbmax, tvs, .Tapp ts _ =>
    ts.attach.all fun ⟨t, _⟩ => check_freevars dbmax tvs t
  | dbmax, _, .Tvar_db n => n < dbmax
termination_by _ _ t => sizeOf t
decreasing_by
  simp_wf
  rename_i h
  have := List.sizeOf_lt_of_mem h
  simp at this
  omega

/- HOL4:
Definition check_freevars_ast_def: ...
End
-/
def check_freevars_ast : List mlstring → ast_t → Bool
  | tvs, .Atvar tv => tvs.any (· == tv)
  | tvs, .Attup ts => ts.attach.all fun ⟨t, _⟩ => check_freevars_ast tvs t
  | tvs, .Atfun t1 t2 => check_freevars_ast tvs t1 && check_freevars_ast tvs t2
  | tvs, .Atapp ts _ => ts.attach.all fun ⟨t, _⟩ => check_freevars_ast tvs t
termination_by _ t => sizeOf t
decreasing_by
  all_goals (
    simp_wf
    first
      | decreasing_trivial
      | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega))

-- ============================================================
-- Type substitution and de Bruijn operations
-- ============================================================

/- HOL4:
Definition type_subst_def: ...
End
-/
def type_subst (s : Finmap mlstring sem_t) : sem_t → sem_t
  | .Tvar tv =>
    match Finmap.FLOOKUP s tv with
    | none => .Tvar tv
    | some t => t
  | .Tapp ts tn => .Tapp (ts.map (type_subst s)) tn
  | .Tvar_db n => .Tvar_db n

/- HOL4:
Definition deBruijn_inc_def: ...
End
-/
def deBruijn_inc (skip n : Nat) : sem_t → sem_t
  | .Tvar tv => .Tvar tv
  | .Tvar_db m => if m < skip then .Tvar_db m else .Tvar_db (m + n)
  | .Tapp ts tn => .Tapp (ts.map (deBruijn_inc skip n)) tn

/- HOL4:
Definition deBruijn_subst_def: ...
End
-/
def deBruijn_subst (skip : Nat) (ts : List sem_t) : sem_t → sem_t
  | .Tvar tv => .Tvar tv
  | .Tvar_db n =>
    if ¬(n < skip) && n < ts.length + skip then
      EL (n - skip) ts
    else if ¬(n < skip) then
      .Tvar_db (n - ts.length)
    else
      .Tvar_db n
  | .Tapp ts' tn => .Tapp (ts'.map (deBruijn_subst skip ts)) tn

-- ============================================================
-- Type environments
-- ============================================================

/- HOL4:
Datatype:
  tenv_val_exp = Empty | Bind_tvar num tenv_val_exp | Bind_name varN num t tenv_val_exp
End
-/
inductive tenv_val_exp where
  | Empty : tenv_val_exp
  | Bind_tvar : Nat → tenv_val_exp → tenv_val_exp
  | Bind_name : varN → Nat → sem_t → tenv_val_exp → tenv_val_exp

/- HOL4:
Definition bind_tvar_def: ...
End
-/
def bind_tvar (tvs : Nat) (tenvE : tenv_val_exp) : tenv_val_exp :=
  if tvs == 0 then tenvE else .Bind_tvar tvs tenvE

/- HOL4:
Definition opt_bind_name_def: ...
End
-/
def opt_bind_name (n : Option mlstring) (tvs : Nat) (t : sem_t) (tenvE : tenv_val_exp) :
    tenv_val_exp :=
  match n with
  | none => tenvE
  | some n' => .Bind_name n' tvs t tenvE

/- HOL4:
Definition tveLookup_def: ...
End
-/
def tveLookup (n : mlstring) (inc : Nat) : tenv_val_exp → Option (Nat × sem_t)
  | .Empty => none
  | .Bind_tvar tvs tenvE => tveLookup n (inc + tvs) tenvE
  | .Bind_name n' tvs t tenvE =>
    if n' == n then some (tvs, deBruijn_inc tvs inc t)
    else tveLookup n inc tenvE

/- HOL4: Type abbreviations for type environments -/
abbrev tenv_abbrev := «namespace» modN typeN (List tvarN × sem_t)
abbrev tenv_ctor := «namespace» modN conN (List tvarN × List sem_t × type_ident)
abbrev tenv_val := «namespace» modN varN (Nat × sem_t)

/- HOL4:
Datatype:
  type_env = <| v : tenv_val ; c : tenv_ctor ; t : tenv_abbrev |>
End
-/
structure type_env where
  v : tenv_val
  c : tenv_ctor
  t : tenv_abbrev

/- HOL4:
Definition extend_dec_tenv_def: ...
End
-/
def extend_dec_tenv (tenv' tenv : type_env) : type_env :=
  { v := nsAppend tenv'.v tenv.v
  , c := nsAppend tenv'.c tenv.c
  , t := nsAppend tenv'.t tenv.t }

/- HOL4:
Definition lookup_varE_def: ...
End
-/
def lookup_varE (id : cml_id modN varN) (tenvE : tenv_val_exp) : Option (Nat × sem_t) :=
  match id with
  | .Short x => tveLookup x 0 tenvE
  | _ => none

/- HOL4:
Definition lookup_var_def: ...
End
-/
def lookup_var (id : cml_id modN varN) (tenvE : tenv_val_exp) (tenv : type_env) :
    Option (Nat × sem_t) :=
  match lookup_varE id tenvE with
  | some x => some x
  | none => nsLookup tenv.v id

/- HOL4:
Definition num_tvs_def: ...
End
-/
def num_tvs : tenv_val_exp → Nat
  | .Empty => 0
  | .Bind_tvar tvs tenvE => tvs + num_tvs tenvE
  | .Bind_name _ _ _ tenvE => num_tvs tenvE

/- HOL4:
Definition bind_var_list_def: ...
End
-/
def bind_var_list (tvs : Nat) : List (mlstring × sem_t) → tenv_val_exp → tenv_val_exp
  | [], tenvE => tenvE
  | (n, t) :: binds, tenvE => .Bind_name n tvs t (bind_var_list tvs binds tenvE)

-- ============================================================
-- Type operator checking
-- ============================================================

/- HOL4:
Definition t_of_def[simp]: ...
End
-/
def t_of : prim_type → sem_t
  | .BoolT => Tbool
  | .IntT => Tint
  | .CharT => Tchar
  | .StrT => Tstring
  | .WordT .W8 => Tword8
  | .WordT .W64 => Tword64
  | .Float64T => Tdouble

/- HOL4:
Definition supported_test_def[simp]: ...
End
-/
def supported_test : test → prim_type → Bool
  | .Equal, _ => true
  | .Compare _, ty => [prim_type.IntT, .CharT, .WordT .W8, .Float64T].any (· == ty)
  | _, _ => false

/- HOL4:
Definition supported_arith_def[simp]: ...
End
-/
def supported_arith (a : arith) (ty : prim_type) : Option Nat :=
  match ty with
  | .IntT =>
    if [arith.Add, .Sub, .Mul, .Div, .Mod].any (· == a) then some 2 else none
  | .Float64T =>
    if [arith.Abs, .Neg, .Sqrt].any (· == a) then some 1
    else if [arith.Add, .Sub, .Mul, .Div].any (· == a) then some 2
    else if a == .FMA then some 3 else none
  | .WordT _ =>
    if [arith.Add, .Sub, .And, .Or, .Xor].any (· == a) then some 2 else none
  | .BoolT =>
    if a == .Not then some 1 else none
  | _ => none

/- HOL4:
Definition supported_conversion_def[simp]: ...
End
-/
def supported_conversion : prim_type → prim_type → Bool
  | .WordT .W8, .IntT => true
  | .WordT .W64, .IntT => true
  | .IntT, .WordT .W8 => true
  | .IntT, .WordT .W64 => true
  | .CharT, .IntT => true
  | .IntT, .CharT => true
  | .CharT, .WordT .W8 => true
  | .WordT .W8, .CharT => true
  | .Float64T, .WordT .W64 => true
  | .WordT .W64, .Float64T => true
  | _, _ => false

/- HOL4:
Definition type_op_def: ...
End
-/
def type_op (o_ : op) (ts : List sem_t) (t : sem_t) : Prop :=
  match o_, ts with
  | .Opapp, [t1, t2] => t1 = Tfn t2 t
  | .Shift .W8 _ _, [t1] => t1 = Tword8 ∧ t = Tword8
  | .Shift .W64 _ _, [t1] => t1 = Tword64 ∧ t = Tword64
  | .Equality, [t1, t2] => t1 = t2 ∧ t = Tbool
  | .Arith a ty, _ =>
    (∀ arg, arg ∈ ts → arg = t_of ty) ∧ t = t_of ty ∧
    supported_arith a ty = some ts.length
  | .FromTo ty1 ty2, [t1] =>
    t1 = t_of ty1 ∧ t = t_of ty2 ∧ supported_conversion ty1 ty2 = true
  | .Test test ty, [t1, t2] =>
    t1 = t2 ∧ t = Tbool ∧ t1 = t_of ty ∧ supported_test test ty = true
  | .Opassign, [t1, t2] => t1 = Tref t2 ∧ t = Ttup []
  | .Opref, [t1] => t = Tref t1
  | .Opderef, [t1] => t1 = Tref t
  | .Aw8alloc, [t1, t2] => t1 = Tint ∧ t2 = Tword8 ∧ t = Tword8array
  | .Aw8sub, [t1, t2] => t1 = Tword8array ∧ t2 = Tint ∧ t = Tword8
  | .Aw8length, [t1] => t1 = Tword8array ∧ t = Tint
  | .Aw8update, [t1, t2, t3] =>
    t1 = Tword8array ∧ t2 = Tint ∧ t3 = Tword8 ∧ t = Ttup []
  | .CopyStrStr, [t1, t2, t3] =>
    t1 = Tstring ∧ t2 = Tint ∧ t3 = Tint ∧ t = Tstring
  | .CopyStrAw8, [t1, t2, t3, t4, t5] =>
    t1 = Tstring ∧ t2 = Tint ∧ t3 = Tint ∧ t4 = Tword8array ∧ t5 = Tint ∧ t = Ttup []
  | .CopyAw8Str, [t1, t2, t3] =>
    t1 = Tword8array ∧ t2 = Tint ∧ t3 = Tint ∧ t = Tstring
  | .CopyAw8Aw8, [t1, t2, t3, t4, t5] =>
    t1 = Tword8array ∧ t2 = Tint ∧ t3 = Tint ∧ t4 = Tword8array ∧ t5 = Tint ∧ t = Ttup []
  | .Implode, [t1] => t1 = Tlist Tchar ∧ t = Tstring
  | .Explode, [t1] => t1 = Tstring ∧ t = Tlist Tchar
  | .Strsub, [t1, t2] => t1 = Tstring ∧ t2 = Tint ∧ t = Tchar
  | .Strlen, [t1] => t1 = Tstring ∧ t = Tint
  | .Strcat, [t1] => t1 = Tlist Tstring ∧ t = Tstring
  | .VfromList, [.Tapp [t1] ctor] => ctor = Tlist_num ∧ t = Tvector t1
  | .Vsub, [t1, t2] => t2 = Tint ∧ Tvector t = t1
  | .Vlength, [.Tapp [_] ctor] => ctor = Tvector_num ∧ t = Tint
  | .Aalloc, [t1, t2] => t1 = Tint ∧ t = Tarray t2
  | .AallocEmpty, [t1] => t1 = Ttup [] ∧ ∃ t2, t = Tarray t2
  | .Asub, [t1, t2] => t2 = Tint ∧ Tarray t = t1
  | .Alength, [.Tapp [_] ctor] => ctor = Tarray_num ∧ t = Tint
  | .Aupdate, [t1, t2, t3] => t1 = Tarray t3 ∧ t2 = Tint ∧ t = Ttup []
  | .ConfigGC, [t1, t2] => t1 = Tint ∧ t2 = Tint ∧ t = Ttup []
  | .FFI _, [t1, t2] => t1 = Tstring ∧ t2 = Tword8array ∧ t = Ttup []
  | .ListAppend, [.Tapp [t1] ctor, t2] =>
    ctor = Tlist_num ∧ t2 = sem_t.Tapp [t1] ctor ∧ t = t2
  | _, _ => False

-- ============================================================
-- Type name operations
-- ============================================================

/- HOL4:
Definition check_type_names_def: ...
End
-/
def check_type_names (tenvT : tenv_abbrev) : ast_t → Bool
  | .Atvar _ => true
  | .Attup ts => ts.attach.all fun ⟨t, _⟩ => check_type_names tenvT t
  | .Atfun t1 t2 => check_type_names tenvT t1 && check_type_names tenvT t2
  | .Atapp ts tn =>
    (match nsLookup tenvT tn with
     | some (tvs, _) => tvs.length == ts.length
     | none => false) &&
    ts.attach.all fun ⟨t, _⟩ => check_type_names tenvT t
termination_by t => sizeOf t
decreasing_by
  all_goals (
    simp_wf
    first
      | decreasing_trivial
      | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega))

/- HOL4:
Definition type_name_subst_def: ...
End
-/
def type_name_subst (tenvT : tenv_abbrev) : ast_t → sem_t
  | .Atvar tv => .Tvar tv
  | .Attup ts => Ttup (ts.map (type_name_subst tenvT))
  | .Atfun t1 t2 => Tfn (type_name_subst tenvT t1) (type_name_subst tenvT t2)
  | .Atapp ts tc =>
    let args := ts.map (type_name_subst tenvT)
    match nsLookup tenvT tc with
    | some (tvs, t) => type_subst (Finmap.alist_to_fmap (tvs.zip args)) t
    | none => Ttup args

-- ============================================================
-- Constructor type checking
-- ============================================================

/- HOL4:
Definition check_ctor_tenv_def: ...
End
-/
def check_ctor_tenv (tenvT : tenv_abbrev) :
    List (List tvarN × mlstring × List (conN × List ast_t)) → Bool
  | [] => true
  | (tvs, tn, ctors) :: tds =>
    check_dup_ctors (tvs, tn, ctors) &&
    ALL_DISTINCT tvs &&
    ctors.all (fun (_, ts) =>
      ts.all (check_freevars_ast tvs) && ts.all (check_type_names tenvT)) &&
    !(tds.map fun (_, tn', _) => tn').any (· == tn) &&
    check_ctor_tenv tenvT tds

/- HOL4:
Definition build_ctor_tenv_def: ...
End
-/
def build_ctor_tenv (tenvT : tenv_abbrev) :
    List (List tvarN × mlstring × List (conN × List ast_t)) → List type_ident →
    «namespace» modN conN (List tvarN × List sem_t × type_ident)
  | [], [] => alist_to_ns []
  | (tvs, _, ctors) :: tds, id_ :: ids =>
    nsAppend (build_ctor_tenv tenvT tds ids)
      (alist_to_ns ((ctors.map fun (cn, ts) =>
        (cn, (tvs, ts.map (type_name_subst tenvT), id_))).reverse))
  | _, _ => alist_to_ns []

/- HOL4:
Definition is_value_def: ...
End
-/
def is_value : exp → Bool
  | .Lit _ => true
  | .Con _ es => es.attach.all fun ⟨e, _⟩ => is_value e
  | .Var _ => true
  | .Fun _ _ => true
  | .Tannot e _ => is_value e
  | .Lannot e _ => is_value e
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals (
    simp_wf
    first
      | decreasing_trivial
      | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega))

-- ============================================================
-- Inductive relation: type_p / type_ps
-- ============================================================

/- HOL4:
Inductive type_p:
  ... (12 rules for type_p) ...
  ... (2 rules for type_ps) ...
End
-/
mutual
inductive type_p : Nat → type_env → pat → sem_t → List (varN × sem_t) → Prop where
  | pany : ∀ tvs tenv t,
    check_freevars tvs [] t →
    type_p tvs tenv .Pany t []
  | pvar : ∀ tvs tenv n t,
    check_freevars tvs [] t →
    type_p tvs tenv (.Pvar n) t [(n, t)]
  | plit_int : ∀ tvs tenv n,
    type_p tvs tenv (.Plit (.IntLit n)) Tint []
  | plit_char : ∀ tvs tenv c,
    type_p tvs tenv (.Plit (.Char c)) Tchar []
  | plit_str : ∀ tvs tenv s,
    type_p tvs tenv (.Plit (.StrLit s)) Tstring []
  | plit_word8 : ∀ tvs tenv w,
    type_p tvs tenv (.Plit (.Word8 w)) Tword8 []
  | plit_word64 : ∀ tvs tenv w,
    type_p tvs tenv (.Plit (.Word64 w)) Tword64 []
  | pcon_some : ∀ tvs tenv cn ps ts' tvs' ts tn bindings,
    (∀ t', t' ∈ ts' → check_freevars tvs [] t') →
    ts'.length = tvs'.length →
    type_ps tvs tenv ps (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))) bindings →
    nsLookup tenv.c cn = some (tvs', ts, tn) →
    type_p tvs tenv (.Pcon (some cn) ps) (.Tapp ts' tn) bindings
  | pcon_none : ∀ tvs tenv ps ts bindings,
    type_ps tvs tenv ps ts bindings →
    type_p tvs tenv (.Pcon none ps) (Ttup ts) bindings
  | pref : ∀ tvs tenv p t bindings,
    type_p tvs tenv p t bindings →
    type_p tvs tenv (.Pref p) (Tref t) bindings
  | pas : ∀ tvs tenv pat t bindings v_,
    type_p tvs tenv pat t bindings →
    type_p tvs tenv (.Pas pat v_) t (bindings ++ [(v_, t)])
  | ptannot : ∀ tvs tenv p t bindings,
    check_freevars_ast [] t →
    check_type_names tenv.t t →
    type_p tvs tenv p (type_name_subst tenv.t t) bindings →
    type_p tvs tenv (.Ptannot p t) (type_name_subst tenv.t t) bindings

inductive type_ps : Nat → type_env → List pat → List sem_t → List (varN × sem_t) → Prop where
  | nil : ∀ tvs tenv,
    type_ps tvs tenv [] [] []
  | cons : ∀ tvs tenv p t bindings ps ts bindings',
    type_p tvs tenv p t bindings →
    type_ps tvs tenv ps ts bindings' →
    type_ps tvs tenv (p :: ps) (t :: ts) (bindings' ++ bindings)
end

-- ============================================================
-- Inductive relations: type_e / type_es / type_funs
-- ============================================================

/- HOL4:
Inductive type_e: ... (24 rules) ... End
-/
mutual
inductive type_e : type_env → tenv_val_exp → exp → sem_t → Prop where
  | lit_int : ∀ tenv tenvE n,
    type_e tenv tenvE (.Lit (.IntLit n)) Tint
  | lit_char : ∀ tenv tenvE c,
    type_e tenv tenvE (.Lit (.Char c)) Tchar
  | lit_str : ∀ tenv tenvE s,
    type_e tenv tenvE (.Lit (.StrLit s)) Tstring
  | lit_word8 : ∀ tenv tenvE w,
    type_e tenv tenvE (.Lit (.Word8 w)) Tword8
  | lit_word64 : ∀ tenv tenvE w,
    type_e tenv tenvE (.Lit (.Word64 w)) Tword64
  | lit_float64 : ∀ tenv tenvE w,
    type_e tenv tenvE (.Lit (.Float64 w)) Tdouble
  | raise : ∀ tenv tenvE e t,
    check_freevars (num_tvs tenvE) [] t →
    type_e tenv tenvE e Texn →
    type_e tenv tenvE (.Raise e) t
  | handle : ∀ tenv tenvE e t pes
    (bindings_of : (pat × exp) → List (varN × sem_t)),
    type_e tenv tenvE e t → pes ≠ [] →
    (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
    (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 Texn (bindings_of pe)) →
    (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t) →
    type_e tenv tenvE (.Handle e pes) t
  | con_some : ∀ tenv tenvE cn es ts' tvs ts tn,
    (∀ t', t' ∈ ts' → check_freevars (num_tvs tenvE) [] t') →
    tvs.length = ts'.length →
    type_es tenv tenvE es (ts.map (type_subst (Finmap.alist_to_fmap (tvs.zip ts')))) →
    nsLookup tenv.c cn = some (tvs, ts, tn) →
    type_e tenv tenvE (.Con (some cn) es) (.Tapp ts' tn)
  | con_none : ∀ tenv tenvE es ts,
    type_es tenv tenvE es ts →
    type_e tenv tenvE (.Con none es) (Ttup ts)
  | var : ∀ tenv tenvE n tvs t targs,
    tvs = targs.length →
    (∀ ta, ta ∈ targs → check_freevars (num_tvs tenvE) [] ta) →
    lookup_var n tenvE tenv = some (tvs, t) →
    type_e tenv tenvE (.Var n) (deBruijn_subst 0 targs t)
  | fun_ : ∀ tenv tenvE n e t1 t2,
    check_freevars (num_tvs tenvE) [] t1 →
    type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
    type_e tenv tenvE (.Fun n e) (Tfn t1 t2)
  | app : ∀ tenv tenvE o_ es ts t,
    type_es tenv tenvE es ts →
    type_op o_ ts t →
    check_freevars (num_tvs tenvE) [] t →
    type_e tenv tenvE (.App o_ es) t
  | log : ∀ tenv tenvE l e1 e2,
    type_e tenv tenvE e1 Tbool →
    type_e tenv tenvE e2 Tbool →
    type_e tenv tenvE (.Log l e1 e2) Tbool
  | if_ : ∀ tenv tenvE e1 e2 e3 t,
    type_e tenv tenvE e1 Tbool →
    type_e tenv tenvE e2 t →
    type_e tenv tenvE e3 t →
    type_e tenv tenvE (.If e1 e2 e3) t
  | mat : ∀ tenv tenvE e t1 t2 pes
    (bindings_of : (pat × exp) → List (varN × sem_t)),
    type_e tenv tenvE e t1 → pes ≠ [] →
    (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
    (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 t1 (bindings_of pe)) →
    (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t2) →
    type_e tenv tenvE (.Mat e pes) t2
  | let_ : ∀ tenv tenvE n e1 t1 e2 t2,
    type_e tenv tenvE e1 t1 →
    type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2 →
    type_e tenv tenvE (.Let n e1 e2) t2
  | letrec : ∀ tenv tenvE funs bindings e t,
    type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings →
    type_e tenv (bind_var_list 0 bindings tenvE) e t →
    type_e tenv tenvE (.Letrec funs e) t
  | tannot : ∀ tenv tenvE e t,
    check_freevars_ast [] t →
    check_type_names tenv.t t →
    type_e tenv tenvE e (type_name_subst tenv.t t) →
    type_e tenv tenvE (.Tannot e t) (type_name_subst tenv.t t)
  | lannot : ∀ tenv tenvE e t l,
    type_e tenv tenvE e t →
    type_e tenv tenvE (.Lannot e l) t

inductive type_es : type_env → tenv_val_exp → List exp → List sem_t → Prop where
  | nil : ∀ tenv tenvE,
    type_es tenv tenvE [] []
  | cons : ∀ tenv tenvE e t es ts,
    type_e tenv tenvE e t →
    type_es tenv tenvE es ts →
    type_es tenv tenvE (e :: es) (t :: ts)

inductive type_funs : type_env → tenv_val_exp → List (varN × varN × exp) →
    List (varN × sem_t) → Prop where
  | nil : ∀ tenv tenvE,
    type_funs tenv tenvE [] []
  | cons : ∀ tenv tenvE fn n e t1 t2 funs bindings,
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2) →
    type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
    type_funs tenv tenvE funs bindings →
    ALOOKUP bindings fn = none →
    type_funs tenv tenvE ((fn, n, e) :: funs) ((fn, Tfn t1 t2) :: bindings)
end

-- ============================================================
-- Declaration typing utilities
-- ============================================================

/- HOL4:
Definition tenv_add_tvs_def: ...
End
-/
def tenv_add_tvs (tvs : Nat) (bindings : List (mlstring × sem_t)) :
    List (mlstring × Nat × sem_t) :=
  bindings.map fun (n, t) => (n, (tvs, t))

/- HOL4:
Definition type_pe_determ_def: ...
End
-/
def type_pe_determ (tenv : type_env) (tenvE : tenv_val_exp) (p : pat) (e : exp) : Prop :=
  ∀ t1 tenv1 t2 tenv2,
    type_p 0 tenv p t1 tenv1 ∧ type_e tenv tenvE e t1 ∧
    type_p 0 tenv p t2 tenv2 ∧ type_e tenv tenvE e t2 →
    tenv1 = tenv2

/- HOL4:
Definition tscheme_inst_def: ...
End
-/
def tscheme_inst (ts1 ts2 : Nat × sem_t) : Prop :=
  let (tvs_spec, t_spec) := ts1
  let (tvs_impl, t_impl) := ts2
  ∃ subst : List sem_t,
    subst.length = tvs_impl ∧
    check_freevars tvs_impl [] t_impl ∧
    (∀ s, s ∈ subst → check_freevars tvs_spec [] s) ∧
    deBruijn_subst 0 subst t_impl = t_spec

/- HOL4:
Definition tenvLift_def: ...
End
-/
def tenvLift (mn : mlstring) (tenv : type_env) : type_env :=
  { v := nsLift mn tenv.v, c := nsLift mn tenv.c, t := nsLift mn tenv.t }

/- HOL4:
Definition tscheme_inst2_def: ...
End
-/
def tscheme_inst2 (_ : cml_id modN varN) (ts1 ts2 : Nat × sem_t) : Prop :=
  tscheme_inst ts1 ts2

/- HOL4:
Definition weak_tenv_def: ...
End
-/
def weak_tenv (tenv_impl tenv_spec : type_env) : Prop :=
  nsSub tscheme_inst2 tenv_spec.v tenv_impl.v ∧
  nsSub (fun _ x y => x = y) tenv_spec.c tenv_impl.c

-- ============================================================
-- Inductive relations: type_d / type_ds
-- ============================================================

/- HOL4:
Inductive type_d: ... (10 rules) ... End
-/
mutual
inductive type_d : Bool → type_env → dec → Set type_ident → type_env → Prop where
  | dlet_poly : ∀ (extra_checks : Bool) tenv locs p e tvs t bindings,
    is_value e →
    ALL_DISTINCT (pat_bindings p []) →
    type_p tvs tenv p t bindings →
    type_e tenv (bind_tvar tvs .Empty) e t →
    (extra_checks →
      ∀ tvs' bindings' t',
        type_p tvs' tenv p t' bindings' →
        type_e tenv (bind_tvar tvs' .Empty) e t' →
        LIST_REL (fun a b => tscheme_inst a b)
          ((tenv_add_tvs tvs' bindings').map Prod.snd)
          ((tenv_add_tvs tvs bindings).map Prod.snd)) →
    type_d extra_checks tenv (.Dlet locs p e) ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty }
  | dlet_mono : ∀ (extra_checks : Bool) tenv locs p e t bindings,
    (extra_checks → ¬is_value e ∧ type_pe_determ tenv .Empty p e) →
    ALL_DISTINCT (pat_bindings p []) →
    type_p 0 tenv p t bindings →
    type_e tenv .Empty e t →
    type_d extra_checks tenv (.Dlet locs p e) ∅
      { v := alist_to_ns (tenv_add_tvs 0 bindings), c := nsEmpty, t := nsEmpty }
  | dletrec : ∀ (extra_checks : Bool) tenv locs funs tvs bindings,
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs .Empty)) funs bindings →
    (extra_checks →
      ∀ tvs' bindings',
        type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' .Empty)) funs bindings' →
        LIST_REL (fun a b => tscheme_inst a b)
          ((tenv_add_tvs tvs' bindings').map Prod.snd)
          ((tenv_add_tvs tvs bindings).map Prod.snd)) →
    type_d extra_checks tenv (.Dletrec locs funs) ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty }
  | dtype : ∀ (extra_checks : Bool) tenv locs tdefs type_identities tenvT,
    ALL_DISTINCT type_identities →
    Set.Disjoint (fun x => x ∈ type_identities) (fun x => x ∈ (Tlist_num :: Tbool_num :: prim_type_nums)) →
    check_ctor_tenv (nsAppend tenvT tenv.t) tdefs →
    type_identities.length = tdefs.length →
    tenvT = alist_to_ns (List.zipWith
      (fun td i => match td with | (tvs, tn, _) => (tn, (tvs, sem_t.Tapp (tvs.map sem_t.Tvar) i)))
      tdefs type_identities) →
    type_d extra_checks tenv (.Dtype locs tdefs)
      (fun x => x ∈ type_identities)
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities, t := tenvT }
  | dtabbrev : ∀ (extra_checks : Bool) tenv locs tvs tn t,
    check_freevars_ast tvs t →
    check_type_names tenv.t t →
    ALL_DISTINCT tvs →
    type_d extra_checks tenv (.Dtabbrev locs tvs tn t) ∅
      { v := nsEmpty, c := nsEmpty, t := nsSing tn (tvs, type_name_subst tenv.t t) }
  | dexn : ∀ (extra_checks : Bool) tenv locs cn ts,
    (∀ t', t' ∈ ts → check_freevars_ast [] t') →
    (∀ t', t' ∈ ts → check_type_names tenv.t t') →
    type_d extra_checks tenv (.Dexn locs cn ts) ∅
      { v := nsEmpty,
        c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty }
  | dmod : ∀ (extra_checks : Bool) tenv mn ds decls tenv',
    type_ds extra_checks tenv ds decls tenv' →
    type_d extra_checks tenv (.Dmod mn ds) decls (tenvLift mn tenv')
  | dlocal : ∀ (extra_checks : Bool) tenv lds ds decls1 tenv1 decls2 tenv2,
    type_ds extra_checks tenv lds decls1 tenv1 →
    type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
    Set.Disjoint decls1 decls2 →
    type_d extra_checks tenv (.Dlocal lds ds) (decls1 ∪ decls2) tenv2

inductive type_ds : Bool → type_env → List dec → Set type_ident → type_env → Prop where
  | nil : ∀ (extra_checks : Bool) tenv,
    type_ds extra_checks tenv [] ∅
      { v := nsEmpty, c := nsEmpty, t := nsEmpty }
  | cons : ∀ (extra_checks : Bool) tenv d ds decls1 tenv1 decls2 tenv2,
    type_d extra_checks tenv d decls1 tenv1 →
    type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
    Set.Disjoint decls1 decls2 →
    type_ds extra_checks tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1)
end

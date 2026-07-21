/-
  Translation of typeSoundInvariantsScript.sml
  A type system for values, and the invariants that are used for type soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.TypeSystem
import LeanTypeSound.NamespaceProps

open HOL4

-- ============================================================
-- Types
-- ============================================================

/- HOL4:
Datatype:
 store_t =
 | Ref_t t
 | W8array_t
 | Varray_t t
End
-/
inductive store_t where
  | Ref_t : sem_t → store_t
  | W8array_t : store_t
  | Varray_t : sem_t → store_t

/- HOL4: Type tenv_store = ``:(num, store_t) fmap`` -/
abbrev tenv_store := Finmap Nat store_t

/- HOL4: Type ctMap = ``:(stamp, (tvarN list # t list # type_ident)) fmap`` -/
abbrev ctMap := Finmap stamp (List tvarN × List sem_t × type_ident)

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition tenv_abbrev_ok_def:
  tenv_abbrev_ok tenvT ⇔ nsAll (\id (tvs,t). check_freevars 0 tvs t) tenvT
End
-/
def tenv_abbrev_ok (tenvT : tenv_abbrev) : Prop :=
  nsAll (fun _ p => check_freevars 0 p.1 p.2) tenvT

/- HOL4:
Definition tenv_ctor_ok_def:
  tenv_ctor_ok tenvC ⇔ nsAll (\id (tvs,ts,tn). EVERY (check_freevars 0 tvs) ts) tenvC
End
-/
def tenv_ctor_ok (tenvC : tenv_ctor) : Prop :=
  nsAll (fun _ p => match p with | (tvs, ts, _) => EVERY (check_freevars 0 tvs) ts) tenvC

/- HOL4:
Definition tenv_val_ok_def:
  tenv_val_ok tenvV ⇔ nsAll (\id (tvs,t). check_freevars tvs [] t) tenvV
End
-/
def tenv_val_ok (tenvV : tenv_val) : Prop :=
  nsAll (fun _ p => check_freevars p.1 [] p.2) tenvV

/- HOL4:
Definition tenv_ok_def:
  tenv_ok tenv ⇔
    tenv_val_ok tenv.v ∧
    tenv_ctor_ok tenv.c ∧
    tenv_abbrev_ok tenv.t
End
-/
def tenv_ok (tenv : type_env) : Prop :=
  tenv_val_ok tenv.v ∧
  tenv_ctor_ok tenv.c ∧
  tenv_abbrev_ok tenv.t

/- HOL4:
Definition tenv_val_exp_ok_def:
  (tenv_val_exp_ok Empty ⇔ T) ∧
  (tenv_val_exp_ok (Bind_tvar n tenv) ⇔ tenv_val_exp_ok tenv) ∧
  (tenv_val_exp_ok (Bind_name x tvs t tenv) ⇔
    check_freevars (tvs + num_tvs tenv) [] t ∧
    tenv_val_exp_ok tenv)
End
-/
def tenv_val_exp_ok : tenv_val_exp → Prop
  | .Empty => True
  | .Bind_tvar _ tenv => tenv_val_exp_ok tenv
  | .Bind_name _ tvs t tenv =>
    check_freevars (tvs + num_tvs tenv) [] t ∧ tenv_val_exp_ok tenv

/- HOL4:
Definition ctMap_ok_def:
  ctMap_ok ctMap ⇔
    FEVERY (\ (stamp,(tvs,ts, _)). EVERY (check_freevars 0 tvs) ts) ctMap ∧
    (!ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs, ts, ti) ⇒
      tvs = [] ∧ ti = Texn_num) ∧
    (!cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME (tvs, ts, ti) ⇒
      ~MEM ti prim_type_nums) ∧
    (!stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
      FLOOKUP ctMap stamp1 = SOME (tvs1, ts1, ti) ∧
      FLOOKUP ctMap stamp2 = SOME (tvs2, ts2, ti) ⇒
      same_type stamp1 stamp2)
End
-/
def ctMap_ok (ctMap : ctMap) : Prop :=
  Finmap.FEVERY (fun (_, (tvs, ts, _)) => EVERY (check_freevars 0 tvs) ts) ctMap ∧
  (∀ ex tvs ts ti, Finmap.FLOOKUP ctMap (.ExnStamp ex) = some (tvs, ts, ti) →
    tvs = [] ∧ ti = Texn_num) ∧
  (∀ cn x tvs ts ti, Finmap.FLOOKUP ctMap (.TypeStamp cn x) = some (tvs, ts, ti) →
    ¬(prim_type_nums.elem ti)) ∧
  (∀ stamp1 tvs1 ts1 ti stamp2 tvs2 ts2,
    Finmap.FLOOKUP ctMap stamp1 = some (tvs1, ts1, ti) ∧
    Finmap.FLOOKUP ctMap stamp2 = some (tvs2, ts2, ti) →
    same_type stamp1 stamp2)

/- HOL4:
Definition type_ctor_def:
  type_ctor ctMap _ (n, stamp) (tvs, ts, ti) ⇔
    FLOOKUP ctMap stamp = SOME (tvs, ts, ti) ∧
    LENGTH ts = n
End
-/
def type_ctor (ctMap : ctMap) (_ : cml_id modN conN) (p1 : Nat × stamp) (p2 : List tvarN × List sem_t × type_ident) : Prop :=
  Finmap.FLOOKUP ctMap p1.2 = some p2 ∧
  p2.2.1.length = p1.1

/- HOL4:
Definition add_tenvE_def:
  (add_tenvE Empty tenvV = tenvV) ∧
  (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) ∧
  (add_tenvE (Bind_name x tvs t tenvE) tenvV = nsBind x (tvs,t) (add_tenvE tenvE tenvV))
End
-/
def add_tenvE : tenv_val_exp → tenv_val → tenv_val
  | .Empty, tenvV => tenvV
  | .Bind_tvar _ tenvE, tenvV => add_tenvE tenvE tenvV
  | .Bind_name x tvs t tenvE, tenvV => nsBind x (tvs, t) (add_tenvE tenvE tenvV)

-- ============================================================
-- Inductive relation: type_v
-- ============================================================

/- HOL4:
Inductive type_v:
  ... (14 rules)
End
-/
inductive type_v : Nat → ctMap → tenv_store → v → sem_t → Prop where
  | litv_int : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (n : Int),
    type_v tvs ctMap_ tenvS (.Litv (.IntLit n)) Tint
  | litv_char : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (c : Char),
    type_v tvs ctMap_ tenvS (.Litv (.Char c)) Tchar
  | litv_str : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (s : mlstring),
    type_v tvs ctMap_ tenvS (.Litv (.StrLit s)) Tstring
  | litv_word8 : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (w : word8),
    type_v tvs ctMap_ tenvS (.Litv (.Word8 w)) Tword8
  | litv_word64 : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (w : word64),
    type_v tvs ctMap_ tenvS (.Litv (.Word64 w)) Tword64
  | litv_float64 : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (w : word64),
    type_v tvs ctMap_ tenvS (.Litv (.Float64 w)) Tdouble
  | conv_some : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (ts' : List sem_t) (tvs' : List tvarN) (vs : List v) (ts : List sem_t)
      (ti : type_ident) (stmp : stamp),
    (∀ t', t' ∈ ts' → check_freevars tvs [] t') →
    tvs'.length = ts'.length →
    vs.length = (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts').reverse))).length →
    (∀ (i : Nat), i < vs.length →
      type_v tvs ctMap_ tenvS vs[i]!
        (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts').reverse)))[i]!) →
    Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, ti) →
    type_v tvs ctMap_ tenvS (.Conv (some stmp) vs) (.Tapp ts' ti)
  | conv_none : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (vs : List v) (ts : List sem_t),
    vs.length = ts.length →
    (∀ (i : Nat), i < vs.length → type_v tvs ctMap_ tenvS vs[i]! ts[i]!) →
    type_v tvs ctMap_ tenvS (.Conv none vs) (Ttup ts)
  | closure : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env)
      (n : varN) (e : exp) (t1 t2 : sem_t),
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap_) (sem_env_c env) tenv.c →
    /- nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v)
       expanded for strict positivity: domain equality + typing property -/
    (∀ (id_ : cml_id modN varN),
      (nsLookup (sem_env_v env) id_ = none ↔ nsLookup (add_tenvE tenvE tenv.v) id_ = none)) →
    (∀ (id_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t),
      nsLookup (sem_env_v env) id_ = some val_ →
      nsLookup (add_tenvE tenvE tenv.v) id_ = some p →
      type_v p.1 ctMap_ tenvS val_ p.2) →
    check_freevars tvs [] t1 →
    type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 →
    type_v tvs ctMap_ tenvS (.Closure env n e) (Tfn t1 t2)
  | recclosure : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env)
      (n : varN) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (t : sem_t),
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap_) (sem_env_c env) tenv.c →
    /- nsAll2 expanded: domain equality + typing property -/
    (∀ (id_ : cml_id modN varN),
      (nsLookup (sem_env_v env) id_ = none ↔ nsLookup (add_tenvE tenvE tenv.v) id_ = none)) →
    (∀ (id_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t),
      nsLookup (sem_env_v env) id_ = some val_ →
      nsLookup (add_tenvE tenvE tenv.v) id_ = some p →
      type_v p.1 ctMap_ tenvS val_ p.2) →
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings →
    ALOOKUP bindings n = some t →
    ALL_DISTINCT (funs.map Prod.fst) →
    n ∈ (funs.map Prod.fst) →
    type_v tvs ctMap_ tenvS (.Recclosure env funs n) t
  | loc_ref : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (t : sem_t) (n : Nat),
    check_freevars 0 [] t →
    Finmap.FLOOKUP tenvS n = some (.Ref_t t) →
    type_v tvs ctMap_ tenvS (.Loc true n) (Tref t)
  | loc_w8array : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (n : Nat),
    Finmap.FLOOKUP tenvS n = some .W8array_t →
    type_v tvs ctMap_ tenvS (.Loc true n) Tword8array
  | loc_varray : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (t : sem_t) (n : Nat),
    check_freevars 0 [] t →
    Finmap.FLOOKUP tenvS n = some (.Varray_t t) →
    type_v tvs ctMap_ tenvS (.Loc true n) (Tarray t)
  | vectorv : ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store)
      (t : sem_t) (vs : List v),
    check_freevars 0 [] t →
    (∀ w, w ∈ vs → type_v tvs ctMap_ tenvS w t) →
    type_v tvs ctMap_ tenvS (.Vectorv vs) (Tvector t)

-- ============================================================
-- More definitions
-- ============================================================

/- HOL4:
Definition type_sv_def:
  (type_sv ctMap tenvS (Refv v) (Ref_t t) ⇔ type_v 0 ctMap tenvS v t) ∧
  (type_sv ctMap tenvS (W8array v) W8array_t ⇔ T) ∧
  (type_sv ctMap tenvS (Varray vs) (Varray_t t) ⇔
    EVERY (\v. type_v 0 ctMap tenvS v t) vs) ∧
  (type_sv _ _ _ _ ⇔ F)
End
-/
def type_sv (ctMap : ctMap) (tenvS : tenv_store) : store_v v → store_t → Prop
  | .Refv val_, .Ref_t t => type_v 0 ctMap tenvS val_ t
  | .W8array _, .W8array_t => True
  | .Varray vs, .Varray_t t => ∀ w, w ∈ vs → type_v 0 ctMap tenvS w t
  | _, _ => False

/- HOL4:
Definition type_s_def:
  type_s ctMap envS tenvS ⇔
    (!l.
      ((?st. FLOOKUP tenvS l = SOME st) ⇔ (?v. store_lookup l envS = SOME v)) ∧
      (!st sv.
        FLOOKUP tenvS l = SOME st ∧ store_lookup l envS = SOME sv
        ⇒
        type_sv ctMap tenvS sv st))
End
-/
def type_s (ctMap : ctMap) (envS : List (store_v v)) (tenvS : tenv_store) : Prop :=
  ∀ l,
    ((∃ st, Finmap.FLOOKUP tenvS l = some st) ↔ (∃ v_, store_lookup l envS = some v_)) ∧
    (∀ st sv,
      Finmap.FLOOKUP tenvS l = some st ∧ store_lookup l envS = some sv →
      type_sv ctMap tenvS sv st)

/- HOL4:
Definition ctMap_has_exns_def:
  ctMap_has_exns ctMap ⇔
    FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)
End
-/
def ctMap_has_exns (ctMap : ctMap) : Prop :=
  Finmap.FLOOKUP ctMap bind_stamp = some ([], [], Texn_num) ∧
  Finmap.FLOOKUP ctMap chr_stamp = some ([], [], Texn_num) ∧
  Finmap.FLOOKUP ctMap div_stamp = some ([], [], Texn_num) ∧
  Finmap.FLOOKUP ctMap subscript_stamp = some ([], [], Texn_num)

/- HOL4:
Definition ctMap_has_lists_def:
  ctMap_has_lists ctMap ⇔
    FLOOKUP ctMap (TypeStamp «[]» list_type_num) = SOME ([«'a»],[],Tlist_num) ∧
    FLOOKUP ctMap (TypeStamp «::» list_type_num) =
      SOME ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num) ∧
    (!cn. cn ≠ «::» ∧ cn ≠ «[]» ⇒ FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)
End
-/
def ctMap_has_lists (ctMap : ctMap) : Prop :=
  Finmap.FLOOKUP ctMap (.TypeStamp (mlstring.strlit "[]") list_type_num) =
    some ([mlstring.strlit "'a"], [], Tlist_num) ∧
  Finmap.FLOOKUP ctMap (.TypeStamp (mlstring.strlit "::") list_type_num) =
    some ([mlstring.strlit "'a"],
          [.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))],
          Tlist_num) ∧
  (∀ cn, cn ≠ mlstring.strlit "::" ∧ cn ≠ mlstring.strlit "[]" →
    Finmap.FLOOKUP ctMap (.TypeStamp cn list_type_num) = none)

/- HOL4:
Definition ctMap_has_bools_def:
  ctMap_has_bools ctMap ⇔
    FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) ∧
    FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) ∧
    (!cn. cn ≠ «True» ∧ cn ≠ «False» ⇒ FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)
End
-/
def ctMap_has_bools (ctMap : ctMap) : Prop :=
  Finmap.FLOOKUP ctMap (.TypeStamp (mlstring.strlit "True") bool_type_num) =
    some ([], [], Tbool_num) ∧
  Finmap.FLOOKUP ctMap (.TypeStamp (mlstring.strlit "False") bool_type_num) =
    some ([], [], Tbool_num) ∧
  (∀ cn, cn ≠ mlstring.strlit "True" ∧ cn ≠ mlstring.strlit "False" →
    Finmap.FLOOKUP ctMap (.TypeStamp cn bool_type_num) = none)

/- HOL4:
Definition good_ctMap_def:
  good_ctMap ctMap ⇔
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap
End
-/
def good_ctMap (ctMap : ctMap) : Prop :=
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ∧
  ctMap_has_exns ctMap ∧
  ctMap_has_lists ctMap

/- HOL4:
Definition consistent_ctMap_def:
  consistent_ctMap st type_ids ctMap ⇔
    (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) ∧
    !cn id.
      (TypeStamp cn id ∈ FDOM ctMap ⇒ id < st.next_type_stamp) ∧
      (ExnStamp id ∈ FDOM ctMap ⇒ id < st.next_exn_stamp)
End
-/
def consistent_ctMap {ffi : Type} (st : cml_state ffi) (type_ids : Set type_ident) (ctMap : ctMap) : Prop :=
  Set.Disjoint' type_ids (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap)) ∧
  ∀ cn id_,
    (stamp.TypeStamp cn id_ ∈ Finmap.FDOM ctMap → id_ < st.next_type_stamp) ∧
    (stamp.ExnStamp id_ ∈ Finmap.FDOM ctMap → id_ < st.next_exn_stamp)

/- HOL4:
Definition type_all_env_def:
  type_all_env ctMap tenvS env tenv ⇔
    nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v env) tenv.v
End
-/
def type_all_env (ctMap : ctMap) (tenvS : tenv_store) (env : sem_env) (tenv : type_env) : Prop :=
  nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
  nsAll2 (fun _ v_ p => type_v p.1 ctMap tenvS v_ p.2) (sem_env_v env) tenv.v

/- HOL4:
Definition type_sound_invariant_def:
type_sound_invariant st env ctMap tenvS type_idents tenv ⇔
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS
End
-/
def type_sound_invariant {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (ctMap : ctMap) (tenvS : tenv_store) (type_idents : Set type_ident) (tenv : type_env) : Prop :=
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS

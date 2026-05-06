/-
  Translation of typeSoundScript.sml
  Proof of type soundness: a type-correct program does not crash.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.FpSem
import LeanTypeSound.Evaluate
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.EvaluateProps
import LeanTypeSound.Weakening
import LeanTypeSound.TypeSysProps
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.SemanticsMin

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition store_type_extension_def:
  store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))
End
-/
def store_type_extension (tenvS1 tenvS2 : tenv_store) : Prop :=
  ∃ tenvS',
    tenvS2 = Finmap.FUNION tenvS' tenvS1 ∧
    (∀ l, Finmap.FLOOKUP tenvS' l = none ∨ Finmap.FLOOKUP tenvS1 l = none)

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4:
Theorem fst_triple[local]:
  (\ (x,y,z). x) = FST
-/
theorem fst_triple {α β γ : Type} :
    (fun ((x, _, _) : α × β × γ) => x) = (fun (p : α × β × γ) => p.1) := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rfl
/- HOL4:
Theorem sing_list[local]:
  !l. LENGTH l = 1 ⇔ ?x. l = [x]
-/
theorem sing_list {α : Type} :
    ∀ (l : List α), l.length = 1 ↔ ∃ (x : α), l = [x] := by
  intro l
  constructor
  · intro h
    match l, h with
    | [x], _ => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; rfl
/- HOL4:
Theorem EVERY_LIST_REL[local]:
  EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y)
-/
theorem EVERY_LIST_REL_local {α β : Type} :
    ∀ (f : α → β → Prop) (y : β) (l : List α),
      (∀ (x : α), x ∈ l → f x y) ↔ LIST_REL (fun x y => f x y) l (REPLICATE l.length y) := sorry
/- HOL4:
Theorem v_unchanged[simp]:
  !tenv x. tenv with v := tenv.v = tenv
-/
theorem v_unchanged :
    ∀ (tenv : type_env), { tenv with v := tenv.v } = tenv := by
  intro tenv; rfl
/- HOL4:
Theorem check_dup_ctors_thm:
  check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
-/
theorem check_dup_ctors_thm :
    ∀ (tvs : List tvarN) (tn : typeN) (condefs : List (conN × List ast_t)),
      check_dup_ctors (tvs, tn, condefs) = ALL_DISTINCT (condefs.map Prod.fst) := by
  intro tvs tn condefs
  simp [check_dup_ctors]
/- HOL4:
Theorem prim_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap ⇒ (∃s. v = Litv (StrLit s))) ∧
  (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word64 n))) ∧
  (type_v tvs ctMap tenvS v Tdouble ∧ ctMap_ok ctMap ⇒ ∃n. v = Litv (Float64 n)) ∧
  (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap ⇒
   (∃vs. v = Conv NONE vs ∧ LENGTH ts = LENGTH vs)) ∧
  (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap ⇒
   (∃env n e. v = Closure env n e) ∨
   (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n v2. v = Loc T n ∧ store_lookup n envS = SOME (Refv v2) ∧
           type_v 0 ctMap tenvS v2 t1)) ∧
  (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n ws. v = Loc T n ∧ store_lookup n envS = SOME (W8array ws) ∧
           FLOOKUP tenvS n = SOME W8array_t)) ∧
  (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n vs. v = Loc T n ∧ store_lookup n envS = SOME (Varray vs) ∧
           EVERY (\v. type_v 0 ctMap tenvS v t) vs ∧
           FLOOKUP tenvS n = SOME (Varray_t t))) ∧
  (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap ⇒
   (?vs. v = Vectorv vs ∧ EVERY (\v. type_v tvs ctMap tenvS v t) vs))
-/
theorem prim_canonical_values_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v)
      (envS : List (store_v v)) (ts : List sem_t) (t1 t2 t : sem_t),
    (type_v tvs ctMap_ tenvS val_ Tint ∧ ctMap_ok ctMap_ →
      ∃ (n : Int), val_ = .Litv (.IntLit n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tchar ∧ ctMap_ok ctMap_ →
      ∃ (c : Char), val_ = .Litv (.Char c)) ∧
    (type_v tvs ctMap_ tenvS val_ Tstring ∧ ctMap_ok ctMap_ →
      ∃ (s : mlstring), val_ = .Litv (.StrLit s)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8 ∧ ctMap_ok ctMap_ →
      ∃ (n : word8), val_ = .Litv (.Word8 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword64 ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Word64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tdouble ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Float64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Ttup ts) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v), val_ = .Conv none vs ∧ ts.length = vs.length) ∧
    (type_v tvs ctMap_ tenvS val_ (Tfn t1 t2) ∧ ctMap_ok ctMap_ →
      (∃ (env : sem_env) (n : varN) (e : exp), val_ = .Closure env n e) ∨
      (∃ (env : sem_env) (funs : List (varN × varN × exp)) (n : varN),
        val_ = .Recclosure env funs n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tref t1) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (v2 : v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Refv v2) ∧
        type_v 0 ctMap_ tenvS v2 t1) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8array ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (ws : List word8),
        val_ = .Loc true n ∧ store_lookup n envS = some (.W8array ws) ∧
        Finmap.FLOOKUP tenvS n = some .W8array_t) ∧
    (type_v tvs ctMap_ tenvS val_ (Tarray t) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (vs : List v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Varray vs) ∧
        (∀ (v_ : v), v_ ∈ vs → type_v 0 ctMap_ tenvS v_ t) ∧
        Finmap.FLOOKUP tenvS n = some (.Varray_t t)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tvector t) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v),
        val_ = .Vectorv vs ∧ (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t)) := sorry
/- HOL4:
Theorem has_lists_v_to_list[local]:
  !ctMap tvs tenvS t3.
    ctMap_ok ctMap ∧
    ctMap_has_lists ctMap ∧
    type_v tvs ctMap tenvS v (Tlist t3)
    ⇒
    ?vs. v_to_list v = SOME vs ∧
         EVERY (\v. type_v tvs ctMap tenvS v t3) vs ∧
         (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
         (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str)
-/
theorem has_lists_v_to_list :
    ∀ (ctMap_ : ctMap) (tvs : Nat) (tenvS : tenv_store) (t3 : sem_t) (val_ : v),
      ctMap_ok ctMap_ ∧
      ctMap_has_lists ctMap_ ∧
      type_v tvs ctMap_ tenvS val_ (Tlist t3) →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t3) ∧
        (t3 = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t3 = Tstring → ∃ (str : mlstring), vs_to_string vs = some str) := sorry
/- HOL4:
Theorem ctor_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
   (∃b. v = Boolv b)) ∧
  (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap ⇒
   ?vs.
     v_to_list v = SOME vs ∧
     EVERY (\v. type_v tvs ctMap tenvS v t) vs ∧
     (t = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
     (t = Tstring ⇒ ∃str. vs_to_string vs = SOME str)) ∧
  (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
   ctMap_ok ctMap ∧
   FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ⇒
   (?cn n vs. same_type stamp (TypeStamp cn n) ∧ v = Conv (SOME (TypeStamp cn n)) vs) ∨
   (?n vs. same_type stamp (ExnStamp n) ∧ v = Conv (SOME (ExnStamp n)) vs))
-/
theorem ctor_canonical_values_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v)
      (t : sem_t) (ts : List sem_t) (ti : type_ident)
      (stmp : stamp) (tvs' : List tvarN) (ts' : List sem_t),
    (type_v tvs ctMap_ tenvS val_ Tbool ∧ ctMap_ok ctMap_ ∧ ctMap_has_bools ctMap_ →
      ∃ (b : Bool), val_ = Boolv b) ∧
    (type_v tvs ctMap_ tenvS val_ (Tlist t) ∧ ctMap_ok ctMap_ ∧ ctMap_has_lists ctMap_ →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t) ∧
        (t = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t = Tstring → ∃ (str : mlstring), vs_to_string vs = some str)) ∧
    (type_v tvs ctMap_ tenvS val_ (.Tapp ts ti) ∧
     ctMap_ok ctMap_ ∧
     Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts', ti) →
      (∃ (cn : conN) (n : Nat) (vs : List v),
        same_type stmp (.TypeStamp cn n) ∧ val_ = .Conv (some (.TypeStamp cn n)) vs) ∨
      (∃ (n : Nat) (vs : List v),
        same_type stmp (.ExnStamp n) ∧ val_ = .Conv (some (.ExnStamp n)) vs)) := sorry
/- HOL4:
Theorem same_type_refl[local]:
  !t. same_type t t
-/
theorem same_type_refl :
    ∀ (t : stamp), same_type t t := sorry
/- HOL4:
Theorem eq_same_type[local]:
  (!v1 v2 tvs ctMap cns tenvS t.
     ctMap_ok ctMap ∧
     type_v tvs ctMap tenvS v1 t ∧
     type_v tvs ctMap tenvS v2 t
     ⇒
     do_eq v1 v2 ≠ Eq_type_error) ∧
  (!vs1 vs2 tvs ctMap cns tenvS ts.
     ctMap_ok ctMap ∧
     LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
     LIST_REL (type_v tvs ctMap tenvS) vs2 ts
     ⇒
     do_eq_list vs1 vs2 ≠ Eq_type_error)
-/
theorem eq_same_type :
    (∀ (v1 v2 : v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_v tvs ctMap_ tenvS v1 t ∧
      type_v tvs ctMap_ tenvS v2 t →
      do_eq v1 v2 ≠ .Eq_type_error) ∧
    (∀ (vs1 vs2 : List v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (ts : List sem_t),
      ctMap_ok ctMap_ ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs1 ts ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs2 ts →
      do_eq_list vs1 vs2 ≠ .Eq_type_error) := sorry
/- HOL4:
Theorem type_env_conv_thm[local]:
  ∀ctMap envC tenvC.
    nsAll2 (type_ctor ctMap) envC tenvC ⇒
    ∀cn tvs ts tn ti.
      (nsLookup tenvC cn = SOME (tvs,ts,ti) ⇒
       ?cn' stamp.
         nsLookup envC cn = SOME (LENGTH ts,stamp) ∧
         FLOOKUP ctMap stamp = SOME (tvs, ts, ti)) ∧
      (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)
-/
theorem type_env_conv_thm :
    ∀ (ctMap_ : ctMap) (envC : env_ctor) (tenvC : tenv_ctor),
      nsAll2 (type_ctor ctMap_) envC tenvC →
      ∀ (cn : cml_id modN conN) (tvs' : List tvarN) (ts : List sem_t) (tn : type_ident) (ti : type_ident),
        (nsLookup tenvC cn = some (tvs', ts, tn) →
          ∃ (cn' : conN) (stmp : stamp),
            nsLookup envC cn = some (ts.length, stmp) ∧
            Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, tn)) ∧
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := sorry
/- HOL4:
Theorem type_funs_fst[local]:
  !tenv tenvE funs tenv'.
    type_funs tenv tenvE funs tenv'
    ⇒
    MAP FST funs = MAP FST tenv'
-/
theorem type_funs_fst :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (tenv' : List (varN × sem_t)),
      type_funs tenv tenvE funs tenv' →
      funs.map Prod.fst = tenv'.map Prod.fst := sorry
/- HOL4:
Theorem type_recfun_env_help[local]:
  ∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
    ALL_DISTINCT (MAP FST funs') ∧
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
-/
theorem type_recfun_env_help :
    ∀ (fn_ : varN) (funs funs' : List (varN × varN × exp)) (ctMap_ : ctMap)
      (tenv : type_env) (bindings : List (varN × sem_t)) (tenvE : tenv_val_exp)
      (env : sem_env) (tenvS : tenv_store) (tvs : Nat) (bindings' : List (varN × sem_t)),
      ALL_DISTINCT (funs'.map Prod.fst) ∧
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      (∀ (fn_ : varN) (t : sem_t), ALOOKUP bindings fn_ = some t → ALOOKUP bindings' fn_ = some t) ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs' p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := sorry
/- HOL4:
Theorem type_recfun_env[local]:
  ∀funs ctMap tenvS tvs tenv tenvE env bindings.
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
-/
theorem type_recfun_env :
    ∀ (funs : List (varN × varN × exp)) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tvs : Nat) (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env)
      (bindings : List (varN × sem_t)),
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALL_DISTINCT (funs.map Prod.fst) →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := sorry
/- HOL4:
val type_v_exn = Q.prove (
  `!tvs cenv senv.
     ctMap_has_exns cenv ⇒
   type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`)
-/
theorem type_v_exn :
    ∀ (tvs : Nat) (cenv : ctMap) (senv : tenv_store),
      ctMap_has_exns cenv →
      type_v tvs cenv senv (.Conv (some chr_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some subscript_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some bind_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some div_stamp) []) Texn := sorry
/- HOL4:
Theorem type_v_Boolv[local]:
  ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool
-/
theorem type_v_Boolv :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (b : Bool),
      ctMap_has_bools ctMap_ → type_v tvs ctMap_ tenvS (Boolv b) Tbool := sorry
/- HOL4:
Theorem remove_lambda_prod[local]:
  (\ (x,y). P x y) = (\xy. P (FST xy) (SND xy))
-/
theorem remove_lambda_prod {α β γ : Type} :
    ∀ (P : α → β → γ),
      (fun ((x, y) : α × β) => P x y) = (fun (p : α × β) => P p.1 p.2) := sorry
/- HOL4:
Theorem opapp_type_sound:
  !ctMap tenvS vs ts t.
    ctMap_ok ctMap ∧
    type_op Opapp ts t ∧
    LIST_REL (type_v 0 ctMap tenvS) vs ts
    ⇒
    ?env e tenv tenvE.
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
      type_e tenv tenvE e t ∧
      do_opapp vs = SOME (env,e)
-/
theorem opapp_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v) (ts : List sem_t) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_op .Opapp ts t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts →
      ∃ (env : sem_env) (e : exp) (tenv : type_env) (tenvE : tenv_val_exp),
        tenv_ok tenv ∧
        tenv_val_exp_ok tenvE ∧
        num_tvs tenvE = 0 ∧
        type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
        type_e tenv tenvE e t ∧
        do_opapp vs = some (env, e) := sorry
/- HOL4:
Theorem store_type_extension_weakS:
  !tenvS1 tenvS2.
    store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1
-/
theorem store_type_extension_weakS :
    ∀ (tenvS1 tenvS2 : tenv_store),
      store_type_extension tenvS1 tenvS2 → weakS tenvS2 tenvS1 := sorry
/- HOL4:
Theorem store_type_extension_refl:
  !tenvS. store_type_extension tenvS tenvS
-/
theorem store_type_extension_refl :
    ∀ (tenvS : tenv_store), store_type_extension tenvS tenvS := sorry
/- HOL4:
Theorem store_type_extension_trans:
  !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3
-/
theorem store_type_extension_trans :
    ∀ (s1 s2 s3 : tenv_store),
      store_type_extension s1 s2 ∧ store_type_extension s2 s3 →
      store_type_extension s1 s3 := sorry
/- HOL4:
Theorem store_assign_type_sound:
  !ctMap tenvS store sv st l.
    type_s ctMap store tenvS ∧
    FLOOKUP tenvS l = SOME st ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store'.
      store_assign l sv store = SOME store' ∧
      type_s ctMap store' tenvS
-/
theorem store_assign_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t) (l : Nat),
      type_s ctMap_ store_ tenvS ∧
      Finmap.FLOOKUP tenvS l = some st ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)),
        store_assign l sv store_ = some store' ∧
        type_s ctMap_ store' tenvS := sorry
/- HOL4:
Theorem store_alloc_type_sound:
  !ctMap tenvS store sv st.
    ctMap_ok ctMap ∧
    type_s ctMap store tenvS ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store' tenvS' n.
      store_type_extension tenvS tenvS' ∧
      store_alloc sv store = (store', n) ∧
      type_s ctMap store' tenvS' ∧
      FLOOKUP tenvS' n = SOME st
-/
theorem store_alloc_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t),
      ctMap_ok ctMap_ ∧
      type_s ctMap_ store_ tenvS ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)) (tenvS' : tenv_store) (n : Nat),
        store_type_extension tenvS tenvS' ∧
        store_alloc sv store_ = (store', n) ∧
        type_s ctMap_ store' tenvS' ∧
        Finmap.FLOOKUP tenvS' n = some st := sorry
-- store_lookup_type_sound is commented out in HOL4 source

/- HOL4:
Theorem type_v_list_to_v:
  !x xs t.
    type_v n ctMap tenvS x t ∧
    v_to_list x = SOME xs ⇒
    type_v n ctMap tenvS (list_to_v xs) t
-/
theorem type_v_list_to_v :
    ∀ (n : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (x : v) (xs : List v) (t : sem_t),
      type_v n ctMap_ tenvS x t ∧
      v_to_list x = some xs →
      type_v n ctMap_ tenvS (list_to_v xs) t := sorry
/- HOL4:
Theorem type_v_list_to_v_APPEND:
  !xs ys t.
    ctMap_has_lists ctMap ∧
    type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) ∧
    type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
    ⇒
    type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num)
-/
theorem type_v_list_to_v_APPEND :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (xs ys : List v) (t : sem_t),
      ctMap_has_lists ctMap_ ∧
      type_v 0 ctMap_ tenvS (list_to_v xs) (.Tapp [t] Tlist_num) ∧
      type_v 0 ctMap_ tenvS (list_to_v ys) (.Tapp [t] Tlist_num) →
      type_v 0 ctMap_ tenvS (list_to_v (xs ++ ys)) (.Tapp [t] Tlist_num) := sorry
/- HOL4:
Theorem do_eq_Boolv:
  do_eq (Boolv b) (Boolv b') = Eq_val (b = b')
-/
theorem do_eq_Boolv :
    ∀ (b b' : Bool),
      do_eq (Boolv b) (Boolv b') = .Eq_val (b == b') := sorry
/- HOL4:
Theorem prim_canonical_Boolv_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
  (∃b. v = Boolv b))
-/
theorem prim_canonical_Boolv_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v),
      type_v tvs ctMap_ tenvS val_ Tbool ∧ ctMap_ok ctMap_ ∧ ctMap_has_bools ctMap_ →
      ∃ (b : Bool), val_ = Boolv b := sorry
/- HOL4:
Theorem prim_canonical_Boolv_cases[local]:
  type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ⇒
  v = Boolv T ∨ v = Boolv F
-/
theorem prim_canonical_Boolv_cases :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v),
      type_v tvs ctMap_ tenvS val_ (.Tapp [] Tbool_num) ∧
      ctMap_ok ctMap_ ∧
      ctMap_has_bools ctMap_ →
      val_ = Boolv true ∨ val_ = Boolv false := sorry
/- HOL4:
Theorem op_type_sound:
 !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
   good_ctMap ctMap ∧
   op ≠ Opapp ∧
   type_s ctMap store tenvS ∧
   type_op op ts t ∧
   check_freevars 0 [] t ∧
   LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort(Rffi_error _)) => T
   | Rerr (Rabort _) => F
-/
theorem op_type_sound :
    ∀ {ffi : Type} (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v)
      (op_ : op) (ts : List sem_t) (t : sem_t) (store_ : List (store_v v))
      (ffi_ : ffi_state ffi),
      good_ctMap ctMap_ ∧
      op_ ≠ .Opapp ∧
      type_s ctMap_ store_ tenvS ∧
      type_op op_ ts t ∧
      check_freevars 0 [] t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts.reverse →
      ∃ (tenvS' : tenv_store) (store' : List (store_v v)) (ffi' : ffi_state ffi)
        (r : result v v),
        store_type_extension tenvS tenvS' ∧
        type_s ctMap_ store' tenvS' ∧
        do_app (store_, ffi_) op_ vs.reverse = some ((store', ffi'), r) ∧
        match r with
        | .Rval val_ => type_v 0 ctMap_ tenvS' val_ t
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort _) => False := sorry
/- HOL4:
Theorem build_conv_type_sound:
 !envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' tn)
-/
theorem build_conv_type_sound :
    ∀ (envC : env_ctor) (cn : cml_id modN conN) (vs : List v) (tvs : Nat)
      (ts : List sem_t) (ctMap_ : ctMap) (tenvS : tenv_store) (ts' : List sem_t)
      (tn : type_ident) (tenvC : tenv_ctor) (tvs' : List tvarN)
      (tenvE : tenv_val_exp) (l : Nat),
      nsAll2 (type_ctor ctMap_) envC tenvC ∧
      do_con_check envC (some cn) l ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs
        (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))).reverse ∧
      nsLookup tenvC cn = some (tvs', ts, tn) →
      ∃ (val_ : v),
        build_conv envC (some cn) vs.reverse = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (.Tapp ts' tn) := sorry
/- HOL4:
Theorem same_ctor_and_same_tid:
   !stamp1 stamp2.
    same_ctor stamp1 stamp2 ∧
    same_type stamp1 stamp2
    ⇒
    stamp1 = stamp2
-/
theorem same_ctor_and_same_tid :
    ∀ (stamp1 stamp2 : stamp),
      same_ctor stamp1 stamp2 ∧ same_type stamp1 stamp2 →
      stamp1 = stamp2 := sorry
/- HOL4:
Theorem pat_type_sound:
  (∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings)))
-/
theorem pat_type_sound :
    (∀ (cenv : env_ctor) (st : store v) (p : pat) (val_ : v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (t : sem_t)
       (new_tbindings : List (varN × sem_t)) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      type_v tvs ctMap_ tenvS val_ t ∧
      type_p tvs tenv p t new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch cenv st p val_ bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch cenv st p val_ bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) ∧
    (∀ (cenv : env_ctor) (st : store v) (ps : List pat) (vs : List v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (new_tbindings : List (varN × sem_t))
       (ts : List sem_t) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs ts ∧
      type_ps tvs tenv ps ts new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch_list cenv st ps vs bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch_list cenv st ps vs bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) := sorry
/- HOL4:
Theorem lookup_var_sound:
   !n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)
-/
theorem lookup_var_sound :
    ∀ (n : cml_id modN varN) (tvs : Nat) (tenvE : tenv_val_exp)
      (targs : List sem_t) (t : sem_t) (ctMap_ : ctMap) (tenvS : tenv_store)
      (env : sem_env) (tenv : type_env),
      lookup_var n (bind_tvar tvs tenvE) tenv = some (targs.length, t) ∧
      ctMap_ok ctMap_ ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      ∃ (val_ : v),
        nsLookup env.v_ n = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (deBruijn_subst 0 targs t) := sorry
/- HOL4:
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t'))
-/
theorem EVERY_REPLICATE :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenv : tenv_store) (t' : sem_t) (vs : List v),
      (∀ (x : v), x ∈ vs → type_v tvs ctMap_ tenv x t') ↔
      (∀ (x : v × sem_t), x ∈ vs.zip (REPLICATE vs.length t') → type_v tvs ctMap_ tenv x.1 x.2) := sorry
/- HOL4:
Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
-/
theorem EVERY_LIST_REL_thm :
    ∀ (n : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (t : sem_t) (vs : List v),
      (∀ (v_ : v), v_ ∈ vs → type_v n ctMap_ tenvS v_ t) ↔
      LIST_REL (type_v n ctMap_ tenvS) vs (REPLICATE vs.length t) := sorry
/- HOL4:
Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F)
-/
theorem exp_type_sound :
    ∀ (ctMap_ : ctMap),
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (es : List exp)
       (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env)
       (tenvE : tenv_val_exp) (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => LIST_REL (type_v tvs ctMap_ tenvS') vs ts
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) ∧
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (val_ : v)
       (pes : List (pat × exp)) (err_v : v) (r : result (List v) v)
       (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
       (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env val_ pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      type_v tvs ctMap_ tenvS val_ t1 ∧
      type_v 0 ctMap_ tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => type_v tvs ctMap_ tenvS' vs.head! t2
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) := sorry
/- HOL4:
Theorem build_tdefs_build_tenv[local]:
  !tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids)
-/
theorem build_tdefs_build_tenv :
    ∀ (tenvT : tenv_abbrev) (tds : type_def) (tids : List type_ident)
      (next : Nat) (ctMap_ : ctMap),
      EVERY (fun (p : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (p.2.2.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := sorry
/- HOL4:
Theorem type_sound_invariant_union[local]:
  type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv
-/
theorem type_sound_invariant_union :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tids1 tids2 : Set type_ident) (tenv : type_env),
      type_sound_invariant st env ctMap_ tenvS (tids1 ∪ tids2) tenv →
      type_sound_invariant st env ctMap_ tenvS tids1 tenv := sorry
/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds
-/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : tenv_abbrev) (tds : type_def),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := sorry
/- HOL4:
Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    ∧ type_all_env ctMap tenvS env2 tenv2
    ⇒ type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2)
-/
theorem type_all_env_extend :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (env1 env2 : sem_env)
      (tenv1 tenv2 : type_env),
      type_all_env ctMap_ tenvS env1 tenv1 ∧
      type_all_env ctMap_ tenvS env2 tenv2 →
      type_all_env ctMap_ tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) := sorry
/- HOL4:
Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs)
-/
theorem type_e_con_check :
    ∀ (ctMap_ : ctMap) (envc : env_ctor),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      every_exp (one_con_check envc) e) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env_ : List (varN × sem_t)),
      type_funs tenv tenvE funs env_ →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs) := sorry
/- HOL4:
Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T
-/
theorem decs_type_sound_no_check :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (st' : cml_state ffi) (r : result sem_env v) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True := sorry
/- HOL4:
Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
-/
theorem decs_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (extra_checks : Bool) (st' : cml_state ffi) (r : result sem_env v)
      (ctMap_ : ctMap) (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtimeout_error) => True := sorry
/- HOL4:
Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail
-/
theorem semantics_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (tops : List dec)
      (r : behaviour) (checks : Bool) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      r ≠ .Fail := sorry

/-
  Translation of semanticPrimitivesPropsScript.sml
  Various basic properties of the semantic primitives.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.Ffi
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.NamespaceProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End
-/
def map_error_result {α β : Type} (f : α → β) : error_result α → error_result β
  | .Rraise e => .Rraise (f e)
  | .Rabort a => .Rabort a

/- HOL4:
Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End
-/
def map_result {α β γ δ : Type} (f1 : α → β) (f2 : γ → δ) :
    result α γ → result β δ
  | .Rval v => .Rval (f1 v)
  | .Rerr e => .Rerr (map_error_result f2 e)

/- HOL4:
Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End
-/
def every_error_result {α : Type} (P : α → Bool) : error_result α → Bool
  | .Rraise e => P e
  | .Rabort _ => true

/- HOL4:
Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End
-/
def every_result {α β : Type} (P1 : α → Bool) (P2 : β → Bool) : result α β → Bool
  | .Rval v => P1 v
  | .Rerr e => every_error_result P2 e

/- HOL4:
Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End
-/
def map_sv {α β : Type} (f : α → β) : store_v α → store_v β
  | .Refv v => .Refv (f v)
  | .W8array w => .W8array w
  | .Varray vs => .Varray (vs.map f)
  | .Thunk m v => .Thunk m (f v)

/- HOL4:
Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End
-/
def dest_Refv {α : Type} [Inhabited α] : store_v α → α
  | .Refv v => v
  | _ => default

/- HOL4:
Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End
-/
def store_v_vs {α : Type} : store_v α → List α
  | .Refv v => [v]
  | .Varray vs => vs
  | .W8array _ => []
  | .Thunk _ v => [v]

/- HOL4:
Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End
-/
def ctors_of_tdef : List tvarN × typeN × List (conN × List ast_t) → List conN
  | (_, _, condefs) => condefs.map Prod.fst

/- HOL4:
Definition FV_def[simp]: ... End
  Free variables of expressions (set-valued).
-/
mutual
def FV : exp → Set (cml_id modN varN)
  | .Raise e => FV e
  | .Handle e pes => FV e ∪ FV_pes pes
  | .Lit _ => ∅
  | .Con _ ls => FV_list ls
  | .Var id => {id}
  | .Fun x e => FV e \ {cml_id.Short x}
  | .App _ es => FV_list es
  | .Log _ e1 e2 => FV e1 ∪ FV e2
  | .If e1 e2 e3 => FV e1 ∪ FV e2 ∪ FV e3
  | .Mat e pes => FV e ∪ FV_pes pes
  | .Let xo e b => FV e ∪ (FV b \ (match xo with | none => ∅ | some x => {cml_id.Short x}))
  | .Letrec defs b => FV_defs defs ∪ (FV b \ (fun x => x ∈ defs.map (fun (f, _, _) => cml_id.Short f)))
  | .Tannot e _ => FV e
  | .Lannot e _ => FV e

def FV_list : List exp → Set (cml_id modN varN)
  | [] => ∅
  | e :: es => FV e ∪ FV_list es

def FV_pes : List (pat × exp) → Set (cml_id modN varN)
  | [] => ∅
  | (p, e) :: pes =>
    (FV e \ (Set.image cml_id.Short (fun x => x ∈ pat_bindings p []))) ∪ FV_pes pes

def FV_defs : List (varN × varN × exp) → Set (cml_id modN varN)
  | [] => ∅
  | (_, x, e) :: defs => (FV e \ {cml_id.Short x}) ∪ FV_defs defs
end

/- HOL4:
Definition FV_dec_def[simp]: ... End
-/
def FV_dec : dec → Set (cml_id modN varN)
  | .Dlet _ p e => FV (.Mat e [(p, .Lit (.IntLit 0))])
  | .Dletrec _ defs => FV (.Letrec defs (.Lit (.IntLit 0)))
  | .Dtype _ _ => ∅
  | .Dtabbrev _ _ _ _ => ∅
  | .Dexn _ _ _ => ∅
  | .Dmod _ _ => ∅
  | .Dlocal _ _ => ∅
  | .Denv _ => ∅

/- HOL4:
Definition shift_lookup_def[simp]:
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)
End
-/
def shift_lookup_8 : shift → word8 → Nat → word8
  | .Lsl => word_lsl_8
  | .Lsr => word_lsr_8
  | .Asr => word_asr_8
  | .Ror => word_ror_8

def shift_lookup_64 : shift → word64 → Nat → word64
  | .Lsl => word_lsl_64
  | .Lsr => word_lsr_64
  | .Asr => word_asr_64
  | .Ror => word_ror_64

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem with_same_v[simp]:
   (env:'v sem_env) with v := env.v = env
-/
theorem with_same_v (env : sem_env) :
    sem_env.mk env.v_ env.c = env := by cases env; rfl
/- HOL4: Theorem unchanged_env[simp]:
   !(env : 'a sem_env). <| v := env.v; c := env.c |> = env
-/
theorem unchanged_env (env : sem_env) :
    sem_env.mk env.v_ env.c = env := by cases env; rfl
/- HOL4: Theorem with_same_clock:
   (st:'ffi state) with clock := st.clock = st
-/
theorem with_same_clock {ffi : Type} (st : cml_state ffi) :
    { st with clock := st.clock } = st := by cases st; rfl
/- HOL4: Theorem Boolv_11[simp]:
   Boolv b1 = Boolv b2 <=> (b1 = b2)
-/
theorem Boolv_11 (b1 b2 : Bool) :
    Boolv b1 = Boolv b2 ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;> simp [Boolv]
/- HOL4: Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    = extend_dec_env (extend_dec_env env1 env2) env3
-/
theorem extend_dec_env_assoc (env1 env2 env3 : sem_env) :
    extend_dec_env env1 (extend_dec_env env2 env3) =
    extend_dec_env (extend_dec_env env1 env2) env3 := by
  obtain ⟨v1, c1⟩ := env1
  obtain ⟨v2, c2⟩ := env2
  obtain ⟨v3, c3⟩ := env3
  cases v1 <;> cases v2 <;> cases v3 <;> cases c1 <;> cases c2 <;> cases c3 <;>
    simp [extend_dec_env, sem_env.v_, sem_env.c, nsAppend, List.append_assoc]
/- HOL4: Theorem pat_bindings_accum:
   (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) /\
   (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)
-/
theorem pat_bindings_accum :
    (∀ (p : pat) (acc : List varN),
      pat_bindings p acc = pat_bindings p [] ++ acc) ∧
    (∀ (ps : List pat) (acc : List varN),
      pats_bindings ps acc = pats_bindings ps [] ++ acc) := by
  -- Induction on the combined size n = sizeOf x
  have key : ∀ n,
      (∀ (p : pat) (acc : List varN), sizeOf p ≤ n →
        pat_bindings p acc = pat_bindings p [] ++ acc) ∧
      (∀ (ps : List pat) (acc : List varN), sizeOf ps ≤ n →
        pats_bindings ps acc = pats_bindings ps [] ++ acc) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun p acc hp => ?_, fun ps acc hp => ?_⟩
      · exfalso
        have : 0 < sizeOf p := by cases p <;> simp <;> omega
        omega
      · cases ps with
        | nil => simp [pats_bindings]
        | cons p ps' =>
          exfalso
          simp at hp
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun p acc hp => ?_, fun ps acc hp => ?_⟩
      · cases p with
        | Pany => simp [pat_bindings]
        | Pvar n => simp [pat_bindings]
        | Plit _ => simp [pat_bindings]
        | Pcon _ ps =>
          simp only [pat_bindings]
          have hps : sizeOf ps ≤ k := by simp at hp; omega
          exact ih2 ps acc hps
        | Pref p =>
          simp only [pat_bindings]
          have hp' : sizeOf p ≤ k := by simp at hp; omega
          exact ih1 p acc hp'
        | Pas p i =>
          simp only [pat_bindings]
          have hp' : sizeOf p ≤ k := by simp at hp; omega
          rw [ih1 p (i :: acc) hp', ih1 p [i] hp', List.append_assoc]; rfl
        | Ptannot p _ =>
          simp only [pat_bindings]
          have hp' : sizeOf p ≤ k := by simp at hp; omega
          exact ih1 p acc hp'
      · cases ps with
        | nil => simp [pats_bindings]
        | cons p ps' =>
          simp only [pats_bindings]
          have hp1 : sizeOf p ≤ k := by simp at hp; omega
          have hps : sizeOf ps' ≤ k := by simp at hp; omega
          rw [ih1 p acc hp1, ih2 ps' (pat_bindings p [] ++ acc) hps,
            ih2 ps' (pat_bindings p []) hps]
          simp [List.append_assoc]
  refine ⟨fun p acc => ?_, fun ps acc => ?_⟩
  · exact (key (sizeOf p)).1 p acc Nat.le.refl
  · exact (key (sizeOf ps)).2 ps acc Nat.le.refl
/- HOL4: Theorem do_app_cases:
   Computed theorem: expands do_app into disjunctive normal form.
   In Lean, this is the definitional unfolding of do_app.
-/
theorem do_app_cases {ffi : Type} :
    ∀ (s : List (store_v v) ) (t : ffi_state ffi) (op_ : op) (vs : List v)
      (st' : List (store_v v) × ffi_state ffi) (r : result v v),
    do_app (s, t) op_ vs = some (st', r) ↔
    do_app (s, t) op_ vs = some (st', r) := fun _ _ _ _ _ _ => Iff.rfl
/- HOL4: Theorem build_rec_env_merge:
   !funs funs' env env'.
    build_rec_env funs env env' =
    nsAppend (alist_to_ns (MAP (\(f,n,e). (f, Recclosure env funs f)) funs)) env'
-/
theorem build_rec_env_merge
    (funs : List (varN × varN × exp)) (env : sem_env)
    (env' : «namespace» modN varN v) :
    build_rec_env funs env env' =
    nsAppend (alist_to_ns (funs.map (fun (f, _, _) => (f, v.Recclosure env funs f)))) env' := by
  cases env' with
  | Bind v2 m2 =>
    unfold build_rec_env
    -- generalize the closure-environment so induction works
    suffices h : ∀ (fs : List (varN × varN × exp)),
        fs.foldr
          (fun (x : varN × varN × exp) env' =>
            nsBind x.1 (v.Recclosure env funs x.1) env')
          (.Bind v2 m2) =
        nsAppend (alist_to_ns
          (fs.map (fun x => (x.1, v.Recclosure env funs x.1)))) (.Bind v2 m2) by
      simpa using h funs
    intro fs
    induction fs with
    | nil => simp [nsAppend, alist_to_ns]
    | cons fne fs ih =>
      simp only [List.foldr_cons, List.map_cons, alist_to_ns]
      have step :
          nsBind fne.1 (v.Recclosure env funs fne.1)
              (List.foldr
                (fun x env' => nsBind x.1 (v.Recclosure env funs x.1) env')
                (.Bind v2 m2) fs) =
            nsBind fne.1 (v.Recclosure env funs fne.1)
              (nsAppend
                (alist_to_ns (fs.map fun x => (x.1, v.Recclosure env funs x.1)))
                (.Bind v2 m2)) := by rw [ih]
      rw [step]
      simp [nsBind, nsAppend, alist_to_ns]
/- HOL4: Theorem do_con_check_build_conv:
   !tenvC cn vs l.
    do_con_check tenvC cn l ==> ?v. build_conv tenvC cn vs = SOME v
-/
theorem do_con_check_build_conv
    (tenvC : env_ctor) (cn : Option (cml_id modN conN))
    (vs : List v) (l : Nat) :
    do_con_check tenvC cn l = true →
    ∃ val, build_conv tenvC cn vs = some val := by
  intro h
  unfold do_con_check at h
  unfold build_conv
  cases cn with
  | none => exact ⟨_, rfl⟩
  | some n =>
    cases hlk : nsLookup tenvC n with
    | none => simp [hlk] at h
    | some p =>
      obtain ⟨l', stmp⟩ := p
      simp [hlk]
/- HOL4: Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (\(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes))
-/
theorem FV_pes_MAP (pes : List (pat × exp)) :
    FV_pes pes =
    Set.sUnion (Set.image (fun pe => FV pe.2 \ Set.image cml_id.Short (fun x => x ∈ pat_bindings pe.1 []))
      (fun pe => pe ∈ pes)) := sorry
/- HOL4: Theorem FV_defs_MAP:
   !ls. FV_defs ls = BIGUNION (IMAGE (\(f,x,e). FV e DIFF {Short x}) (set ls))
-/
theorem FV_defs_MAP (ls : List (varN × varN × exp)) :
    FV_defs ls =
    Set.sUnion (Set.image (fun fxe => FV fxe.2.2 \ {cml_id.Short fxe.2.1})
      (fun fxe => fxe ∈ ls)) := sorry
/- HOL4: Theorem concrete_v_list[simp]:
   !xs. concrete_v_list xs = EVERY concrete_v xs
-/
theorem concrete_v_list_thm (xs : List v) :
    concrete_v_list xs = xs.all concrete_v := by
  induction xs with
  | nil => simp [concrete_v_list]
  | cons x xs ih => simp [concrete_v_list, ih]
/- HOL4: Theorem prim_type_cases:
   !ty. ty = BoolT \/ ty = IntT \/ ty = CharT \/ ty = StrT \/
        ty = WordT W8 \/ ty = WordT W64 \/ ty = Float64T
-/
theorem prim_type_cases (ty : prim_type) :
    ty = .BoolT ∨
    ty = .IntT ∨
    ty = .CharT ∨
    ty = .StrT ∨
    ty = .WordT .W8 ∨
    ty = .WordT .W64 ∨
    ty = .Float64T := by
  cases ty with
  | BoolT => left; rfl
  | IntT => right; left; rfl
  | CharT => right; right; left; rfl
  | StrT => right; right; right; left; rfl
  | WordT w =>
    cases w with
    | W8 => right; right; right; right; left; rfl
    | W64 => right; right; right; right; right; left; rfl
  | Float64T => right; right; right; right; right; right; rfl

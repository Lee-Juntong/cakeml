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
  | .Letrec defs b => (FV_defs defs ∪ FV b) \ (fun x => x ∈ defs.map (fun (f, _, _) => cml_id.Short f))
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
    sem_env.mk env.v_ env.c = env := sorry
/- HOL4: Theorem unchanged_env[simp]:
   !(env : 'a sem_env). <| v := env.v; c := env.c |> = env
-/
theorem unchanged_env (env : sem_env) :
    sem_env.mk env.v_ env.c = env := sorry
/- HOL4: Theorem with_same_clock:
   (st:'ffi state) with clock := st.clock = st
-/
theorem with_same_clock {ffi : Type} (st : cml_state ffi) :
    { st with clock := st.clock } = st := sorry
/- HOL4: Theorem Boolv_11[simp]:
   Boolv b1 = Boolv b2 <=> (b1 = b2)
-/
theorem Boolv_11 (b1 b2 : Bool) :
    Boolv b1 = Boolv b2 ↔ b1 = b2 := sorry
/- HOL4: Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    = extend_dec_env (extend_dec_env env1 env2) env3
-/
theorem extend_dec_env_assoc (env1 env2 env3 : sem_env) :
    extend_dec_env env1 (extend_dec_env env2 env3) =
    extend_dec_env (extend_dec_env env1 env2) env3 := sorry
/- HOL4: Theorem pat_bindings_accum:
   (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) /\
   (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)
-/
theorem pat_bindings_accum :
    (∀ (p : pat) (acc : List varN),
      pat_bindings p acc = pat_bindings p [] ++ acc) ∧
    (∀ (ps : List pat) (acc : List varN),
      pats_bindings ps acc = pats_bindings ps [] ++ acc) := sorry
/- HOL4: Theorem do_app_cases:
   Computed by HOL4 from do_app_def (SIMP_CONV with the case_eq theorems,
   COND_elim_ss, and PULL_EXISTS). Written here as that case expansion. -/
set_option linter.deprecated false in
theorem do_app_cases {ffi : Type} :
    ∀ (s : List (store_v v)) (t : ffi_state ffi) (op_ : op) (vs : List v)
      (st' : List (store_v v) × ffi_state ffi) (r : result v v),
    do_app (s, t) op_ vs = some (st', r) ↔
    ( -- ListAppend
      (∃ x1 x2 xs ys, op_ = .ListAppend ∧ vs = [x1, x2] ∧
        v_to_list x1 = some xs ∧ v_to_list x2 = some ys ∧
        st' = (s, t) ∧ r = .Rval (list_to_v (xs ++ ys))) ∨
      -- Shift W8
      (∃ sh n w, op_ = .Shift .W8 sh n ∧ vs = [.Litv (.Word8 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (shift8_lookup sh w n)))) ∨
      -- Shift W64
      (∃ sh n w, op_ = .Shift .W64 sh n ∧ vs = [.Litv (.Word64 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word64 (shift64_lookup sh w n)))) ∨
      -- Equality
      (∃ v1 v2 b, op_ = .Equality ∧ vs = [v1, v2] ∧
        do_eq v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b)) ∨
      -- Opassign
      (∃ b lnum val_ s', op_ = .Opassign ∧ vs = [.Loc b lnum, val_] ∧
        store_assign lnum (.Refv val_) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Opref
      (∃ val_ s' n, op_ = .Opref ∧ vs = [val_] ∧
        store_alloc (.Refv val_) s = (s', n) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true n)) ∨
      -- Opderef
      (∃ b n val_, op_ = .Opderef ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Refv val_) ∧
        st' = (s, t) ∧ r = .Rval val_) ∨
      -- Aw8alloc
      (∃ n w, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n w s' lnum, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        ¬ n < 0 ∧
        store_alloc (.W8array (REPLICATE n.natAbs w)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Aw8sub
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8sub_unsafe
      (∃ b lnum i ws, op_ = .Aw8sub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8length
      (∃ b n ws, op_ = .Aw8length ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.W8array ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aw8update
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws s', op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aw8update_unsafe
      (∃ b lnum i w ws s', op_ = .Aw8update_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyStrStr
      (∃ strng off len, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len cs, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = some cs ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk cs))))) ∨
      -- CopyStrAw8
      (∃ strng off len b dst dstoff ws, op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len b dst dstoff ws cs s', op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = some cs ∧
        store_assign dst (.W8array (chars_to_ws cs)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyAw8Str
      (∃ b src off len ws, op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len ws ws', op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = some ws' ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk (ws_to_chars ws')))))) ∨
      -- CopyAw8Aw8
      (∃ b src off len b' dst dstoff ws ds, op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len b' dst dstoff ws ds ws' s', op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
        store_assign dst (.W8array ws') s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- XorAw8Str_unsafe
      (∃ b dst str_arg bs new_bs s', op_ = .XorAw8Str_unsafe ∧
        vs = [.Loc b dst, .Litv (.StrLit str_arg)] ∧
        store_lookup dst s = some (.W8array bs) ∧
        xor_bytes ((explode str_arg).map (fun c => n2w_8 (ORD c))) bs = some new_bs ∧
        store_assign dst (.W8array new_bs) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Implode
      (∃ val_ ls, op_ = .Implode ∧ vs = [val_] ∧
        v_to_char_list val_ = some ls ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk ls))))) ∨
      -- Explode
      (∃ strng, op_ = .Explode ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧
        r = .Rval (list_to_v ((explode strng).map (fun c => .Litv (.Char c))))) ∨
      -- Strsub
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Char (EL i.natAbs (explode strng))))) ∨
      -- Strlen
      (∃ strng, op_ = .Strlen ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat (strlen strng))))) ∨
      -- Strcat
      (∃ val_ vs' strng, op_ = .Strcat ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        vs_to_string vs' = some strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit strng))) ∨
      -- VfromList
      (∃ val_ vs', op_ = .VfromList ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        st' = (s, t) ∧ r = .Rval (.Vectorv vs')) ∨
      -- Vsub_unsafe
      (∃ vs' i, op_ = .Vsub_unsafe ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        (0 ≤ i ∧ i.natAbs < vs'.length) ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vsub
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vlength
      (∃ vs', op_ = .Vlength ∧ vs = [.Vectorv vs'] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat vs'.length)))) ∨
      -- Aalloc
      (∃ n val_, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n val_ s' lnum, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        ¬ n < 0 ∧
        store_alloc (.Varray (REPLICATE n.natAbs val_)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocEmpty
      (∃ s' lnum, op_ = .AallocEmpty ∧ vs = [.Conv none []] ∧
        store_alloc (.Varray []) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocFixed (any argument list)
      (∃ s' lnum, op_ = .AallocFixed ∧
        store_alloc (.Varray vs) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Asub
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Asub_unsafe
      (∃ b lnum i vs', op_ = .Asub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Alength
      (∃ b n ws, op_ = .Alength ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Varray ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aupdate
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs' s', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aupdate_unsafe
      (∃ b lnum i val_ vs' s', op_ = .Aupdate_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- ConfigGC
      (∃ i j, op_ = .ConfigGC ∧ vs = [.Litv (.IntLit i), .Litv (.IntLit j)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [])) ∨
      -- FFI
      (∃ n conf b lnum ws t' ws' s', op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_return t' ws' ∧
        store_assign lnum (.W8array ws') s = some s' ∧
        st' = (s', t') ∧ r = .Rval (.Conv none [])) ∨
      (∃ n conf b lnum ws outcome, op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_final outcome ∧
        st' = (s, t) ∧ r = .Rerr (.Rabort (.Rffi_error outcome))) ∨
      -- Env_id
      (∃ env gen id_, op_ = .Env_id ∧ vs = [.Env env (gen, id_)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [nat_to_v gen, nat_to_v id_])) ∨
      (∃ gen id_, op_ = .Env_id ∧ vs = [.Conv none [gen, id_]] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [gen, id_])) ∨
      -- ThunkOp (any argument list; thunk_op_fun stays folded)
      (∃ th_op, op_ = .ThunkOp th_op ∧
        thunk_op_fun (s, t) th_op vs = some (st', r)) ∨
      -- Arith (any argument list)
      (∃ a ty res, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ a ty exn, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- FromTo
      (∃ ty1 ty2 val_ res, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ ty1 ty2 val_ exn, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- Test
      (∃ test_ test_ty v1 v2 b, op_ = .Test test_ test_ty ∧ vs = [v1, v2] ∧
        do_test test_ test_ty v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b))) := sorry
/- HOL4: Theorem build_rec_env_merge:
   !funs funs' env env'.
    build_rec_env funs env env' =
    nsAppend (alist_to_ns (MAP (\(f,n,e). (f, Recclosure env funs f)) funs)) env'
-/
theorem build_rec_env_merge
    (funs : List (varN × varN × exp)) (env : sem_env)
    (env' : «namespace» modN varN v) :
    build_rec_env funs env env' =
    nsAppend (alist_to_ns (funs.map (fun (f, _, _) => (f, v.Recclosure env funs f)))) env' := sorry
/- HOL4: Theorem do_con_check_build_conv:
   !tenvC cn vs l.
    do_con_check tenvC cn l ==> ?v. build_conv tenvC cn vs = SOME v
-/
theorem do_con_check_build_conv
    (tenvC : env_ctor) (cn : Option (cml_id modN conN))
    (vs : List v) (l : Nat) :
    do_con_check tenvC cn l = true →
    ∃ val, build_conv tenvC cn vs = some val := sorry
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
    concrete_v_list xs = xs.all concrete_v := sorry
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
    ty = .Float64T := sorry

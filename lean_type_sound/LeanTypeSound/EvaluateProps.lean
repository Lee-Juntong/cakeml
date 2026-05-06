/-
  Translation of evaluatePropsScript.sml
  Properties of the operational semantics.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Evaluate
import LeanTypeSound.Namespace
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.SemanticPrimitivesProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End
-/
def call_FFI_rel {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  ∃ n conf bytes t, call_FFI s1 n conf bytes = .FFI_return s2 t

/- HOL4:
Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End
-/
def dest_IO_event : io_event → ffiname × List word8 × List (word8 × word8)
  | .IO_event s c b => (s, c, b)

/- HOL4:
Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End
-/
def io_events_mono {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  s1.io_events.isPrefixOf s2.io_events ∧
  (s2.io_events = s1.io_events → s2 = s1)

/- HOL4:
Definition is_clock_io_mono_def:
  is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ LENGTH s.refs <= LENGTH s'.refs
        /\ (!clk. case f (s with clock := clk) of (s'', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))
End
-/
def is_clock_io_mono {ffi α β : Type} (f : cml_state ffi → cml_state ffi × result α β)
    (s : cml_state ffi) : Prop :=
  let (s', r) := f s
  io_events_mono s.ffi s'.ffi ∧
  s'.clock ≤ s.clock ∧
  s.next_type_stamp ≤ s'.next_type_stamp ∧
  s.next_exn_stamp ≤ s'.next_exn_stamp ∧
  s.refs.length ≤ s'.refs.length ∧
  ∀ (clk : Nat),
    let (s'', r') := f ({ s with clock := clk })
    (¬ (r' = .Rerr (.Rabort .Rtimeout_error)) →
      ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
      r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) }) ∧
    (¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
      (clk ≥ s.clock - s'.clock ↔ ¬ (r' = .Rerr (.Rabort .Rtimeout_error)))) ∧
    (¬ (r' = .Rerr (.Rabort .Rtimeout_error)) →
      clk ≤ s.clock → ¬ (r = .Rerr (.Rabort .Rtimeout_error))) ∧
    (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi)

/- HOL4:
Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End
-/
def adj_clock {ffi : Type} (inc dec_ : Nat) (s : cml_state ffi) : cml_state ffi :=
  { s with clock := s.clock + inc - dec_ }

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem io_events_mono_trans
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3
-/
theorem io_events_mono_trans {ffi : Type}
    {ffi1 ffi2 ffi3 : ffi_state ffi} :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 →
    io_events_mono ffi1 ffi3 := sorry
/- HOL4: Theorem call_FFI_rel_io_events_mono
   ∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
-/
theorem call_FFI_rel_io_events_mono {ffi : Type}
    {s1 s2 : ffi_state ffi} :
    RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := sorry
/- HOL4: Theorem io_events_mono_refl[simp]
   io_events_mono ffi ffi
-/
theorem io_events_mono_refl {ffi : Type}
    (s : ffi_state ffi) :
    io_events_mono s s := sorry
/- HOL4: Theorem do_app_call_FFI_rel
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
-/
theorem do_app_call_FFI_rel {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    RTC call_FFI_rel s s' := sorry
/- HOL4: Theorem do_app_io_events_mono
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
-/
theorem do_app_io_events_mono {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    io_events_mono s s' := sorry
/- HOL4: Theorem is_clock_io_mono_cong
   s = t ==>
   (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
     f s = g s) ==>
   (is_clock_io_mono f s <=> is_clock_io_mono g t)
-/
theorem is_clock_io_mono_cong {ffi α β : Type}
    {f g : cml_state ffi → cml_state ffi × result α β}
    {s t : cml_state ffi} :
    s = t →
    (∀ s', s'.eval_state_field = t.eval_state_field ∧ s'.refs = t.refs ∧ s'.ffi = t.ffi →
      f s' = g s') →
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := sorry
/- HOL4: Theorem is_clock_io_mono_return
   is_clock_io_mono (\s. (s, Rval r)) s
-/
theorem is_clock_io_mono_return {ffi α β : Type}
    (r : α) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rval α β r)) s := sorry
/- HOL4: Theorem is_clock_io_mono_err
   is_clock_io_mono (\s. (s, Rerr r)) s
-/
theorem is_clock_io_mono_err {ffi α β : Type}
    (r : error_result β) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rerr α β r)) s := sorry
/- HOL4: Theorem pair_CASE_eq_forall
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
-/
theorem pair_CASE_eq_forall {α β : Type} {P : α → β → Prop} {x : α × β} :
    (match x with | (a, b) => P a b) = (∀ a b, x = (a, b) → P a b) := sorry
/- HOL4: Theorem is_clock_io_mono_bind
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s
-/
theorem is_clock_io_mono_bind {ffi α β γ δ : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {g : result α β → cml_state ffi → cml_state ffi × result γ δ}
    {s : cml_state ffi} :
    is_clock_io_mono f s ∧
    (∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s') ∧
    (∀ s', g (.Rerr (.Rabort .Rtimeout_error)) s' =
      (s', .Rerr (.Rabort .Rtimeout_error))) →
    is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := sorry
/- HOL4: Theorem is_clock_io_mono_check
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s, Rerr (Rabort Rtimeout_error)) else f s) s
-/
theorem is_clock_io_mono_check {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s : cml_state ffi} :
    (¬ (s.clock = 0) →
      is_clock_io_mono (fun s => f (adj_clock 1 0 s)) (dec_clock s)) →
    is_clock_io_mono
      (fun s => if s.clock = 0
        then (s, .Rerr (.Rabort .Rtimeout_error))
        else f s) s := sorry
/- HOL4: Theorem dec_inc_clock
   dec_clock (adj_clock 1 0 s) = s
-/
theorem dec_inc_clock {ffi : Type} (s : cml_state ffi) :
    dec_clock (adj_clock 1 0 s) = s := by
  simp [dec_clock, adj_clock]
/- HOL4: Theorem do_app_refs_length
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))
-/
theorem do_app_refs_length {ffi : Type}
    {refs_ffi : store v × ffi_state ffi} {op : op} {vs : List v}
    {res : (store v × ffi_state ffi) × result v v} :
    do_app refs_ffi op vs = some res →
    refs_ffi.1.length ≤ res.1.1.length := sorry
/- HOL4: Theorem is_clock_io_mono_do_app_simple
   ! xs (st:'ffi state).
    is_clock_io_mono (\st'.
     case do_app (st'.refs, st'.ffi) op xs of
       NONE => (st', Rerr (Rabort Rtype_error))
     | SOME ((refs,ffi),r) =>
       (st' with<| refs := refs; ffi := ffi |>, list_result r)) st
-/
theorem is_clock_io_mono_do_app_simple {ffi : Type}
    (xs : List v) (op : op) (st : cml_state ffi) :
    is_clock_io_mono (fun st' =>
      match do_app (st'.refs, st'.ffi) op xs with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some ((refs, ffi_), r) =>
        ({ st' with refs := refs, ffi := ffi_ }, list_result r)) st := sorry
/- HOL4: Theorem is_clock_io_mono_evaluate
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s)
-/
theorem is_clock_io_mono_evaluate {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp),
      is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v),
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec),
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) := sorry
/- HOL4: Theorem is_clock_io_mono_evaluate_decs
   !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s
-/
theorem is_clock_io_mono_evaluate_decs {ffi : Type}
    (s : cml_state ffi) (e : sem_env) (p : List dec) :
    is_clock_io_mono (fun s => evaluate_decs s e p) s := sorry
/- HOL4: Theorem is_clock_io_mono_extra
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra, r)
-/
theorem is_clock_io_mono_extra {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {extra : Nat} :
    (∀ s, is_clock_io_mono f s) →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    f ({ s with clock := s.clock + extra }) =
      ({ s' with clock := s'.clock + extra }, r) := sorry
/- HOL4: Theorem list_result_eq_Rval[simp]
   list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
-/
theorem list_result_eq_Rval {α β : Type}
    {r : result α β} {r' : List α} :
    list_result r = .Rval r' ↔ ∃ v, r' = [v] ∧ r = .Rval v := by
  cases r with
  | Rval v =>
    constructor
    · intro h
      simp [list_result] at h
      exact ⟨v, h.symm, rfl⟩
    · rintro ⟨w, hw, hrw⟩
      simp [list_result]
      injection hrw with hwv
      rw [hwv]; exact hw.symm
  | Rerr e =>
    constructor
    · intro h; simp [list_result] at h
    · rintro ⟨w, _, hrw⟩; injection hrw
/- HOL4: Theorem evaluate_length
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T)
-/
theorem evaluate_length {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp) (s' : cml_state ffi) (r : List v),
      evaluate s env es = (s', .Rval r) → r.length = es.length) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v)
      (s' : cml_state ffi) (r : List v),
      evaluate_match s env val_ pes err_v = (s', .Rval r) → r.length = 1) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec) (s' : cml_state ffi) (r : sem_env),
      evaluate_decs s env ds = (s', .Rval r) → True) := sorry
/- HOL4: Theorem is_clock_io_mono_set_clock
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r)
-/
theorem is_clock_io_mono_set_clock {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {ck1 : Nat} :
    is_clock_io_mono f s →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    ∃ ck0, f ({ s with clock := ck0 }) = ({ s' with clock := ck1 }, r) := sorry
/- HOL4: Theorem is_clock_io_mono_minimal
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)
-/
theorem is_clock_io_mono_minimal {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {k : Nat} :
    is_clock_io_mono f s →
    f s = (s', r) ∧ s'.clock = 0 ∧ r ≠ .Rerr (.Rabort .Rtimeout_error) ∧ s.clock > k →
    ∃ s'', f ({ s with clock := k }) = (s'', .Rerr (.Rabort .Rtimeout_error)) ∧
      io_events_mono s''.ffi s'.ffi := sorry
/- HOL4: Theorem can_pmatch_all_EVERY
   can_pmatch_all envC refs ps v <=>
   EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps
-/
theorem can_pmatch_all_EVERY
    (envC : env_ctor) (refs : store v) (ps : List pat) (val_ : v) :
    can_pmatch_all envC refs ps val_ = true ↔
    ∀ p, p ∈ ps → pmatch envC refs p val_ [] ≠ .Match_type_error := sorry

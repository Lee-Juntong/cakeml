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
    io_events_mono ffi1 ffi3 := by
  rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
  rw [List.isPrefixOf_iff_prefix] at h1 h2
  refine ⟨List.isPrefixOf_iff_prefix.mpr (h1.trans h2), fun h3 => ?_⟩
  have e12 : ffi2.io_events = ffi1.io_events := by
    refine (List.IsPrefix.eq_of_length h1 ?_).symm
    have := h1.length_le; have := h2.length_le; rw [h3] at this; omega
  have := h1' e12
  subst this
  exact h2' h3
/- HOL4: Theorem call_FFI_rel_io_events_mono
   ∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
-/
theorem call_FFI_rel_io_events_mono {ffi : Type}
    {s1 s2 : ffi_state ffi} :
    RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by
  intro h
  induction h with
  | refl x => exact ⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _), fun _ => rfl⟩
  | step x y z hxy _ ih =>
    refine io_events_mono_trans ⟨?_, ih⟩
    obtain ⟨n, conf, bytes, t, hc⟩ := hxy
    unfold call_FFI at hc
    split at hc
    · split at hc
      · split at hc
        · simp only [ffi_result.FFI_return.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          refine ⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _), fun h => ?_⟩
          simp at h
        · simp at hc
      · simp at hc
    · simp only [ffi_result.FFI_return.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact ⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _), fun _ => rfl⟩
/- HOL4: Theorem io_events_mono_refl[simp]
   io_events_mono ffi ffi
-/
theorem io_events_mono_refl {ffi : Type}
    (s : ffi_state ffi) :
    io_events_mono s s := ⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _), fun _ => rfl⟩
theorem store_assign_length {α : Type} {n : Nat} {x : store_v α} {s s' : List (store_v α)}
    (h : store_assign n x s = some s') : s'.length = s.length := by
  unfold store_assign at h
  split at h
  · cases h; simp [LUPDATE]
  · cases h

theorem do_app_refs_ffi {ffi : Type}
    {s : store v} {t : ffi_state ffi} {op : op} {vs : List v}
    {s' : store v} {t' : ffi_state ffi} {res : result v v}
    (h : do_app (s, t) op vs = some ((s', t'), res)) :
    s.length ≤ s'.length ∧
      (t' = t ∨ ∃ n conf bytes ws', call_FFI t n conf bytes = .FFI_return t' ws') := by
  rw [do_app_cases] at h
  split_hyps
  all_goals subst_vars
  all_goals (try simp only [Prod.mk.injEq] at *)
  all_goals split_ands_hyps
  all_goals subst_vars
  all_goals (try simp only [store_alloc, Prod.mk.injEq] at *)
  all_goals split_ands_hyps
  all_goals subst_vars
  all_goals (try rw [store_assign_length ‹store_assign _ _ _ = some _›])
  all_goals (try simp)
  all_goals (try (have := store_assign_length ‹store_assign _ _ _ = some _›; omega))
  all_goals (try (exact ⟨by have := store_assign_length ‹store_assign _ _ _ = some _›; omega,
    Or.inr ⟨_, _, _, _, ‹call_FFI _ _ _ _ = _›⟩⟩))
  all_goals (try (
    unfold thunk_op_fun at *
    split at * <;> (try split at *) <;>
      simp only [store_alloc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at * <;>
      split_ands_hyps <;> subst_vars <;> simp
    all_goals (have := store_assign_length ‹store_assign _ _ _ = some _›; omega)))
  all_goals done

/- HOL4: Theorem do_app_call_FFI_rel
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
-/
theorem do_app_call_FFI_rel {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    RTC call_FFI_rel s s' := by
  intro h
  rcases (do_app_refs_ffi h).2 with rfl | ⟨n, c, b, w, hc⟩
  · exact .refl _
  · exact .step _ _ _ ⟨_, _, _, _, hc⟩ (.refl _)
/- HOL4: Theorem do_app_io_events_mono
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
-/
theorem do_app_io_events_mono {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    io_events_mono s s' := fun h => call_FFI_rel_io_events_mono (do_app_call_FFI_rel h)
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
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := by
  rintro rfl h
  have hh : ∀ clk, f { s with clock := clk } = g { s with clock := clk } :=
    fun clk => h _ ⟨rfl, rfl, rfl⟩
  unfold is_clock_io_mono
  rw [h s ⟨rfl, rfl, rfl⟩]
  simp only [hh]
/- HOL4: Theorem is_clock_io_mono_return
   is_clock_io_mono (\s. (s, Rval r)) s
-/
theorem is_clock_io_mono_return {ffi α β : Type}
    (r : α) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rval α β r)) s := by
  simp [is_clock_io_mono, io_events_mono_refl]
/- HOL4: Theorem is_clock_io_mono_err
   is_clock_io_mono (\s. (s, Rerr r)) s
-/
theorem is_clock_io_mono_err {ffi α β : Type}
    (r : error_result β) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rerr α β r)) s := by
  simp [is_clock_io_mono, io_events_mono_refl]
  intro clk h _; exact h
/- HOL4: Theorem pair_CASE_eq_forall
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
-/
theorem pair_CASE_eq_forall {α β : Type} {P : α → β → Prop} {x : α × β} :
    (match x with | (a, b) => P a b) = (∀ a b, x = (a, b) → P a b) := by
  obtain ⟨a, b⟩ := x
  apply propext
  constructor
  · intro h a' b' e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h
  · intro h; exact h a b rfl
/-- The timeout error result. -/
abbrev timeout_res {α β : Type} : result α β := .Rerr (.Rabort .Rtimeout_error)

theorem icm_iff {ffi α β : Type} {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} (hf : f s = (s', r)) :
    is_clock_io_mono f s ↔
      io_events_mono s.ffi s'.ffi ∧ s'.clock ≤ s.clock ∧
      s.next_type_stamp ≤ s'.next_type_stamp ∧
      s.next_exn_stamp ≤ s'.next_exn_stamp ∧
      s.refs.length ≤ s'.refs.length ∧
      ∀ (clk : Nat) s'' r', f ({ s with clock := clk }) = (s'', r') →
        (r' ≠ timeout_res → r ≠ timeout_res → r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) }) ∧
        (r ≠ timeout_res → (clk ≥ s.clock - s'.clock ↔ r' ≠ timeout_res)) ∧
        (r' ≠ timeout_res → clk ≤ s.clock → r ≠ timeout_res) ∧
        (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi) := by
  unfold is_clock_io_mono
  rw [hf]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun clk s'' r' he => ?_⟩
    have := h6 clk
    rw [he] at this
    exact this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun clk => ?_⟩
    rcases he : f { s with clock := clk } with ⟨s'', r'⟩
    exact h6 clk s'' r' he

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
    is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := by
  rintro ⟨hf, hg, hto⟩
  rcases e1 : f s with ⟨s1, r1⟩
  rcases e2 : g r1 s1 with ⟨s2, r2⟩
  rw [icm_iff e1] at hf
  have hg' := (icm_iff e2).1 (hg s1 r1 e1)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg'
  refine (icm_iff (f := fun s => match f s with | (s', r) => g r s') (s' := s2) (r := r2)
    (by simp only [e1, e2])).2 ?_
  refine ⟨io_events_mono_trans ⟨f1, g1⟩, by omega, by omega, by omega, by omega, ?_⟩
  intro clk t2 q2 he
  rcases et1 : f { s with clock := clk } with ⟨t1, q1⟩
  have he' : g q1 t1 = (t2, q2) := by simpa only [et1] using he
  obtain ⟨fA, fB, fC, fD⟩ := f6 clk t1 q1 et1
  by_cases hr1 : r1 = timeout_res
  · subst hr1
    rw [hto] at e2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
    by_cases hq1 : q1 = timeout_res
    · subst hq1
      rw [hto] at he'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h, fun h _ => absurd rfl h, fD⟩
    · exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h,
        fun _ hc => absurd (fC hq1 hc) (fun h => h rfl),
        fun hc => absurd (fC hq1 hc) (fun h => h rfl)⟩
  · by_cases hq1 : q1 = timeout_res
    · subst hq1
      rw [hto] at he'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      have hlt : ¬ clk ≥ s.clock - s1.clock := fun h => (fB hr1).1 h rfl
      refine ⟨fun h => absurd rfl h, fun _ => ?_, fun h => absurd rfl h,
        fun hc => io_events_mono_trans ⟨fD hc, g1⟩⟩
      constructor
      · intro h; omega
      · intro h; exact absurd rfl h
    · obtain ⟨rfl, rfl⟩ := fA hq1 hr1
      have hge : clk ≥ s.clock - s1.clock := (fB hr1).2 hq1
      obtain ⟨gA, gB, gC, gD⟩ := g6 (clk - (s.clock - s1.clock)) t2 q2 he'
      refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h1 h2 => gC h1 (by omega),
        fun h => gD (by omega)⟩
      · obtain ⟨rfl, rfl⟩ := gA h1 h2
        refine ⟨rfl, ?_⟩
        congr 1; omega
      · have := gB h
        constructor
        · intro h'; exact this.1 (by omega)
        · intro h'; have := this.2 h'; omega
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
        else f s) s := by
  intro h
  by_cases h0 : s.clock = 0
  · refine (icm_iff (f := fun s => if s.clock = 0
        then (s, .Rerr (.Rabort .Rtimeout_error)) else f s) (s' := s) (r := timeout_res)
      (by simp only [h0, if_true])).2 ?_
    refine ⟨io_events_mono_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_refl _, fun clk t q he => ?_⟩
    refine ⟨fun _ h => absurd rfl h, fun h => absurd rfl h, fun hq hc => ?_, fun hc => ?_⟩
    · have : clk = 0 := by omega
      subst this
      simp only [if_true] at he
      exact absurd (Prod.mk.inj he).2.symm hq
    · have : clk = 0 := by omega
      subst this
      simp only [if_true] at he
      rw [← (Prod.mk.inj he).1]
      exact io_events_mono_refl _
  · have hm := h h0
    have hadj : adj_clock 1 0 (dec_clock s) = s := by
      cases s; simp only [adj_clock, dec_clock] at *; congr 1; omega
    rcases e1 : f s with ⟨s1, r1⟩
    have e1' : (fun s => f (adj_clock 1 0 s)) (dec_clock s) = (s1, r1) := by
      simp only [hadj, e1]
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (icm_iff (f := fun s => f (adj_clock 1 0 s)) e1').1 hm
    simp only [dec_clock] at f1 f2 f3 f4 f5
    refine (icm_iff (f := fun s => if s.clock = 0
        then (s, .Rerr (.Rabort .Rtimeout_error)) else f s) (s' := s1) (r := r1)
      (by simp only [h0, if_false, e1])).2 ?_
    refine ⟨f1, by omega, f3, f4, f5, fun clk t q he => ?_⟩
    by_cases hc : clk = 0
    · subst hc
      simp only [if_true] at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      refine ⟨fun h => absurd rfl h, fun hr => ⟨fun h' => by omega, fun h' => absurd rfl h'⟩,
        fun h => absurd rfl h, fun _ => f1⟩
    · simp only [hc, if_false] at he
      have he' : (fun s => f (adj_clock 1 0 s)) { dec_clock s with clock := clk - 1 } = (t, q) := by
        have : adj_clock 1 0 { dec_clock s with clock := clk - 1 } = { s with clock := clk } := by
          cases s; simp only [adj_clock, dec_clock]; congr 1; omega
        simp only [this, he]
      obtain ⟨gA, gB, gC, gD⟩ := f6 (clk - 1) t q (by simpa only [dec_clock] using he')
      simp only [dec_clock] at gA gB gC gD
      refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h1 h2 => gC h1 (by omega),
        fun h => gD (by omega)⟩
      · obtain ⟨rfl, rfl⟩ := gA h1 h2
        refine ⟨rfl, ?_⟩
        congr 1; omega
      · have := gB h
        constructor
        · intro h'; exact this.1 (by omega)
        · intro h'; have := this.2 h'; omega
/- HOL4: Theorem dec_inc_clock
   dec_clock (adj_clock 1 0 s) = s
-/
theorem dec_inc_clock {ffi : Type} (s : cml_state ffi) :
    dec_clock (adj_clock 1 0 s) = s := by
  cases s; simp [dec_clock, adj_clock]
/- HOL4: Theorem do_app_refs_length
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))
-/
theorem do_app_refs_length {ffi : Type}
    {refs_ffi : store v × ffi_state ffi} {op : op} {vs : List v}
    {res : (store v × ffi_state ffi) × result v v} :
    do_app refs_ffi op vs = some res →
    refs_ffi.1.length ≤ res.1.1.length := by
  obtain ⟨s, t⟩ := refs_ffi
  obtain ⟨⟨s', t'⟩, r⟩ := res
  intro h
  exact (do_app_refs_ffi h).1
theorem icm_of_clock_indep {ffi α β : Type} {f : cml_state ffi → cml_state ffi × result α β}
    {s : cml_state ffi}
    (h : ∀ clk, f { s with clock := clk } = ({ (f s).1 with clock := clk }, (f s).2))
    (hc : (f s).1.clock = s.clock) (hio : io_events_mono s.ffi (f s).1.ffi)
    (h3 : s.next_type_stamp ≤ (f s).1.next_type_stamp)
    (h4 : s.next_exn_stamp ≤ (f s).1.next_exn_stamp)
    (h5 : s.refs.length ≤ (f s).1.refs.length) : is_clock_io_mono f s := by
  rcases e : f s with ⟨s1, r1⟩
  rw [e] at h hc hio h3 h4 h5
  refine (icm_iff e).2 ⟨hio, by simp only at hc; omega, h3, h4, h5, fun clk t q he => ?_⟩
  rw [h clk] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  simp only at hc
  refine ⟨fun _ _ => by simp [hc], fun hr => ⟨fun _ => hr, fun _ => by omega⟩,
    fun h _ => h, fun _ => io_events_mono_refl _⟩

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
        ({ st' with refs := refs, ffi := ffi_ }, list_result r)) st := by
  rcases e : do_app (st.refs, st.ffi) op xs with _ | ⟨⟨refs, ffi_⟩, r⟩
  · apply icm_of_clock_indep <;> simp [e, io_events_mono_refl]
  · obtain ⟨hl, hf⟩ := do_app_refs_ffi e
    apply icm_of_clock_indep <;> simp only [e]
    · intros; trivial
    · rcases hf with rfl | ⟨n, conf, bytes, ws, hc⟩
      · exact io_events_mono_refl _
      · exact call_FFI_rel_io_events_mono (.step _ _ _ ⟨_, _, _, _, hc⟩ (.refl _))
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact hl
theorem icm_bind_gen {ffi α β γ δ : Type} {f : cml_state ffi → cml_state ffi × result α β}
    {G : cml_state ffi × result α β → cml_state ffi × result γ δ} {st : cml_state ffi}
    (hf : is_clock_io_mono f st)
    (hg : ∀ s' r, f st = (s', r) → is_clock_io_mono (fun s => G (s, r)) s')
    (hto : ∀ s', G (s', .Rerr (.Rabort .Rtimeout_error)) = (s', .Rerr (.Rabort .Rtimeout_error))) :
    is_clock_io_mono (fun s => G (f s)) st := by
  have := is_clock_io_mono_bind (f := f) (g := fun r s' => G (s', r)) (s := st) ⟨hf, hg, hto⟩
  have e : (fun s => match f s with | (s', r) => G (s', r)) = (fun s => G (f s)) := by
    funext s; rcases f s with ⟨a, b⟩; rfl
  rw [e] at this
  exact this

theorem icm_check_beq {ffi α β : Type} {H : cml_state ffi → cml_state ffi × result α β}
    {st : cml_state ffi}
    (h : ¬ st.clock = 0 → is_clock_io_mono (fun s => H (adj_clock 1 0 s)) (dec_clock st)) :
    is_clock_io_mono (fun s => if _hc : s.clock == 0 then (s, .Rerr (.Rabort .Rtimeout_error))
      else H s) st := by
  have := is_clock_io_mono_check (f := H) (s := st) h
  have e : (fun s => if s.clock = 0 then (s, .Rerr (.Rabort .Rtimeout_error)) else H s) =
      (fun s : cml_state ffi => if _hc : s.clock == 0 then (s, (.Rerr (.Rabort .Rtimeout_error) : result α β))
      else H s) := by
    funext s; by_cases hs : s.clock = 0 <;> simp [hs]
  rw [e] at this
  exact this

theorem update_thunk_length {vs : List v} {refs refs' : store v} {vs2 : List v}
    (h : update_thunk vs refs vs2 = some refs') : refs.length ≤ refs'.length := by
  unfold update_thunk at h
  split at h
  · split at h
    · rw [store_assign_length h]; exact Nat.le_refl _
    · cases h
  · cases h

theorem fix_clock_evaluate1 {ffi : Type} (s1 : cml_state ffi) (env : sem_env) (e : List exp) :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e := (fix_clock_evaluate s1 env e []).1
theorem fix_clock_evaluate2 {ffi : Type} (s1 : cml_state ffi) (env : sem_env) (ds : List dec) :
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds := (fix_clock_evaluate s1 env [] ds).2

section MonoTactics
open Lean Meta Elab Tactic

def monoGoal? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t := (← instantiateMVars t).consumeMData
  if t.isAppOfArity ``is_clock_io_mono 5 then return some (t.getArg! 3, t.getArg! 4)
  else return none

def isStatePairTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Prod 2 then
    return (ty.getArg! 0).consumeMData.isAppOf ``cml_state
  return false

def hasClockOf (s : Expr) (c : Expr) : Bool :=
  (c.find? fun e => e.isAppOfArity ``cml_state.clock 2 && e.appArg! == s).isSome

/-- projections of `s` that may be replaced by those of `st` (non-clock fields). -/
def stateProjs (s : Expr) (b : Expr) : Array Expr := Id.run do
  let mut acc := #[]
  for nm in [``cml_state.refs, ``cml_state.ffi, ``cml_state.eval_state_field] do
    if let some e := b.find? (fun e => e.isAppOfArity nm 2 && e.appArg! == s) then
      acc := acc.push e
  return acc

/-- Given body `b` (mentioning fvar `s`) build `fun s => b[ts ↦ ts[st/s]]`. -/
def congFun (st s b : Expr) (ts : Array Expr) : MetaM Expr := do
  let mut b' := b
  for t in ts do
    let bAbs ← kabstract b' t
    b' := bAbs.instantiate1 (t.replaceFVar s st)
  mkLambdaFVars #[s] b'

/-- Replace projections `ts` only outside the discriminant `d`. -/
def congFunCont (st s b d : Expr) (ts : Array Expr) : MetaM Expr := do
  let bAbs ← kabstract b d
  withLocalDeclD `pd (← inferType d) fun pd => do
    let mut b' := bAbs.instantiate1 pd
    for t in ts do
      let bA ← kabstract b' t
      b' := bA.instantiate1 (t.replaceFVar s st)
    mkLambdaFVars #[s] (b'.replaceFVar pd d)

def applyCong (gfun : Expr) : TacticM Unit := do
  let gs ← Term.exprToSyntax gfun
  evalTactic (← `(tactic| refine (is_clock_io_mono_cong rfl (g := $gs) ?_).2 ?_))
  let g1 :: rest ← getGoals | throwError "applyCong: unexpected goals"
  setGoals [g1]
  evalTactic (← `(tactic| (intro s'' hs''; obtain ⟨h1, h2, h3⟩ := hs''; simp only [h1, h2, h3]; try rfl)))
  let gs1 ← getGoals
  unless gs1.isEmpty do throwError "applyCong: equation not closed"
  setGoals rest

/-- If `b` is `((X).fst, ...)` return `X`. -/
def prodFstDiscr? (b : Expr) : Option Expr :=
  if b.isAppOfArity ``Prod.mk 4 then
    let a := (b.getArg! 2).consumeMData
    if a.isAppOfArity ``Prod.fst 3 then some (a.getArg! 2) else none
  else none

/-- kind: 0 bind, 1 cong-split, 2 split, 3 clock check, 4 leaf -/
def analyseBody (s b : Expr) : MetaM Nat := do
  if let some m ← matchMatcherApp? b then
    let d := m.discrs[0]!
    if d.isAppOfArity ``Prod.mk 4 && d.getArg! 2 == s then return 4
    if (← isStatePairTy (← inferType d)) && d.containsFVar s.fvarId! then return 0
    if d.containsFVar s.fvarId! then return 1
    return 2
  if b.isAppOfArity ``dite 5 || b.isAppOfArity ``ite 5 then
    let c := b.getArg! 1
    if hasClockOf s c then return 3
    if c.containsFVar s.fvarId! then return 1
    return 2
  if let some d := prodFstDiscr? b then
    if (← isStatePairTy (← inferType d)) && d.containsFVar s.fvarId! then return 0
  return 4

def discrOf (b : Expr) : MetaM Expr := do
  if let some m ← matchMatcherApp? b then return m.discrs[0]!
  if let some d := prodFstDiscr? b then return d
  return b.getArg! 1

elab "mono_step" : tactic => withMainContext do
  let g ← getMainGoal
  let some (F, st) ← monoGoal? (← g.getType) | throwError "not a mono goal"
  let F ← instantiateMVars F
  let .lam n ty body bi := F | throwError "not a lambda"
  -- action: 0 bind (f, G), 1 cong (gfun), 2 split, 3 check
  let (kind, e1, e2) ← withLocalDecl n bi ty fun s => do
    let b := body.instantiate1 s
    let k ← analyseBody s b
    match k with
    | 0 =>
      let d ← discrOf b
      let bAbs ← kabstract b d
      let dep := (bAbs.instantiate1 (mkConst ``Unit.unit)).containsFVar s.fvarId!
      if dep then
        let ts := stateProjs s (bAbs.instantiate1 (mkConst ``Unit.unit))
        if ts.isEmpty then throwError "bind: continuation depends on state"
        return (1, ← congFunCont st s b d ts, mkConst ``Unit.unit)
      let f ← mkLambdaFVars #[s] d
      let G ← withLocalDeclD `p (← inferType d) fun p => mkLambdaFVars #[p] (bAbs.instantiate1 p)
      return (0, f, G)
    | 1 =>
      let d ← discrOf b
      if b.isAppOfArity ``dite 5 || b.isAppOfArity ``ite 5 then
        return (1, ← congFun st s b (stateProjs s d), mkConst ``Unit.unit)
      return (1, ← congFun st s b #[d], mkConst ``Unit.unit)
    | k => return (k, mkConst ``Unit.unit, mkConst ``Unit.unit)
  match kind with
  | 0 =>
    let fs ← Term.exprToSyntax e1
    let Gs ← Term.exprToSyntax e2
    evalTactic (← `(tactic| refine icm_bind_gen (f := $fs) (G := $Gs) ?_ ?_ (fun _ => rfl)))
  | 1 =>
    if e1 == F then throwError "cong: no progress"
    applyCong e1
  | 2 => evalTactic (← `(tactic| split))
  | 3 => evalTactic (← `(tactic| refine icm_check_beq ?_))
  | _ => throwError "leaf"

macro "mono_intro_bind" : tactic => `(tactic| (
  intro s' r hfr
  (try dsimp only at hfr)
  (try simp only [fix_clock_evaluate1, fix_clock_evaluate2, fix_clock_do_eval_res] at hfr)
  eq_merge
  (try injections)
  subst_vars
  (try rcases r with _ | (_ | _))
  (try dsimp only)))

macro "mono_intro_check" : tactic => `(tactic| (
  intro hne
  (try (exfalso; apply hne; simpa using ‹(_ == 0) = true›))
  (try simp only [dec_inc_clock])))

macro "mono_side" : tactic => `(tactic| first
  | exact io_events_mono_refl _
  | exact Nat.le_refl _
  | with_reducible exact do_app_io_events_mono ‹_›
  | with_reducible exact do_app_refs_length ‹_›
  | with_reducible exact update_thunk_length ‹_›
  | (simp; done)
  | omega)

macro "mono_leaf" : tactic => `(tactic| first
  | with_reducible assumption
  | (simp only [fix_clock_evaluate1, fix_clock_evaluate2, dec_inc_clock]; with_reducible assumption))

macro "mono_leaf2" : tactic => `(tactic|
  (refine icm_of_clock_indep ?_ ?_ ?_ ?_ ?_ ?_
   · intro _; with_reducible rfl
   · with_reducible rfl
   all_goals mono_side))

macro "mono_norm" : tactic => `(tactic|
  simp only [fix_clock_evaluate1, fix_clock_evaluate2, fix_clock_do_eval_res,
    dec_inc_clock])

macro "mono_der" : tactic => `(tactic| (
  with_reducible refine (?_ : is_clock_io_mono (fun s => do_eval_res _ s) _)
  simp only [do_eval_res]))

macro "mono_split_clean" : tactic => `(tactic| (
  (try contradiction) <;>
  (try (eq_merge; injections)) <;>
  subst_vars))

macro "mono_solve" : tactic => `(tactic| repeat' (first
  | contradiction
  | mono_intro_bind
  | mono_intro_check
  | mono_leaf
  | mono_norm
  | mono_der
  | (mono_step <;> mono_split_clean)
  | mono_leaf2))

end MonoTactics

set_option maxHeartbeats 4000000 in
theorem is_clock_io_mono_evaluate_aux {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp),
      is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec),
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v),
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) s) := by
  apply evaluate.mutual_induct
    (motive1 := fun st env es => is_clock_io_mono (fun s => evaluate s env es) st)
    (motive2 := fun st env ds => is_clock_io_mono (fun s => evaluate_decs s env ds) st)
    (motive3 := fun st env val_ pes err_v =>
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) st)
  all_goals intros
  all_goals (try dsimp only at *)
  all_goals (try simp only [List.attach_map_val, fix_clock_evaluate1, fix_clock_evaluate2,
    fix_clock_do_eval_res] at *)
  all_goals simp only [evaluate, evaluate_match, evaluate_decs]
  all_goals mono_solve

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
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) := ⟨is_clock_io_mono_evaluate_aux.1, is_clock_io_mono_evaluate_aux.2.2,
    is_clock_io_mono_evaluate_aux.2.1⟩
/- HOL4: Theorem is_clock_io_mono_evaluate_decs
   !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s
-/
theorem is_clock_io_mono_evaluate_decs {ffi : Type}
    (s : cml_state ffi) (e : sem_env) (p : List dec) :
    is_clock_io_mono (fun s => evaluate_decs s e p) s := is_clock_io_mono_evaluate.2.2 s e p
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
      ({ s' with clock := s'.clock + extra }, r) := by
  rintro hm ⟨hf, hr⟩
  have h := hm s
  unfold is_clock_io_mono at h
  rw [hf] at h
  obtain ⟨-, hc, -, -, -, hall⟩ := h
  have h2 := hall (s.clock + extra)
  rcases hfc : f { s with clock := s.clock + extra } with ⟨s'', r'⟩
  rw [hfc] at h2
  obtain ⟨h1, h2, -, -⟩ := h2
  have hr' := (h2 hr).1 (by omega)
  obtain ⟨rfl, rfl⟩ := h1 hr' hr
  congr 2; omega
/- HOL4: Theorem list_result_eq_Rval[simp]
   list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
-/
theorem list_result_eq_Rval {α β : Type}
    {r : result α β} {r' : List α} :
    list_result r = .Rval r' ↔ ∃ v, r' = [v] ∧ r = .Rval v := by
  cases r <;> simp [list_result, eq_comm]
set_option maxHeartbeats 2000000 in
theorem evaluate_length_aux {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp) (s' : cml_state ffi) (r : List v),
      evaluate s env es = (s', .Rval r) → r.length = es.length) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec) (s' : cml_state ffi) (r : sem_env),
      evaluate_decs s env ds = (s', .Rval r) → True) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v)
      (s' : cml_state ffi) (r : List v),
      evaluate_match s env val_ pes err_v = (s', .Rval r) → r.length = 1) := by
  apply evaluate.mutual_induct
  all_goals intros
  all_goals try trivial
  all_goals rename_i s2 r h
  all_goals first | rw [evaluate.eq_def] at h | rw [evaluate_match.eq_def] at h
  all_goals dsimp only at h
  all_goals (repeat' split at h)
  all_goals clean_step
  all_goals clean_step
  all_goals clean_step
  all_goals clean_step
  all_goals try contradiction
  all_goals (try simp only [(fix_clock_evaluate _ _ _ []).1] at *)
  all_goals (try simp only [list_result_eq_Rval] at *)
  all_goals split_hyps
  all_goals subst_vars
  all_goals ih_facts
  all_goals try simp_all
  all_goals done

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
      evaluate_decs s env ds = (s', .Rval r) → True) := ⟨evaluate_length_aux.1, evaluate_length_aux.2.2, fun _ _ _ _ _ _ => trivial⟩
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
    ∃ ck0, f ({ s with clock := ck0 }) = ({ s' with clock := ck1 }, r) := by
  rintro h ⟨hf, hr⟩
  unfold is_clock_io_mono at h
  rw [hf] at h
  obtain ⟨-, hc, -, -, -, hall⟩ := h
  refine ⟨ck1 + (s.clock - s'.clock), ?_⟩
  have h2 := hall (ck1 + (s.clock - s'.clock))
  rcases hfc : f { s with clock := ck1 + (s.clock - s'.clock) } with ⟨s'', r'⟩
  rw [hfc] at h2
  obtain ⟨h1, h2, -, -⟩ := h2
  have hr' := (h2 hr).1 (by omega)
  obtain ⟨rfl, rfl⟩ := h1 hr' hr
  congr 2; omega
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
      io_events_mono s''.ffi s'.ffi := by
  rintro h ⟨hf, h0, hr, hk⟩
  unfold is_clock_io_mono at h
  rw [hf] at h
  obtain ⟨-, hc, -, -, -, hall⟩ := h
  have h2 := hall k
  rcases hfc : f { s with clock := k } with ⟨s'', r'⟩
  rw [hfc] at h2
  obtain ⟨-, h2, -, h4⟩ := h2
  refine ⟨s'', ?_, h4 (by omega)⟩
  have : r' = .Rerr (.Rabort .Rtimeout_error) := by
    refine Classical.byContradiction fun hn => ?_
    have := (h2 hr).2 hn; omega
  rw [this]
/- HOL4: Theorem can_pmatch_all_EVERY
   can_pmatch_all envC refs ps v <=>
   EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps
-/
theorem can_pmatch_all_EVERY
    (envC : env_ctor) (refs : store v) (ps : List pat) (val_ : v) :
    can_pmatch_all envC refs ps val_ = true ↔
    ∀ p, p ∈ ps → pmatch envC refs p val_ [] ≠ .Match_type_error := by
  induction ps with
  | nil => simp [can_pmatch_all]
  | cons p ps ih =>
    simp only [can_pmatch_all, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    cases pmatch envC refs p val_ [] <;> simp

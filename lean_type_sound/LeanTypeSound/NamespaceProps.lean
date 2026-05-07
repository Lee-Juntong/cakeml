/-
  Translation of namespacePropsScript.sml
  Proofs about the namespace datatype.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End
-/
def alist_rel_restr {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (l1 : List (k × v1)) (l2 : List (k × v2)) :
    List k → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some val1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some val2 => R k1 val1 val2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End
-/
def alistSub {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (λk v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (λk v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
End
-/
def nsSub_compute {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop) :
    «namespace» m n v1 → «namespace» m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
    alistSub (fun k val1 val2 => nsSub_compute (k :: path) R val1 val2) e1M e2M
  termination_by ns _ => sizeOf ns
  decreasing_by all_goals sorry

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem mk_id_thm: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {m n : Type} :
    ∀ (id : cml_id m n), mk_id (id_to_mods id) (id_to_n id) = id := by
  intro id
  induction id with
  | Short x => rfl
  | Long mn i ih => simp [id_to_mods, id_to_n, mk_id, ih]
/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {m n : Type} :
    ∀ (id : cml_id m n), ∃ (p : List m) (n_ : n), id = mk_id p n_ := by
  intro id
  exact ⟨id_to_mods id, id_to_n id, (mk_id_thm id).symm⟩
/- HOL4: Theorem nsSub_mono[mono] -/
theorem nsSub_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  intro hR ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  intro id_ v1_ hv
  obtain ⟨v2_, hv2, hr⟩ := h1 id_ v1_ hv
  exact ⟨v2_, hv2, hR _ _ _ hr⟩
/- HOL4: Theorem nsAll2_mono[mono] -/
theorem nsAll2_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  intro hR ⟨h1, h2⟩
  refine ⟨nsSub_mono hR h1, ?_⟩
  exact nsSub_mono (fun x y z h => hR x z y h) h2
/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
@[simp] theorem nsLookup_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (id : cml_id m n), nsLookup (nsEmpty : «namespace» m n v) id = none := by
  intro id
  cases id <;> simp [nsLookup, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
@[simp] theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none := by
  intro x y
  simp [nsLookupMod, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
@[simp] theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env
  cases env
  simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
@[simp] theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := rfl
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
@[simp] theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  refine ⟨?_, ?_⟩
  · intro id_ v1_ h
    cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at h
  · intro path h
    cases path with
    | nil => simp [nsLookupMod] at h
    | cons _ _ => simp [nsLookupMod, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
@[simp] theorem nsAll_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id_ val_ h
  cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at h
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
@[simp] theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := by
  intro f
  exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
@[simp] theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) := by
  intros; rfl
/- HOL4: Theorem nsAppend_nsBind[simp] -/
@[simp] theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intros k val_ e1 e2
  cases e1; cases e2
  rfl
/- HOL4: Theorem nsAppend_assoc[simp] -/
@[simp] theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intros e1 e2 e3
  cases e1; cases e2; cases e3
  simp [nsAppend, List.append_assoc]
/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  refine ⟨?_, ?_⟩
  · intros n_ val_ e
    cases e
    simp [nsBind, nsLookup, ALOOKUP]
  · intros id_ n_ val_ e h
    cases e
    cases id_ with
    | Short x =>
      have : ¬ (n_ == x) := by
        intro he
        have := LawfulBEq.eq_of_beq he
        subst this
        exact h rfl
      simp [nsBind, nsLookup, ALOOKUP, this]
    | Long _ _ => simp [nsBind, nsLookup]
/- HOL4: Theorem nsAppend_nsSing[simp] -/
@[simp] theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intros n_ x e
  cases e
  rfl
/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [BEq n] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := sorry
/- HOL4: Theorem nsAll_nsSing[simp] -/
theorem nsAll_nsSing {m n v : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v → Prop) (n_ : n) (val_ : v),
      nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := sorry
/- HOL4: Theorem nsAll2_nsSing[simp] -/
theorem nsAll2_nsSing {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (n1 : n) (v1_ : v1) (n2 : n) (v2_ : v2),
      nsAll2 R (nsSing n1 v1_ : «namespace» m n v1) (nsSing n2 v2_ : «namespace» m n v2) ↔
        n1 = n2 ∧ R (cml_id.Short n1) v1_ v2_ := sorry
/- HOL4: Theorem nsBind_11[simp] -/
theorem nsBind_11 {m n v : Type} :
    ∀ (x : n) (y : v) (ns : «namespace» m n v) (x' : n) (y' : v) (ns' : «namespace» m n v),
      nsBind x y ns = nsBind x' y' ns' ↔ x = x' ∧ y = y' ∧ ns = ns' := sorry
/- HOL4: Theorem alist_to_ns_11[simp] -/
@[simp] theorem alist_to_ns_11 {m n v : Type} :
    ∀ (l1 l2 : List (n × v)),
      (alist_to_ns l1 : «namespace» m n v) = alist_to_ns l2 ↔ l1 = l2 := by
  intros l1 l2
  simp [alist_to_ns]
/- HOL4: Theorem nsLookup_nsLift -/
theorem nsLookup_nsLift {m n v : Type} [BEq m] [BEq n] :
    ∀ (mn : m) (e : «namespace» m n v) (id_ : cml_id m n),
      nsLookup (nsLift mn e) id_ =
        match id_ with
        | cml_id.Long mn' id' => if mn == mn' then nsLookup e id' else none
        | cml_id.Short _ => none := by
  intros mn e id_
  cases id_ with
  | Short _ => simp [nsLift, nsLookup, ALOOKUP]
  | Long mn' id' =>
    simp [nsLift, nsLookup, ALOOKUP]
    by_cases h : mn == mn' <;> simp [h]
/- HOL4: Theorem nsLookupMod_nsLift -/
theorem nsLookupMod_nsLift {m n v : Type} [BEq m] :
    ∀ (mn : m) (e : «namespace» m n v) (path : List m),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn == mn' then nsLookupMod e path' else none := by
  intros mn e path
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn' path' =>
    simp [nsLift, nsLookupMod, ALOOKUP]
    by_cases h : mn == mn' <;> simp [h]
/- HOL4: Theorem nsLookup_nsAppend_some -/
theorem nsLookup_nsAppend_some {m n v : Type} [BEq m] [BEq n] :
    ∀ (e1 : «namespace» m n v) (id_ : cml_id m n) (e2 : «namespace» m n v) (val_ : v),
      nsLookup (nsAppend e1 e2) id_ = some val_ ↔
        nsLookup e1 id_ = some val_ ∨
        (nsLookup e1 id_ = none ∧ nsLookup e2 id_ = some val_ ∧
         ∀ (p1 p2 : List m), p1 ≠ [] ∧ id_to_mods id_ = p1 ++ p2 →
           nsLookupMod e1 p1 = none) := sorry
/- HOL4: Theorem nsAppend_to_nsBindList -/
theorem nsAppend_to_nsBindList {m n v : Type} :
    ∀ (l : List (n × v)) (e : «namespace» m n v),
      nsAppend (alist_to_ns l) e = nsBindList l e := by
  intros l e
  induction l with
  | nil =>
    simp [alist_to_ns, nsBindList, nsAppend]
    cases e
    rfl
  | cons p l ih =>
    obtain ⟨k_, v_⟩ := p
    simp [alist_to_ns, nsBindList, List.foldr]
    show nsAppend (alist_to_ns ((k_, v_) :: l)) e =
         nsBind k_ v_ (l.foldr (fun p e => nsBind p.1 p.2 e) e)
    rw [alist_to_ns_cons]
    rw [nsAppend_nsBind]
    have ih' : nsBindList l e = (l.foldr (fun (p : n × v) e => nsBind p.1 p.2 e) e) := rfl
    rw [← ih', ← ih]
/- HOL4: Theorem nsLookupMod_nsAppend_none -/
theorem nsLookupMod_nsAppend_none {m n v : Type} [BEq m] :
    ∀ (e1 e2 : «namespace» m n v) (path : List m),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
         (nsLookupMod e2 path = none ∨
          ∃ (p1 p2 : List m) (e3 : «namespace» m n v),
            p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := sorry
/- HOL4: Theorem eALL_T[simp] -/
@[simp] theorem eALL_T {m n v : Type} [BEq m] [BEq n] :
    ∀ (e : «namespace» m n v), nsAll (fun (_n : cml_id m n) (_x : v) => True) e := by
  intro e
  intro id_ val_ _
  trivial
/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll {m n v : Type} [BEq m] [BEq n] :
    ∀ (env : «namespace» m n v) (x : cml_id m n) (P : cml_id m n → v → Prop) (val_ : v),
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ := by
  intros env x P val_ h
  exact h.1 x val_ h.2
private theorem ALOOKUP_append_split {α β : Type} [BEq α] (l1 l2 : List (α × β)) (k : α) (v : β) :
    ALOOKUP (l1 ++ l2) k = some v →
    ALOOKUP l1 k = some v ∨ (ALOOKUP l1 k = none ∧ ALOOKUP l2 k = some v) := by
  induction l1 with
  | nil => intro h; exact Or.inr ⟨rfl, by simpa [ALOOKUP] using h⟩
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    intro h
    simp [ALOOKUP] at h
    by_cases hk : k' == k
    · simp [hk] at h
      exact Or.inl (by simp [ALOOKUP, hk]; exact h)
    · simp [hk] at h
      rcases ih h with h' | ⟨h1, h2⟩
      · exact Or.inl (by simp [ALOOKUP, hk]; exact h')
      · exact Or.inr ⟨by simp [ALOOKUP, hk]; exact h1, h2⟩
/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  intros f e1 e2 hh
  obtain ⟨h1, h2⟩ := hh
  intros id_ val_ hl
  cases e1 with
  | Bind v1 m1 =>
  cases e2 with
  | Bind v2 m2 =>
  cases id_ with
  | Short x =>
    simp [nsAppend, nsLookup] at hl
    rcases ALOOKUP_append_split v1 v2 x val_ hl with hk | ⟨_, hk⟩
    · exact h1 (.Short x) val_ (by simp [nsLookup]; exact hk)
    · exact h2 (.Short x) val_ (by simp [nsLookup]; exact hk)
  | Long mn id' =>
    simp [nsAppend, nsLookup] at hl
    cases hM12 : ALOOKUP (m1 ++ m2) mn with
    | none => rw [hM12] at hl; simp at hl
    | some env =>
      rw [hM12] at hl; simp at hl
      rcases ALOOKUP_append_split m1 m2 mn env hM12 with hk | ⟨h1none, hk⟩
      · exact h1 (.Long mn id') val_ (by simp [nsLookup, hk]; exact hl)
      · exact h2 (.Long mn id') val_ (by simp [nsLookup, hk]; exact hl)
/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := by
  intros R l hR id_ val_ hl
  cases id_ with
  | Short x =>
    simp [alist_to_ns, nsLookup] at hl
    induction l with
    | nil => simp [ALOOKUP] at hl
    | cons p l ih =>
      obtain ⟨k_, v_⟩ := p
      simp [ALOOKUP] at hl
      split at hl
      · cases hl
        rename_i hkx
        have : k_ = x := LawfulBEq.eq_of_beq hkx
        subst this
        exact hR (k_, val_) (by simp)
      · exact ih (fun p hp => hR p (List.mem_cons_of_mem _ hp)) hl
  | Long mn id' =>
    simp [alist_to_ns, nsLookup, ALOOKUP] at hl
/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift {m n v : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := sorry
/- HOL4: Theorem nsAll_nsAppend_left -/
private theorem ALOOKUP_append_some {α β : Type} [BEq α] (l1 l2 : List (α × β)) (k : α) (v : β) :
    ALOOKUP l1 k = some v → ALOOKUP (l1 ++ l2) k = some v := by
  induction l1 with
  | nil => intro h; simp [ALOOKUP] at h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    intro h
    simp [ALOOKUP] at h ⊢
    by_cases hk : k' == k
    · simp [hk] at h ⊢; exact h
    · simp [hk] at h ⊢; exact ih h
theorem nsAll_nsAppend_left {m n v : Type} [BEq m] [BEq n] :
    ∀ (P : cml_id m n → v → Prop) (n1 n2 : «namespace» m n v),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intros P n1 n2 hAll
  intros id_ val_ hl
  apply hAll id_ val_
  cases n1 with
  | Bind v1 m1 =>
  cases n2 with
  | Bind v2 m2 =>
  cases id_ with
  | Short x =>
    simp [nsAppend, nsLookup] at hl ⊢
    exact ALOOKUP_append_some _ _ _ _ hl
  | Long mn id' =>
    simp [nsAppend, nsLookup] at hl ⊢
    cases hL : ALOOKUP m1 mn with
    | none => rw [hL] at hl; simp at hl
    | some env =>
      rw [hL] at hl
      simp at hl
      have := ALOOKUP_append_some m1 m2 mn env hL
      rw [this]; simp; exact hl
/- HOL4: Theorem nsSub_conj -/
theorem nsSub_conj {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop) (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsSub (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  intros P Q e1 e2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h2⟩, ⟨?_, h2⟩⟩
    · intro id_ v1_ hl
      obtain ⟨v2_, hv, hP, _⟩ := h1 id_ v1_ hl
      exact ⟨v2_, hv, hP⟩
    · intro id_ v1_ hl
      obtain ⟨v2_, hv, _, hQ⟩ := h1 id_ v1_ hl
      exact ⟨v2_, hv, hQ⟩
  · rintro ⟨⟨hP1, hM⟩, ⟨hQ1, _⟩⟩
    refine ⟨?_, hM⟩
    intro id_ v1_ hl
    obtain ⟨v2_, hv, hP⟩ := hP1 id_ v1_ hl
    obtain ⟨v2_', hv', hQ⟩ := hQ1 id_ v1_ hl
    rw [hv] at hv'
    cases hv'
    exact ⟨v2_, hv, hP, hQ⟩
/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl {m n v : Type} [BEq m] [BEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := by
  intros P R hPR e hAll
  refine ⟨?_, ?_⟩
  · intros id_ v1_ hl
    exact ⟨v1_, hl, hPR _ _ (hAll id_ v1_ hl)⟩
  · intros _ h; exact h
/- HOL4: Theorem nsSub_nsBind -/
theorem nsSub_nsBind {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsSub R e1 e2 →
        nsSub R (nsBind x v1_ e1) (nsBind x v2_ e2) := sorry
/- HOL4: Theorem nsSub_nsAppend2 -/
theorem nsSub_nsAppend2 {m n v_ : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v_ → v_ → Prop)
      (e1 : «namespace» m n v_) (e2 : «namespace» m n v_) (e2' : «namespace» m n v_),
      nsSub R e1 e1 ∧ nsSub R e2 e2' →
        nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := sorry
/- HOL4: Theorem alist_rel_restr_thm -/
theorem alist_rel_restr_thm {k v1 v2 : Type} [BEq k] :
    ∀ (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) (keys : List k),
      alist_rel_restr R e1 e2 keys ↔
        ∀ (k_ : k), MEM k_ keys = true →
          ∃ (val1 : v1) (val2 : v2),
            ALOOKUP e1 k_ = some val1 ∧ ALOOKUP e2 k_ = some val2 ∧ R k_ val1 val2 := sorry
/- HOL4: Theorem alistSub_cong -/
theorem alistSub_cong {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (l1 l1' : List (k × v1)) (l2 l2' : List (k × v2))
      (R R' : k → v1 → v2 → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ (n_ : k) (x : v1) (y : v2),
          ALOOKUP l1' n_ = some x ∧ ALOOKUP l2' n_ = some y → R n_ x y = R' n_ x y) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  intros l1 l1' l2 l2' R R' h
  obtain ⟨h1eq, h2eq, hRR'⟩ := h
  subst h1eq; subst h2eq
  unfold alistSub
  have key : ∀ keys, (∀ k_, MEM k_ keys = true → ∀ x y,
            ALOOKUP l1 k_ = some x ∧ ALOOKUP l2 k_ = some y → R k_ x y = R' k_ x y) →
      (alist_rel_restr R l1 l2 keys ↔ alist_rel_restr R' l1 l2 keys) := by
    intro keys hkeys
    induction keys with
    | nil => simp [alist_rel_restr]
    | cons k1 rest ih =>
      simp [alist_rel_restr]
      cases hL : ALOOKUP l1 k1 with
      | none => simp
      | some v1' =>
        cases hL2 : ALOOKUP l2 k1 with
        | none => simp
        | some v2' =>
          simp
          have hRR := hkeys k1 (by simp [MEM]) v1' v2' ⟨hL, hL2⟩
          rw [hRR]
          rw [ih (fun k hk => hkeys k (by simp [MEM] at hk ⊢; exact Or.inr hk))]
  apply key
  intro k_ _ x y h
  exact hRR' k_ x y h
/- HOL4: Theorem nsLookup_FOLDR_nsLift -/
theorem nsLookup_FOLDR_nsLift {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] :
    ∀ (e : «namespace» m n v) (p : List m) (k : n),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (cml_id.Short k) := by
  intros e p k
  induction p with
  | nil => rfl
  | cons mn p' ih =>
    show nsLookup (nsLift mn (FOLDR nsLift e p')) (mk_id (mn :: p') k) =
         nsLookup e (.Short k)
    show nsLookup (nsLift mn (FOLDR nsLift e p')) (.Long mn (mk_id p' k)) =
         nsLookup e (.Short k)
    simp [nsLift, nsLookup, ALOOKUP]
    exact ih
/- HOL4: Theorem nsLookup_FOLDR_nsLift_some -/
theorem nsLookup_FOLDR_nsLift_some {m n v : Type} [BEq m] [BEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (id_ : cml_id m n) (val_ : v),
      nsLookup (FOLDR nsLift e p) id_ = some val_ ↔
        (p = [] ∧ nsLookup e id_ = some val_) ∨
        (p ≠ [] ∧ ∃ (p2 : List m) (n_ : n),
          id_ = mk_id (p ++ p2) n_ ∧ nsLookup e (mk_id p2 n_) = some val_) := sorry
/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none -/
theorem nsLookupMod_FOLDR_nsLift_none {m n v : Type} [BEq m] :
    ∀ (e : «namespace» m n v) (p1 p2 : List m),
      nsLookupMod (FOLDR nsLift e p1) p2 = none ↔
        (IS_PREFIX p1 p2 = true ∨ IS_PREFIX p2 p1 = true) →
          ∃ (p3 : List m), p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := sorry
/- HOL4: Theorem nsAll2_conj -/
theorem nsAll2_conj {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  intros P Q e1 e2
  unfold nsAll2
  rw [nsSub_conj P Q e1 e2]
  rw [show (fun x y z => P x z y ∧ Q x z y) =
      (fun x y z => (fun a b c => P a c b) x y z ∧ (fun a b c => Q a c b) x y z) from rfl]
  rw [nsSub_conj _ _ e2 e1]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
  intros R e1 e2 n_ v2_ h
  obtain ⟨hl, _, h2V, _⟩ := h
  exact h2V n_ v2_ hl
/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
  intros R e1 e2 n_ h
  obtain ⟨⟨h1V, _⟩, ⟨h2V, _⟩⟩ := h
  constructor
  · intro h
    cases hl : nsLookup e2 n_ with
    | none => rfl
    | some v2_ =>
      obtain ⟨v1_, hv1, _⟩ := h2V n_ v2_ hl
      rw [hv1] at h
      contradiction
  · intro h
    cases hl : nsLookup e1 n_ with
    | none => rfl
    | some v1_ =>
      obtain ⟨v2_, hv2, _⟩ := h1V n_ v1_ hl
      rw [hv2] at h
      contradiction
/- HOL4: Theorem nsAll2_nsBind -/
theorem nsAll2_nsBind {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBind x v1_ e1) (nsBind x v2_ e2) := sorry
/- HOL4: Theorem nsAll2_nsBindList -/
theorem nsAll2_nsBindList {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (l1 : List (n × v1)) (l2 : List (n × v2))
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 ∧
      nsAll2 R e1 e2 →
        nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := sorry
/- HOL4: Theorem nsAll2_nsAppend -/
theorem nsAll2_nsAppend {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
      (e1' : «namespace» m n v1) (e2' : «namespace» m n v2),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
        nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := sorry
/- HOL4: Theorem nsAll2_alist_to_ns -/
theorem nsAll2_alist_to_ns {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (l1 : List (n × v1)) (l2 : List (n × v2)),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 →
        nsAll2 R (alist_to_ns l1 : «namespace» m n v1) (alist_to_ns l2 : «namespace» m n v2) := sorry
/- HOL4: Theorem nsAll2_nsLift[simp] -/
theorem nsAll2_nsLift {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (mn : m)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
        nsAll2 (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := sorry

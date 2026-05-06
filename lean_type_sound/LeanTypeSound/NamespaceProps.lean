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
  decreasing_by all_goals sorry

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem mk_id_thm: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {m n : Type} :
    ∀ (id : cml_id m n), mk_id (id_to_mods id) (id_to_n id) = id := by
  intro id
  induction id with
  | Short x => simp [id_to_mods, id_to_n, mk_id]
  | Long m i ih => simp [id_to_mods, id_to_n, mk_id, ih]
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
  intro hmono ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  intro id v hl
  obtain ⟨v', hv', hr⟩ := h1 id v hl
  exact ⟨v', hv', hmono _ _ _ hr⟩
/- HOL4: Theorem nsAll2_mono[mono] -/
theorem nsAll2_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  intro hmono ⟨h1, h2⟩
  refine ⟨nsSub_mono hmono h1, ?_⟩
  exact nsSub_mono (fun x y z h => hmono x z y h) h2
/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
theorem nsLookup_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (id : cml_id m n), nsLookup (nsEmpty : «namespace» m n v) id = none := by
  intro id
  cases id with
  | Short x => simp [nsEmpty, nsLookup, ALOOKUP]
  | Long mn i => simp [nsEmpty, nsLookup, ALOOKUP]
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none := by
  intro x y
  simp [nsEmpty, nsLookupMod, ALOOKUP]
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env
  cases env with
  | Bind v m =>
    simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := rfl
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  refine ⟨?_, ?_⟩
  · intro id v hl
    have : nsLookup (nsEmpty : «namespace» m n v1) id = none := nsLookup_nsEmpty id
    rw [this] at hl; cases hl
  · intro p hp
    cases p with
    | nil => exfalso; simp [nsLookupMod] at hp
    | cons _ _ => simp [nsLookupMod, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id w hl
  have heq : nsLookup (nsEmpty : «namespace» m n v) id = none := nsLookup_nsEmpty id
  rw [heq] at hl; cases hl
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := by
  intro f
  exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) := by
  intros k val_ l; rfl
/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intro k val_ e1 e2
  cases e1 with
  | Bind v1 m1 =>
    cases e2 with
    | Bind v2 m2 => simp [nsBind, nsAppend]
/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3
  cases e1 with
  | Bind v1 m1 => cases e2 with
    | Bind v2 m2 => cases e3 with
      | Bind v3 m3 => simp [nsAppend, List.append_assoc]
/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  refine ⟨?_, ?_⟩
  · intro n_ val_ e
    cases e with
    | Bind v m => simp [nsBind, nsLookup, ALOOKUP]
  · intro id_ n_ val_ e hne
    cases e with
    | Bind v m =>
      cases id_ with
      | Short x =>
        simp [nsBind, nsLookup, ALOOKUP]
        intro heq
        exact absurd (by rw [heq]) hne
      | Long _ _ => simp [nsBind, nsLookup]
/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intro n_ x e
  cases e with
  | Bind v m => simp [nsAppend, nsSing, nsBind]
/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] [LawfulBEq m] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := by
  intro n_ val_ id_
  cases id_ with
  | Short x =>
    show nsLookup (.Bind [(n_, val_)] []) (cml_id.Short x) = _
    show ALOOKUP [(n_, val_)] x = _
    show (if (n_ == x) = true then some val_ else ALOOKUP [] x) =
         (if (cml_id.Short x == cml_id.Short (m := m) n_) = true then some val_ else none)
    by_cases hbeq : (n_ == x) = true
    · have hxn : x = n_ := (eq_of_beq hbeq).symm
      cases hxn
      have heqs : (cml_id.Short (m := m) n_ == cml_id.Short n_) = true := by
        show (n_ == n_) = true
        exact beq_self_eq_true _
      rw [heqs]
      simp [hbeq]
    · have h1 : (x == n_) = false := by
        rcases h : (x == n_) with _ | _
        · rfl
        · exfalso; apply hbeq; rw [show (n_ == x) = (x == n_) from BEq.comm]; exact h
      simp [hbeq]
      show ALOOKUP ([] : List (n × v)) x =
           if (cml_id.Short x == cml_id.Short (m := m) n_) = true then some val_ else none
      have h2 : (cml_id.Short x == cml_id.Short (m := m) n_) = false := by
        show (x == n_) = false; exact h1
      rw [h2]
      rfl
  | Long mn id' =>
    show nsLookup (@«namespace».Bind m n v [(n_, val_)] []) (cml_id.Long mn id') = _
    show (match (ALOOKUP [] mn : Option («namespace» m n v)) with
          | none => none
          | some env => nsLookup env id') =
         (if (cml_id.Long mn id' == cml_id.Short (m := m) n_) = true then some val_ else none)
    have h1 : (ALOOKUP [] mn : Option («namespace» m n v)) = none := rfl
    have h2 : (cml_id.Long mn id' == cml_id.Short (m := m) n_) = false := rfl
    rw [h1, h2]
    rfl
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
      nsBind x y ns = nsBind x' y' ns' ↔ x = x' ∧ y = y' ∧ ns = ns' := by
  intro x y ns x' y' ns'
  cases ns with
  | Bind val_ md => cases ns' with
    | Bind val_' md' =>
      simp [nsBind]
      constructor
      · intro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
      · intro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
/- HOL4: Theorem alist_to_ns_11[simp] -/
theorem alist_to_ns_11 {m n v : Type} :
    ∀ (l1 l2 : List (n × v)),
      (alist_to_ns l1 : «namespace» m n v) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2
  simp [alist_to_ns]
/- HOL4: Theorem nsLookup_nsLift -/
theorem nsLookup_nsLift {m n v : Type} [BEq m] [BEq n] :
    ∀ (mn : m) (e : «namespace» m n v) (id_ : cml_id m n),
      nsLookup (nsLift mn e) id_ =
        match id_ with
        | cml_id.Long mn' id' => if mn == mn' then nsLookup e id' else none
        | cml_id.Short _ => none := sorry
/- HOL4: Theorem nsLookupMod_nsLift -/
theorem nsLookupMod_nsLift {m n v : Type} [BEq m] :
    ∀ (mn : m) (e : «namespace» m n v) (path : List m),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn == mn' then nsLookupMod e path' else none := sorry
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
  intro l e
  induction l with
  | nil =>
    cases e with
    | Bind v m => simp [alist_to_ns, nsAppend, nsBindList]
  | cons p rest ih =>
    obtain ⟨k, val_⟩ := p
    show nsAppend (alist_to_ns ((k, val_) :: rest)) e = nsBindList ((k, val_) :: rest) e
    rw [show nsBindList ((k, val_) :: rest) e = nsBind k val_ (nsBindList rest e) from rfl]
    rw [← ih]
    cases e with
    | Bind v m => simp [alist_to_ns, nsAppend, nsBind]
/- HOL4: Theorem nsLookupMod_nsAppend_none -/
theorem nsLookupMod_nsAppend_none {m n v : Type} [BEq m] :
    ∀ (e1 e2 : «namespace» m n v) (path : List m),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
         (nsLookupMod e2 path = none ∨
          ∃ (p1 p2 : List m) (e3 : «namespace» m n v),
            p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := sorry
/- HOL4: Theorem eALL_T[simp] -/
theorem eALL_T {m n v : Type} [BEq m] [BEq n] :
    ∀ (e : «namespace» m n v), nsAll (fun (_n : cml_id m n) (_x : v) => True) e := by
  intro e _ _ _; trivial
/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll {m n v : Type} [BEq m] [BEq n] :
    ∀ (env : «namespace» m n v) (x : cml_id m n) (P : cml_id m n → v → Prop) (val_ : v),
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ := by
  intro env x P val_ ⟨hall, hl⟩
  exact hall x val_ hl
/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := sorry
/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := by
  intro R l hall id v hl
  cases id with
  | Short x =>
    simp [alist_to_ns, nsLookup] at hl
    induction l with
    | nil => simp [ALOOKUP] at hl
    | cons p rest ih =>
      obtain ⟨k, val_⟩ := p
      simp [ALOOKUP] at hl
      split at hl
      · cases hl
        rename_i hbeq
        have hkx : k = x := eq_of_beq hbeq
        cases hkx
        exact hall (x, v) List.mem_cons_self
      · apply ih (fun p hp => hall p (List.mem_cons_of_mem _ hp)) hl
  | Long mn id' =>
    simp [alist_to_ns, nsLookup, ALOOKUP] at hl
/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := by
  intro R mn e
  unfold nsAll nsLift
  constructor
  · intro hl id w hlk
    have : nsLookup (@«namespace».Bind m n v [] [(mn, e)]) (cml_id.Long mn id) = some w := by
      show (match (ALOOKUP [(mn, e)] mn : Option («namespace» m n v)) with
            | none => none
            | some env => nsLookup env id) = some w
      simp [ALOOKUP]
      exact hlk
    exact hl _ _ this
  · intro hl id w hlk
    cases id with
    | Short x => simp [nsLookup, ALOOKUP] at hlk
    | Long mn' id' =>
      show R (cml_id.Long mn' id') w
      have hlk' : (match (ALOOKUP [(mn, e)] mn' : Option («namespace» m n v)) with
                   | none => none
                   | some env => nsLookup env id') = some w := hlk
      simp [ALOOKUP] at hlk'
      by_cases hbeq : (mn == mn') = true
      · simp [hbeq] at hlk'
        have : mn = mn' := eq_of_beq hbeq
        cases this
        exact hl _ _ hlk'
      · simp [hbeq] at hlk'
/- HOL4: Theorem nsAll_nsAppend_left -/
theorem nsAll_nsAppend_left {m n v : Type} [BEq m] [BEq n] :
    ∀ (P : cml_id m n → v → Prop) (n1 n2 : «namespace» m n v),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := sorry
/- HOL4: Theorem nsSub_conj -/
theorem nsSub_conj {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop) (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsSub (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  intro P Q e1 e2
  unfold nsSub
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨⟨?_, h2⟩, ⟨?_, h2⟩⟩
    · intro id_ v1_ hl
      obtain ⟨v2_, hl2, hP, _⟩ := h1 _ _ hl
      exact ⟨v2_, hl2, hP⟩
    · intro id_ v1_ hl
      obtain ⟨v2_, hl2, _, hQ⟩ := h1 _ _ hl
      exact ⟨v2_, hl2, hQ⟩
  · intro ⟨⟨h1P, h2⟩, ⟨h1Q, _⟩⟩
    refine ⟨?_, h2⟩
    intro id_ v1_ hl
    obtain ⟨v2_, hl2, hP⟩ := h1P _ _ hl
    obtain ⟨v2_', hl2', hQ⟩ := h1Q _ _ hl
    rw [hl2'] at hl2; cases hl2
    exact ⟨v2_, hl2', hP, hQ⟩
/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl {m n v : Type} [BEq m] [BEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := sorry
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
theorem alist_rel_restr_thm {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) (keys : List k),
      alist_rel_restr R e1 e2 keys ↔
        ∀ (k_ : k), MEM k_ keys = true →
          ∃ (val1 : v1) (val2 : v2),
            ALOOKUP e1 k_ = some val1 ∧ ALOOKUP e2 k_ = some val2 ∧ R k_ val1 val2 := by
  intro R e1 e2 keys
  induction keys with
  | nil => simp [alist_rel_restr, MEM]
  | cons k1 rest ih =>
    simp only [alist_rel_restr]
    constructor
    · intro h
      cases hl1 : ALOOKUP e1 k1 with
      | none => rw [hl1] at h; cases h
      | some v1' =>
        rw [hl1] at h
        cases hl2 : ALOOKUP e2 k1 with
        | none => rw [hl2] at h; cases h
        | some v2' =>
          rw [hl2] at h
          obtain ⟨hr, hrest⟩ := h
          intro k_ hk_
          simp [MEM] at hk_
          rcases hk_ with hk_ | hk_
          · cases hk_; exact ⟨v1', v2', hl1, hl2, hr⟩
          · rw [ih] at hrest
            exact hrest k_ (by simp [MEM]; exact hk_)
    · intro h
      have h1 := h k1 (by simp [MEM])
      obtain ⟨v1', v2', hl1, hl2, hr⟩ := h1
      rw [hl1, hl2]
      refine ⟨hr, ?_⟩
      rw [ih]
      intro k_ hk_
      exact h k_ (by simp [MEM] at hk_ ⊢; right; exact hk_)
/- HOL4: Theorem alistSub_cong -/
theorem alistSub_cong {k v1 v2 : Type} [BEq k] :
    ∀ (l1 l1' : List (k × v1)) (l2 l2' : List (k × v2))
      (R R' : k → v1 → v2 → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ (n_ : k) (x : v1) (y : v2),
          ALOOKUP l1' n_ = some x ∧ ALOOKUP l2' n_ = some y → R n_ x y = R' n_ x y) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := sorry
/- HOL4: Theorem nsLookup_FOLDR_nsLift -/
theorem nsLookup_FOLDR_nsLift {m n v : Type} [BEq m] [BEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (k : n),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (cml_id.Short k) := sorry
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
  intro P Q e1 e2
  unfold nsAll2
  rw [nsSub_conj]
  rw [nsSub_conj]
  constructor
  · intro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨a, c⟩, b, d⟩
  · intro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨a, c⟩, b, d⟩
/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
  intro R e1 e2 n_ v2_ ⟨hl, _, hsr⟩
  unfold nsSub at hsr
  obtain ⟨v1_, hl1, hr⟩ := hsr.1 _ _ hl
  exact ⟨v1_, hl1, hr⟩
/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
  intro R e1 e2 n_ ⟨h1, h2⟩
  unfold nsSub at h1 h2
  constructor
  · intro hn
    rcases hl : nsLookup e2 n_ with _ | v
    · rfl
    · obtain ⟨v', hv', _⟩ := h2.1 _ _ hl
      rw [hv'] at hn; cases hn
  · intro hn
    rcases hl : nsLookup e1 n_ with _ | v
    · rfl
    · obtain ⟨v', hv', _⟩ := h1.1 _ _ hl
      rw [hv'] at hn; cases hn
/- HOL4: Theorem nsAll2_nsBind -/
theorem nsAll2_nsBind {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
  intro R x v1_ v2_ e1 e2 ⟨hR, hl, hr⟩
  exact ⟨nsSub_nsBind R x v1_ v2_ e1 e2 ⟨hR, hl⟩, nsSub_nsBind _ x v2_ v1_ e2 e1 ⟨hR, hr⟩⟩
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
theorem nsAll2_nsLift {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (mn : m)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
        nsAll2 (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := by
  intro R mn e1 e2
  unfold nsAll2 nsSub nsLift
  constructor
  · intro ⟨⟨h1a, h1b⟩, h2a, h2b⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro id w hlk
      have hlk' : nsLookup (@«namespace».Bind m n v1 [] [(mn, e1)]) (cml_id.Long mn id) = some w := by
        show (match (ALOOKUP [(mn, e1)] mn : Option («namespace» m n v1)) with
              | none => none
              | some env => nsLookup env id) = some w
        simp [ALOOKUP]; exact hlk
      obtain ⟨v2_, hv2', hr⟩ := h1a _ _ hlk'
      have hlk2 : (match (ALOOKUP [(mn, e2)] mn : Option («namespace» m n v2)) with
                   | none => none
                   | some env => nsLookup env id) = some v2_ := hv2'
      simp [ALOOKUP] at hlk2
      exact ⟨v2_, hlk2, hr⟩
    · intro path hp
      have := h1b (mn :: path) (by
        show (match (ALOOKUP [(mn, e2)] mn : Option («namespace» m n v2)) with
              | none => none
              | some env => nsLookupMod env path) = none
        simp [ALOOKUP]; exact hp)
      have htgt : (match (ALOOKUP [(mn, e1)] mn : Option («namespace» m n v1)) with
                   | none => none
                   | some env => nsLookupMod env path) = none := this
      simp [ALOOKUP] at htgt
      exact htgt
    · intro id w hlk
      have hlk' : nsLookup (@«namespace».Bind m n v2 [] [(mn, e2)]) (cml_id.Long mn id) = some w := by
        show (match (ALOOKUP [(mn, e2)] mn : Option («namespace» m n v2)) with
              | none => none
              | some env => nsLookup env id) = some w
        simp [ALOOKUP]; exact hlk
      obtain ⟨v1_, hv1', hr⟩ := h2a _ _ hlk'
      have hlk2 : (match (ALOOKUP [(mn, e1)] mn : Option («namespace» m n v1)) with
                   | none => none
                   | some env => nsLookup env id) = some v1_ := hv1'
      simp [ALOOKUP] at hlk2
      exact ⟨v1_, hlk2, hr⟩
    · intro path hp
      have := h2b (mn :: path) (by
        show (match (ALOOKUP [(mn, e1)] mn : Option («namespace» m n v1)) with
              | none => none
              | some env => nsLookupMod env path) = none
        simp [ALOOKUP]; exact hp)
      have htgt : (match (ALOOKUP [(mn, e2)] mn : Option («namespace» m n v2)) with
                   | none => none
                   | some env => nsLookupMod env path) = none := this
      simp [ALOOKUP] at htgt
      exact htgt
  · intro ⟨⟨h1a, h1b⟩, h2a, h2b⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro id w hlk
      cases id with
      | Short x => simp [nsLookup, ALOOKUP] at hlk
      | Long mn' id' =>
        show ∃ v2_, nsLookup (@«namespace».Bind m n v2 [] [(mn, e2)]) (cml_id.Long mn' id') = some v2_ ∧ R (cml_id.Long mn' id') w v2_
        have hlk' : (match (ALOOKUP [(mn, e1)] mn' : Option («namespace» m n v1)) with
                     | none => none
                     | some env => nsLookup env id') = some w := hlk
        simp [ALOOKUP] at hlk'
        by_cases hbeq : (mn == mn') = true
        · simp [hbeq] at hlk'
          have hmn : mn = mn' := eq_of_beq hbeq
          cases hmn
          obtain ⟨v2_, hv2', hr⟩ := h1a _ _ hlk'
          refine ⟨v2_, ?_, hr⟩
          show (match (ALOOKUP [(mn, e2)] mn : Option («namespace» m n v2)) with
                | none => none
                | some env => nsLookup env id') = some v2_
          simp [ALOOKUP]; exact hv2'
        · simp [hbeq] at hlk'
    · intro path hp
      cases path with
      | nil =>
        show nsLookupMod (@«namespace».Bind m n v1 [] [(mn, e1)]) [] = none
        simp [nsLookupMod] at hp
      | cons mn' path' =>
        show (match (ALOOKUP [(mn, e1)] mn' : Option («namespace» m n v1)) with
              | none => none
              | some env => nsLookupMod env path') = none
        have hp' : (match (ALOOKUP [(mn, e2)] mn' : Option («namespace» m n v2)) with
                    | none => none
                    | some env => nsLookupMod env path') = none := hp
        simp [ALOOKUP] at hp' ⊢
        by_cases hbeq : (mn == mn') = true
        · simp [hbeq] at hp' ⊢
          have hmn : mn = mn' := eq_of_beq hbeq
          cases hmn
          exact h1b path' hp'
        · simp [hbeq]
    · intro id w hlk
      cases id with
      | Short x => simp [nsLookup, ALOOKUP] at hlk
      | Long mn' id' =>
        show ∃ v1_, nsLookup (@«namespace».Bind m n v1 [] [(mn, e1)]) (cml_id.Long mn' id') = some v1_ ∧ R (cml_id.Long mn' id') v1_ w
        have hlk' : (match (ALOOKUP [(mn, e2)] mn' : Option («namespace» m n v2)) with
                     | none => none
                     | some env => nsLookup env id') = some w := hlk
        simp [ALOOKUP] at hlk'
        by_cases hbeq : (mn == mn') = true
        · simp [hbeq] at hlk'
          have hmn : mn = mn' := eq_of_beq hbeq
          cases hmn
          obtain ⟨v1_, hv1', hr⟩ := h2a _ _ hlk'
          refine ⟨v1_, ?_, hr⟩
          show (match (ALOOKUP [(mn, e1)] mn : Option («namespace» m n v1)) with
                | none => none
                | some env => nsLookup env id') = some v1_
          simp [ALOOKUP]; exact hv1'
        · simp [hbeq] at hlk'
    · intro path hp
      cases path with
      | nil =>
        show nsLookupMod (@«namespace».Bind m n v2 [] [(mn, e2)]) [] = none
        simp [nsLookupMod] at hp
      | cons mn' path' =>
        show (match (ALOOKUP [(mn, e2)] mn' : Option («namespace» m n v2)) with
              | none => none
              | some env => nsLookupMod env path') = none
        have hp' : (match (ALOOKUP [(mn, e1)] mn' : Option («namespace» m n v1)) with
                    | none => none
                    | some env => nsLookupMod env path') = none := hp
        simp [ALOOKUP] at hp' ⊢
        by_cases hbeq : (mn == mn') = true
        · simp [hbeq] at hp' ⊢
          have hmn : mn = mn' := eq_of_beq hbeq
          cases hmn
          exact h2b path' hp'
        · simp [hbeq]

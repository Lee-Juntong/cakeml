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
   Lean note: the recursive call is guarded by a size test so that termination
   is evident to Lean.  The guard always holds for the values that `alistSub`
   actually inspects (they are looked up in `e1M`), so this is equivalent to
   the HOL4 definition.
-/
def nsSub_compute {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop) :
    «namespace» m n v1 → «namespace» m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
    alistSub (fun k val1 val2 =>
      if sizeOf val1 < sizeOf («namespace».Bind e1V e1M) then
        nsSub_compute (k :: path) R val1 val2
      else False) e1M e2M
  termination_by e1 => sizeOf e1
  decreasing_by assumption

-- ============================================================
-- Theorem stubs
-- ============================================================

-- ============================================================
-- Auxiliary lemmas about `ALOOKUP` and namespaces
-- ============================================================

theorem ALOOKUP_append {α β : Type} [BEq α] (l1 l2 : List (α × β)) (k : α) :
    ALOOKUP (l1 ++ l2) k = (ALOOKUP l1 k).or (ALOOKUP l2 k) := by
  induction l1 with
  | nil => simp [ALOOKUP]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, ALOOKUP]
    split <;> simp [ih]

theorem ALOOKUP_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β} :
    ALOOKUP l k = some v → (k, v) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP]
    split
    · rename_i h; intro e; cases e; simp at h; subst h; simp
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem ALOOKUP_none_iff {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} :
    ALOOKUP l k = none ↔ k ∉ l.map Prod.fst := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP, List.map_cons, List.mem_cons]
    split
    · rename_i h; simp at h; subst h; simp
    · rename_i h; simp at h; rw [ih]; constructor
      · intro h1 h2; rcases h2 with h2 | h2
        · exact h (h2.symm)
        · exact h1 h2
      · intro h1 h2; exact h1 (Or.inr h2)

theorem nsLookupMod_nsBind {m n v : Type} [BEq m] (x : n) (val_ : v)
    (e : «namespace» m n v) (path : List m) (hp : path ≠ []) :
    nsLookupMod (nsBind x val_ e) path = nsLookupMod e path := by
  cases e with
  | Bind vals mods =>
    cases path with
    | nil => exact absurd rfl hp
    | cons mn p => simp [nsBind, nsLookupMod]

theorem nsLookup_Bind_Long {m n v : Type} [BEq m] [BEq n] (vals : List (n × v))
    (mods : List (m × «namespace» m n v)) (mn : m) (id_ : cml_id m n) :
    nsLookup (.Bind vals mods) (.Long mn id_) =
      match ALOOKUP mods mn with
      | none => none
      | some env => nsLookup env id_ := rfl

theorem nsLookupMod_Bind_cons {m n v : Type} [BEq m] (vals : List (n × v))
    (mods : List (m × «namespace» m n v)) (mn : m) (p : List m) :
    nsLookupMod (.Bind vals mods) (mn :: p) =
      match ALOOKUP mods mn with
      | none => none
      | some env => nsLookupMod env p := rfl

/- HOL4: Theorem mk_id_thm: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {m n : Type} :
    ∀ (id : cml_id m n), mk_id (id_to_mods id) (id_to_n id) = id := by
  intro id
  induction id with
  | Short x => rfl
  | Long mn i ih => simp only [id_to_mods, id_to_n, mk_id, ih]
/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {m n : Type} :
    ∀ (id : cml_id m n), ∃ (p : List m) (n_ : n), id = mk_id p n_ := fun id => ⟨id_to_mods id, id_to_n id, (mk_id_thm id).symm⟩
/- HOL4: Theorem nsSub_mono[mono] -/
theorem nsSub_mono {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  intro hR ⟨h1, h2⟩
  refine ⟨fun id v1_ hl => ?_, h2⟩
  obtain ⟨v2_, h, hr⟩ := h1 id v1_ hl
  exact ⟨v2_, h, hR _ _ _ hr⟩
/- HOL4: Theorem nsAll2_mono[mono] -/
theorem nsAll2_mono {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  intro hR ⟨h1, h2⟩
  exact ⟨nsSub_mono hR h1, nsSub_mono (fun x y z h => hR x z y h) h2⟩
/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
theorem nsLookup_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (id : cml_id m n), nsLookup (nsEmpty : «namespace» m n v) id = none := by
  intro id; cases id <;> simp [nsEmpty, nsLookup, ALOOKUP]
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none := by
  intro x y; simp [nsEmpty, nsLookupMod, ALOOKUP]
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env; cases env; simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := rfl
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  refine ⟨fun id v h => by simp [nsLookup_nsEmpty] at h, fun path h => ?_⟩
  cases path with
  | nil => simp [nsLookupMod] at h
  | cons x y => exact nsLookupMod_nsEmpty x y
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id v h; simp [nsLookup_nsEmpty] at h
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := by
  intro f; exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) := by intros; rfl
/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intro k val_ e1 e2; cases e1; cases e2; rfl
/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3; cases e1; cases e2; cases e3; simp [nsAppend]
/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  constructor
  · intro n_ val_ e; cases e; simp [nsBind, nsLookup, ALOOKUP]
  · intro id_ n_ val_ e hne
    cases e with
    | Bind vals mods =>
      cases id_ with
      | Short x =>
        have : n_ ≠ x := fun h => hne (by rw [h])
        simp [nsBind, nsLookup, ALOOKUP, this]
      | Long mn i => simp [nsBind, nsLookup]
/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intro n_ x e; cases e; rfl
/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := by
  intro n_ val_ id_
  cases id_ with
  | Short x =>
    by_cases h : x = n_
    · subst h; simp [nsSing, nsLookup, ALOOKUP]
    · have : n_ ≠ x := fun e => h e.symm
      simp [nsSing, nsLookup, ALOOKUP, h, this]
  | Long mn i => simp [nsSing, nsLookup, ALOOKUP]
/- HOL4: Theorem nsAll_nsSing[simp] -/
theorem nsAll_nsSing {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (n_ : n) (val_ : v),
      nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := by
  intro R n_ val_
  constructor
  · intro h; exact h _ _ (by simp [nsLookup_nsSing])
  · intro hR id_ v hl
    rw [nsLookup_nsSing] at hl
    split at hl
    · rename_i h; simp at h hl; subst h; subst hl; exact hR
    · cases hl
/- HOL4: Theorem nsAll2_nsSing[simp] -/
theorem nsAll2_nsSing {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (n1 : n) (v1_ : v1) (n2 : n) (v2_ : v2),
      nsAll2 R (nsSing n1 v1_ : «namespace» m n v1) (nsSing n2 v2_ : «namespace» m n v2) ↔
        n1 = n2 ∧ R (cml_id.Short n1) v1_ v2_ := by
  intro R n1 v1_ n2 v2_
  constructor
  · rintro ⟨⟨h1, _⟩, _⟩
    obtain ⟨v2', hl, hr⟩ := h1 (.Short n1) v1_ (by simp [nsLookup_nsSing])
    rw [nsLookup_nsSing] at hl
    split at hl
    · rename_i h; simp at h hl; subst h; subst hl; exact ⟨rfl, hr⟩
    · cases hl
  · rintro ⟨rfl, hr⟩
    have hmod : ∀ {w : Type} (x : w) (path : List m),
        nsLookupMod (nsSing n1 x : «namespace» m n w) path = none ↔ path ≠ [] := by
      intro w x path; cases path <;> simp [nsSing, nsLookupMod, ALOOKUP]
    refine ⟨⟨fun id_ v hl => ?_, fun path h => (hmod _ _).2 ((hmod _ _).1 h)⟩,
            ⟨fun id_ v hl => ?_, fun path h => (hmod _ _).2 ((hmod _ _).1 h)⟩⟩
    · rw [nsLookup_nsSing] at hl
      split at hl
      · rename_i h; simp at h hl; subst h; subst hl
        exact ⟨v2_, by simp [nsLookup_nsSing], hr⟩
      · cases hl
    · rw [nsLookup_nsSing] at hl
      split at hl
      · rename_i h; simp at h hl; subst h; subst hl
        exact ⟨v1_, by simp [nsLookup_nsSing], hr⟩
      · cases hl
/- HOL4: Theorem nsBind_11[simp] -/
theorem nsBind_11 {m n v : Type} :
    ∀ (x : n) (y : v) (ns : «namespace» m n v) (x' : n) (y' : v) (ns' : «namespace» m n v),
      nsBind x y ns = nsBind x' y' ns' ↔ x = x' ∧ y = y' ∧ ns = ns' := by
  intro x y ns x' y' ns'
  cases ns; cases ns'; simp [nsBind, and_assoc]
/- HOL4: Theorem alist_to_ns_11[simp] -/
theorem alist_to_ns_11 {m n v : Type} :
    ∀ (l1 l2 : List (n × v)),
      (alist_to_ns l1 : «namespace» m n v) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2; simp [alist_to_ns]
/- HOL4: Theorem nsLookup_nsLift -/
theorem nsLookup_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (mn : m) (e : «namespace» m n v) (id_ : cml_id m n),
      nsLookup (nsLift mn e) id_ =
        match id_ with
        | cml_id.Long mn' id' => if mn == mn' then nsLookup e id' else none
        | cml_id.Short _ => none := by
  intro mn e id_
  cases id_ with
  | Short x => simp [nsLift, nsLookup, ALOOKUP]
  | Long mn' i =>
    by_cases h : mn = mn'
    · subst h; simp [nsLift, nsLookup, ALOOKUP]
    · simp [nsLift, nsLookup, ALOOKUP, h]
/- HOL4: Theorem nsLookupMod_nsLift -/
theorem nsLookupMod_nsLift {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (mn : m) (e : «namespace» m n v) (path : List m),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn == mn' then nsLookupMod e path' else none := by
  intro mn e path
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn' p =>
    by_cases h : mn = mn'
    · subst h; simp [nsLift, nsLookupMod, ALOOKUP]
    · simp [nsLift, nsLookupMod, ALOOKUP, h]
/- HOL4: Theorem nsLookup_nsAppend_some -/
theorem nsLookup_nsAppend_some {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e1 : «namespace» m n v) (id_ : cml_id m n) (e2 : «namespace» m n v) (val_ : v),
      nsLookup (nsAppend e1 e2) id_ = some val_ ↔
        nsLookup e1 id_ = some val_ ∨
        (nsLookup e1 id_ = none ∧ nsLookup e2 id_ = some val_ ∧
         ∀ (p1 p2 : List m), p1 ≠ [] ∧ id_to_mods id_ = p1 ++ p2 →
           nsLookupMod e1 p1 = none) := by
  intro e1 id_ e2 val_
  cases e1 with
  | Bind v1 m1 =>
  cases e2 with
  | Bind v2 m2 =>
  cases id_ with
  | Short x =>
    simp only [nsAppend, nsLookup, ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP v1 x with
    | some a => simp
    | none =>
      simp only [Option.none_or, reduceCtorEq, false_or, true_and]
      constructor
      · intro h2; refine ⟨h2, fun p1 p2 ⟨hp, he⟩ => ?_⟩
        cases p1 with
        | nil => exact absurd rfl hp
        | cons _ _ => simp at he
      · intro h2; exact h2.1
  | Long mn i =>
    simp only [nsAppend, nsLookup_Bind_Long, ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP m1 mn with
    | some env1 =>
      simp only [Option.some_or]
      constructor
      · intro h2; exact Or.inl h2
      · rintro (h2 | ⟨h2, _, h3⟩)
        · exact h2
        · have := h3 [mn] (id_to_mods i) ⟨by simp, by simp⟩
          simp [h, nsLookupMod] at this
    | none =>
      simp only [Option.none_or, reduceCtorEq, false_or, true_and]
      constructor
      · intro h2; refine ⟨h2, fun p1 p2 ⟨hp, he⟩ => ?_⟩
        cases p1 with
        | nil => exact absurd rfl hp
        | cons a p1' =>
          simp at he; obtain ⟨rfl, _⟩ := he
          simp [nsLookupMod_Bind_cons, h]
      · intro h2; exact h2.1
/- HOL4: Theorem nsAppend_to_nsBindList -/
theorem nsAppend_to_nsBindList {m n v : Type} :
    ∀ (l : List (n × v)) (e : «namespace» m n v),
      nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l e
  induction l with
  | nil => exact (nsAppend_nsEmpty e).2
  | cons p l ih =>
    obtain ⟨k, x⟩ := p
    rw [alist_to_ns_cons, nsAppend_nsBind, ih]; rfl
/- HOL4: Theorem nsLookupMod_nsAppend_none -/
theorem nsLookupMod_nsAppend_none {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (e1 e2 : «namespace» m n v) (path : List m),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
         (nsLookupMod e2 path = none ∨
          ∃ (p1 p2 : List m) (e3 : «namespace» m n v),
            p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  intro e1 e2 path
  cases e1 with
  | Bind v1 m1 =>
  cases e2 with
  | Bind v2 m2 =>
  cases path with
  | nil => simp [nsLookupMod, nsAppend]
  | cons mn p =>
    simp only [nsAppend, nsLookupMod_Bind_cons, ALOOKUP_append]
    cases h : ALOOKUP m1 mn with
    | some env1 =>
      simp only [Option.some_or]
      constructor
      · intro h2
        exact ⟨h2, Or.inr ⟨[mn], p, env1, by simp, by simp,
          by simp [h, nsLookupMod]⟩⟩
      · intro h2; exact h2.1
    | none =>
      simp only [Option.none_or, true_and]
      constructor
      · intro h2; exact Or.inl h2
      · rintro (h2 | ⟨p1, p2, e3, hp, he, h3⟩)
        · exact h2
        · cases p1 with
          | nil => exact absurd rfl hp
          | cons a p1' =>
            simp at he; obtain ⟨rfl, _⟩ := he
            simp [nsLookupMod_Bind_cons, h] at h3
/- HOL4: Theorem eALL_T[simp] -/
theorem eALL_T {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v), nsAll (fun (_n : cml_id m n) (_x : v) => True) e := by
  intro e id_ x _; trivial
/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (env : «namespace» m n v) (x : cml_id m n) (P : cml_id m n → v → Prop) (val_ : v),
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ := by
  intro env x P val_ ⟨h1, h2⟩; exact h1 _ _ h2
/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  intro f e1 e2 ⟨h1, h2⟩ id_ v hl
  rcases (nsLookup_nsAppend_some e1 id_ e2 v).1 hl with h | ⟨_, h, _⟩
  · exact h1 _ _ h
  · exact h2 _ _ h
/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := by
  intro R l hl id_ v hlook
  cases id_ with
  | Short x =>
    simp only [alist_to_ns, nsLookup] at hlook
    exact hl _ (ALOOKUP_mem hlook)
  | Long mn i => simp [alist_to_ns, nsLookup, ALOOKUP] at hlook
/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := by
  intro R mn e
  constructor
  · intro h id_ v hl
    apply h (.Long mn id_) v
    rw [nsLookup_nsLift]; simpa using hl
  · intro h id_ v hl
    rw [nsLookup_nsLift] at hl
    cases id_ with
    | Short x => cases hl
    | Long mn' i =>
      simp only at hl
      split at hl
      · rename_i heq; simp at heq; subst heq; exact h _ _ hl
      · cases hl
/- HOL4: Theorem nsAll_nsAppend_left -/
theorem nsAll_nsAppend_left {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (n1 n2 : «namespace» m n v),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intro P n1 n2 h id_ v hl
  exact h _ _ ((nsLookup_nsAppend_some n1 id_ n2 v).2 (Or.inl hl))
/- HOL4: Theorem nsSub_conj -/
theorem nsSub_conj {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop) (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsSub (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  intro P Q e1 e2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun id_ v hl => ?_, h2⟩, ⟨fun id_ v hl => ?_, h2⟩⟩
    · obtain ⟨v2, h, hp, _⟩ := h1 id_ v hl; exact ⟨v2, h, hp⟩
    · obtain ⟨v2, h, _, hq⟩ := h1 id_ v hl; exact ⟨v2, h, hq⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, _⟩⟩
    refine ⟨fun id_ v hl => ?_, h2⟩
    obtain ⟨v2, h, hp⟩ := h1 id_ v hl
    obtain ⟨v2', h', hq⟩ := h3 id_ v hl
    rw [h] at h'; cases h'
    exact ⟨v2, h, hp, hq⟩
/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := by
  intro P R hPR e hall
  exact ⟨fun id_ v h => ⟨v, h, hPR _ _ (hall _ _ h)⟩, fun _ h => h⟩
/- HOL4: Theorem nsSub_nsBind -/
theorem nsSub_nsBind {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsSub R e1 e2 →
        nsSub R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
  intro R x v1_ v2_ e1 e2 ⟨hr, h1, h2⟩
  refine ⟨fun id_ v hl => ?_, fun path h => ?_⟩
  · by_cases hid : id_ = .Short x
    · subst hid
      rw [nsLookup_nsBind.1] at hl; cases hl
      exact ⟨v2_, nsLookup_nsBind.1 _ _ _, hr⟩
    · rw [nsLookup_nsBind.2 _ _ _ _ hid] at hl
      obtain ⟨v2, h, hr'⟩ := h1 _ _ hl
      exact ⟨v2, by rw [nsLookup_nsBind.2 _ _ _ _ hid]; exact h, hr'⟩
  · cases path with
    | nil => cases e2; simp [nsBind, nsLookupMod] at h
    | cons mn p =>
      rw [nsLookupMod_nsBind _ _ _ _ (by simp)] at h ⊢
      exact h2 _ h
/- HOL4: Theorem nsSub_nsAppend2 -/
theorem nsSub_nsAppend2 {m n v_ : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v_ → v_ → Prop)
      (e1 : «namespace» m n v_) (e2 : «namespace» m n v_) (e2' : «namespace» m n v_),
      nsSub R e1 e1 ∧ nsSub R e2 e2' →
        nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  intro R e1 e2 e2' ⟨h1, h2⟩
  refine ⟨fun id_ v hl => ?_, fun path h => ?_⟩
  · rcases (nsLookup_nsAppend_some e1 id_ e2 v).1 hl with h | ⟨hn, h, hp⟩
    · obtain ⟨v', h', hr⟩ := h1.1 _ _ h
      exact ⟨v', (nsLookup_nsAppend_some e1 id_ e2' v').2 (Or.inl h'), hr⟩
    · obtain ⟨v', h', hr⟩ := h2.1 _ _ h
      exact ⟨v', (nsLookup_nsAppend_some e1 id_ e2' v').2 (Or.inr ⟨hn, h', hp⟩), hr⟩
  · rw [nsLookupMod_nsAppend_none] at h ⊢
    obtain ⟨ha, hb⟩ := h
    refine ⟨ha, ?_⟩
    rcases hb with hb | hb
    · exact Or.inl (h2.2 _ hb)
    · exact Or.inr hb
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
  | cons k1 keys ih =>
    simp only [alist_rel_restr]
    constructor
    · intro h k_ hk
      simp [MEM] at hk
      split at h
      · exact h.elim
      · rename_i v1 hv1
        split at h
        · exact h.elim
        · rename_i v2 hv2
          rcases hk with rfl | hk
          · exact ⟨v1, v2, hv1, hv2, h.1⟩
          · exact ih.1 h.2 k_ (by simp [MEM]; exact hk)
    · intro h
      obtain ⟨v1, v2, hv1, hv2, hr⟩ := h k1 (by simp [MEM])
      rw [hv1]; simp only [hv2]
      exact ⟨hr, ih.2 fun k_ hk => h k_ (by simp [MEM] at hk ⊢; exact Or.inr hk)⟩
/- HOL4: Theorem alistSub_cong -/
theorem alistSub_cong {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (l1 l1' : List (k × v1)) (l2 l2' : List (k × v2))
      (R R' : k → v1 → v2 → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ (n_ : k) (x : v1) (y : v2),
          ALOOKUP l1' n_ = some x ∧ ALOOKUP l2' n_ = some y → R n_ x y = R' n_ x y) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  intro l1 l1' l2 l2' R R' ⟨rfl, rfl, h⟩
  unfold alistSub
  rw [alist_rel_restr_thm, alist_rel_restr_thm]
  constructor
  · intro H k_ hk
    obtain ⟨a, b, ha, hb, hr⟩ := H k_ hk
    exact ⟨a, b, ha, hb, (h _ _ _ ⟨ha, hb⟩) ▸ hr⟩
  · intro H k_ hk
    obtain ⟨a, b, ha, hb, hr⟩ := H k_ hk
    exact ⟨a, b, ha, hb, (h _ _ _ ⟨ha, hb⟩).symm ▸ hr⟩
/- HOL4: Theorem nsLookup_FOLDR_nsLift -/
theorem nsLookup_FOLDR_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (k : n),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (cml_id.Short k) := by
  intro e p k
  induction p with
  | nil => rfl
  | cons a p ih =>
    show nsLookup (nsLift a (FOLDR nsLift e p)) (.Long a (mk_id p k)) = _
    rw [nsLookup_nsLift]; simpa using ih
/- HOL4: Theorem nsLookup_FOLDR_nsLift_some -/
theorem nsLookup_FOLDR_nsLift_some {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (id_ : cml_id m n) (val_ : v),
      nsLookup (FOLDR nsLift e p) id_ = some val_ ↔
        (p = [] ∧ nsLookup e id_ = some val_) ∨
        (p ≠ [] ∧ ∃ (p2 : List m) (n_ : n),
          id_ = mk_id (p ++ p2) n_ ∧ nsLookup e (mk_id p2 n_) = some val_) := by
  intro e p
  induction p with
  | nil => intro id_ val_; simp [FOLDR]
  | cons a p ih =>
    intro id_ val_
    show nsLookup (nsLift a (FOLDR nsLift e p)) id_ = some val_ ↔ _
    rw [nsLookup_nsLift]
    simp only [ne_eq, reduceCtorEq, false_and, not_false_eq_true, true_and, false_or,
      List.cons_append]
    cases id_ with
    | Short x => simp [mk_id]
    | Long mn i =>
      simp only
      by_cases ha : a = mn
      · subst ha
        simp only [beq_self_eq_true, if_true, mk_id, cml_id.Long.injEq, true_and]
        rw [ih]
        constructor
        · rintro (⟨rfl, h⟩ | ⟨_, p2, n_, rfl, h⟩)
          · obtain ⟨p2, n_, rfl⟩ := mk_id_surj i
            exact ⟨p2, n_, by simp, h⟩
          · exact ⟨p2, n_, rfl, h⟩
        · rintro ⟨p2, n_, rfl, h⟩
          by_cases hp : p = []
          · subst hp; exact Or.inl ⟨rfl, h⟩
          · exact Or.inr ⟨hp, p2, n_, rfl, h⟩
      · have : (a == mn) = false := by simp [ha]
        simp only [this, Bool.false_eq_true, if_false, reduceCtorEq, false_iff, not_exists,
          not_and, mk_id, cml_id.Long.injEq]
        intro p2 n_ h; exact absurd h.1.symm ha
/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none -/
theorem nsLookupMod_FOLDR_nsLift_none {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (e : «namespace» m n v) (p1 p2 : List m),
      nsLookupMod (FOLDR nsLift e p1) p2 = none ↔
        (IS_PREFIX p1 p2 = true ∨ IS_PREFIX p2 p1 = true) →
          ∃ (p3 : List m), p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := by
  intro e p1
  induction p1 with
  | nil =>
    intro p2
    simp [FOLDR, IS_PREFIX]
  | cons a p1 ih =>
    intro p2
    show nsLookupMod (nsLift a (FOLDR nsLift e p1)) p2 = none ↔ _
    rw [nsLookupMod_nsLift]
    cases p2 with
    | nil => simp [IS_PREFIX]
    | cons b p2 =>
      simp only
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, if_true]
        rw [ih]
        simp [IS_PREFIX, List.isPrefixOf]
      · have : (a == b) = false := by simp [hab]
        simp only [this, Bool.false_eq_true, if_false, true_iff]
        intro h
        simp [IS_PREFIX, List.isPrefixOf, hab, Ne.symm hab] at h
/- HOL4: Theorem nsAll2_conj -/
theorem nsAll2_conj {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  intro P Q e1 e2
  unfold nsAll2
  rw [nsSub_conj, nsSub_conj (fun x y z => P x z y) (fun x y z => Q x z y)]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, c⟩, ⟨b, d⟩⟩
  · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; exact ⟨⟨a, b⟩, ⟨c, d⟩⟩
/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
  intro R e1 e2 n_ v2_ ⟨hl, _, h2⟩
  exact h2.1 _ _ hl
/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
  intro R e1 e2 n_ ⟨h1, h2⟩
  constructor
  · intro hn
    cases h : nsLookup e2 n_ with
    | none => rfl
    | some v2 =>
      obtain ⟨v1, hv1, _⟩ := h2.1 _ _ h
      rw [hn] at hv1; cases hv1
  · intro hn
    cases h : nsLookup e1 n_ with
    | none => rfl
    | some v1 =>
      obtain ⟨v2, hv2, _⟩ := h1.1 _ _ h
      rw [hn] at hv2; cases hv2
/- HOL4: Theorem nsAll2_nsBind -/
theorem nsAll2_nsBind {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
  intro R x v1_ v2_ e1 e2 ⟨hr, h1, h2⟩
  exact ⟨nsSub_nsBind _ _ _ _ _ _ ⟨hr, h1⟩, nsSub_nsBind _ _ _ _ _ _ ⟨hr, h2⟩⟩
/- HOL4: Theorem nsAll2_nsBindList -/
theorem nsAll2_nsBindList {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (l1 : List (n × v1)) (l2 : List (n × v2))
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 ∧
      nsAll2 R e1 e2 →
        nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  intro R l1 l2 e1 e2 ⟨hl, he⟩
  induction hl with
  | nil => exact he
  | cons x y xs ys hxy _ ih =>
    obtain ⟨hk, hr⟩ := hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    simp only at hk hr; subst hk
    exact nsAll2_nsBind R a b d _ _ ⟨hr, ih⟩
theorem nsSub_nsAppend_of_nsAll2 {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    (R : cml_id m n → v1 → v2 → Prop)
    (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
    (e1' : «namespace» m n v1) (e2' : «namespace» m n v2)
    (h : nsAll2 R e1 e2) (h' : nsSub R e1' e2') :
    nsSub R (nsAppend e1 e1') (nsAppend e2 e2') := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun id_ v hl => ?_, fun path hp => ?_⟩
  · rcases (nsLookup_nsAppend_some e1 id_ e1' v).1 hl with hx | ⟨hn, hx, hpre⟩
    · obtain ⟨w, hw, hr⟩ := h1.1 _ _ hx
      exact ⟨w, (nsLookup_nsAppend_some e2 id_ e2' w).2 (Or.inl hw), hr⟩
    · obtain ⟨w, hw, hr⟩ := h'.1 _ _ hx
      refine ⟨w, (nsLookup_nsAppend_some e2 id_ e2' w).2 (Or.inr ⟨?_, hw, ?_⟩), hr⟩
      · cases hz : nsLookup e2 id_ with
        | none => rfl
        | some z =>
          obtain ⟨y, hy, _⟩ := h2.1 _ _ hz
          rw [hn] at hy; cases hy
      · intro p1 p2 hpp
        exact h2.2 _ (hpre p1 p2 hpp)
  · rw [nsLookupMod_nsAppend_none] at hp ⊢
    obtain ⟨ha, hb⟩ := hp
    refine ⟨h1.2 _ ha, ?_⟩
    rcases hb with hb | ⟨p1, p2, e3, hne, hpath, h3⟩
    · exact Or.inl (h'.2 _ hb)
    · cases hz : nsLookupMod e1 p1 with
      | none => have := h2.2 _ hz; rw [h3] at this; cases this
      | some e4 => exact Or.inr ⟨p1, p2, e4, hne, hpath, hz⟩

/- HOL4: Theorem nsAll2_nsAppend -/
theorem nsAll2_nsAppend {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
      (e1' : «namespace» m n v1) (e2' : «namespace» m n v2),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
        nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  intro R e1 e2 e1' e2' ⟨h, h'⟩
  refine ⟨nsSub_nsAppend_of_nsAll2 R e1 e2 e1' e2' h h'.1, ?_⟩
  exact nsSub_nsAppend_of_nsAll2 (fun x y z => R x z y) e2 e1 e2' e1' ⟨h.2, h.1⟩ h'.2
/- HOL4: Theorem nsAll2_alist_to_ns -/
theorem nsAll2_alist_to_ns {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (l1 : List (n × v1)) (l2 : List (n × v2)),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 →
        nsAll2 R (alist_to_ns l1 : «namespace» m n v1) (alist_to_ns l2 : «namespace» m n v2) := by
  intro R l1 l2 hl
  induction hl with
  | nil => exact nsAll2_nsEmpty R
  | cons x y xs ys hxy _ ih =>
    obtain ⟨hk, hr⟩ := hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    simp only at hk hr; subst hk
    rw [alist_to_ns_cons, alist_to_ns_cons]
    exact nsAll2_nsBind R a b d _ _ ⟨hr, ih⟩
/- HOL4: Theorem nsAll2_nsLift[simp] -/
theorem nsAll2_nsLift {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (mn : m)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
        nsAll2 (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := by
  intro R mn e1 e2
  have key : ∀ {w1 w2 : Type} (S : cml_id m n → w1 → w2 → Prop)
      (f1 : «namespace» m n w1) (f2 : «namespace» m n w2),
      nsSub S (nsLift mn f1) (nsLift mn f2) ↔
        nsSub (fun id_ => S (cml_id.Long mn id_)) f1 f2 := by
    intro w1 w2 S f1 f2
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun id_ v hl => ?_, fun path hp => ?_⟩
      · obtain ⟨w, hw, hr⟩ := h1 (.Long mn id_) v (by rw [nsLookup_nsLift]; simpa using hl)
        rw [nsLookup_nsLift] at hw; simp at hw
        exact ⟨w, hw, hr⟩
      · have := h2 (mn :: path) (by rw [nsLookupMod_nsLift]; simpa using hp)
        rw [nsLookupMod_nsLift] at this; simpa using this
    · rintro ⟨h1, h2⟩
      refine ⟨fun id_ v hl => ?_, fun path hp => ?_⟩
      · rw [nsLookup_nsLift] at hl
        cases id_ with
        | Short x => cases hl
        | Long mn' i =>
          simp only at hl
          split at hl
          · rename_i heq; simp at heq; subst heq
            obtain ⟨w, hw, hr⟩ := h1 _ _ hl
            exact ⟨w, by rw [nsLookup_nsLift]; simpa using hw, hr⟩
          · cases hl
      · rw [nsLookupMod_nsLift] at hp ⊢
        cases path with
        | nil => cases hp
        | cons mn' p =>
          simp only at hp ⊢
          split at hp
          · rename_i heq; simp at heq; subst heq; simpa using h2 _ hp
          · rename_i heq; simp [heq]
  unfold nsAll2
  rw [key, key]

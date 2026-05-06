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
  | Short x => rfl
  | Long mn id ih => simp [id_to_mods, id_to_n, mk_id, ih]
/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {m n : Type} :
    ∀ (id : cml_id m n), ∃ (p : List m) (n_ : n), id = mk_id p n_ :=
  fun id => ⟨id_to_mods id, id_to_n id, (mk_id_thm id).symm⟩
/- HOL4: Theorem nsSub_mono[mono] -/
theorem nsSub_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  intro hmono ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  intro id_ v1_ hlk
  obtain ⟨v2_, hlk2, hr⟩ := h1 id_ v1_ hlk
  exact ⟨v2_, hlk2, hmono _ _ _ hr⟩
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
  cases id <;> rfl
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none :=
  fun _ _ => rfl
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env
  cases env
  refine ⟨?_, ?_⟩ <;> simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := rfl
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  refine ⟨?_, ?_⟩
  · intro id_ v1_ hlk
    cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at hlk
  · intro path
    cases path with
    | nil => simp [nsLookupMod]
    | cons x xs => intro _; rfl
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id_ val_ hlk
  cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at hlk
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := by
  intro f
  exact ⟨nsSub_nsEmpty f _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) :=
  fun _ _ _ => rfl
/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intro k val_ e1 e2
  cases e1 <;> cases e2 <;> simp [nsAppend, nsBind]
/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3
  cases e1 <;> cases e2 <;> cases e3 <;> simp [nsAppend, List.append_assoc]
/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  refine ⟨?_, ?_⟩
  · intro n_ val_ e
    cases e; simp [nsLookup, nsBind, ALOOKUP]
  · intro id_ n_ val_ e hne
    cases e with
    | Bind vs ms =>
      cases id_ with
      | Short k =>
        have hne' : k ≠ n_ := fun h => hne (by rw [h])
        simp [nsLookup, nsBind, ALOOKUP]
        intro h; exact absurd h.symm hne'
      | Long mn id' => rfl
/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intro n_ x e
  cases e
  simp [nsAppend, nsSing, nsBind]
/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [BEq n] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := sorry
/- HOL4: Theorem nsAll_nsSing[simp] -/
theorem nsAll_nsSing {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (n_ : n) (val_ : v),
      nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := by
  intro R n_ val_
  constructor
  · intro h
    apply h
    simp [nsLookup, nsSing, ALOOKUP]
  · intro hR id_ val'
    cases id_ with
    | Short k =>
      simp only [nsLookup, nsSing, ALOOKUP]
      by_cases h : k = n_
      · subst h; simp; intro hv; subst hv; exact hR
      · simp [h]
        intro hh; exact absurd hh.symm h
    | Long mn id' =>
      simp only [nsLookup, nsSing, ALOOKUP]
      intro h; cases h
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
  cases ns; cases ns'
  simp [nsBind]
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, hvs⟩, hms⟩; exact ⟨hx, hy, hvs, hms⟩
  · rintro ⟨hx, hy, hvs, hms⟩; exact ⟨⟨⟨hx, hy⟩, hvs⟩, hms⟩
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
  | nil => exact (nsAppend_nsEmpty e).2
  | cons hd tl ih =>
    obtain ⟨k, val_⟩ := hd
    rw [alist_to_ns_cons, nsAppend_nsBind, ih]
    rfl
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
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ :=
  fun _ x _ val_ ⟨h, hlk⟩ => h x val_ hlk
/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := sorry
/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := sorry
/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift {m n v : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := sorry
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
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨⟨?_, h2⟩, ⟨?_, h2⟩⟩
    · intro id_ v1_ hlk
      obtain ⟨v2_, hlk2, hp, _⟩ := h1 id_ v1_ hlk
      exact ⟨v2_, hlk2, hp⟩
    · intro id_ v1_ hlk
      obtain ⟨v2_, hlk2, _, hq⟩ := h1 id_ v1_ hlk
      exact ⟨v2_, hlk2, hq⟩
  · intro ⟨⟨h1, hm⟩, ⟨h2, _⟩⟩
    refine ⟨?_, hm⟩
    intro id_ v1_ hlk
    obtain ⟨v2_, hlk2, hp⟩ := h1 id_ v1_ hlk
    obtain ⟨v2_', hlk2', hq⟩ := h2 id_ v1_ hlk
    rw [hlk2] at hlk2'
    cases hlk2'
    exact ⟨v2_, hlk2, hp, hq⟩
/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl {m n v : Type} [BEq m] [BEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := by
  intro P R hpr e hp
  refine ⟨?_, fun _ h => h⟩
  intro id_ v_ hlk
  exact ⟨v_, hlk, hpr id_ v_ (hp id_ v_ hlk)⟩
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
  rw [nsSub_conj P Q e1 e2]
  rw [nsSub_conj (fun x y z => P x z y) (fun x y z => Q x z y) e2 e1]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, c⟩, ⟨b, d⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, c⟩, ⟨b, d⟩⟩
/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
  intro R e1 e2 n_ v2_ ⟨hlk, ⟨_, ⟨h21, _⟩⟩⟩
  obtain ⟨v1_, hlk1, hr⟩ := h21 n_ v2_ hlk
  exact ⟨v1_, hlk1, hr⟩
/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
  intro R e1 e2 n_ ⟨⟨h12, _⟩, ⟨h21, _⟩⟩
  constructor
  · intro h1
    cases hh : nsLookup e2 n_ with
    | none => rfl
    | some v2_ =>
      exfalso
      obtain ⟨v1_, hlk, _⟩ := h21 n_ v2_ hh
      rw [h1] at hlk; cases hlk
  · intro h2
    cases hh : nsLookup e1 n_ with
    | none => rfl
    | some v1_ =>
      exfalso
      obtain ⟨v2_, hlk, _⟩ := h12 n_ v1_ hh
      rw [h2] at hlk; cases hlk
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

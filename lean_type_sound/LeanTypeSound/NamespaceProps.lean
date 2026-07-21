/-
  Translation of namespacePropsScript.sml
  Proofs about the namespace datatype.
-/
import Mathlib
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
  intro id; induction id with
  | Short x => simp [mk_id, id_to_mods, id_to_n]
  | Long mn i ih => simp [mk_id, id_to_mods, id_to_n, ih]
/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {m n : Type} :
    ∀ (id : cml_id m n), ∃ (p : List m) (n_ : n), id = mk_id p n_ := by
  intro id; induction id with
  | Short x => exact ⟨[], x, rfl⟩
  | Long mn i ih =>
    obtain ⟨p, n_, rfl⟩ := ih
    exact ⟨mn :: p, n_, by simp [mk_id]⟩

/-
HOL4: Theorem nsSub_mono[mono]
-/
theorem nsSub_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
      intro hR h;
      exact ⟨ fun x y hxy => by obtain ⟨ z, hz ⟩ := h.1 x y hxy; exact ⟨ z, hz.1, hR _ _ _ hz.2 ⟩, h.2 ⟩

/-
HOL4: Theorem nsAll2_mono[mono]
-/
theorem nsAll2_mono {m n v1 v2 : Type} [BEq m] [BEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
      exact fun h1 h2 => ⟨ nsSub_mono h1 h2.1, nsSub_mono ( fun x y z h3 => h1 x z y h3 ) h2.2 ⟩

/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
theorem nsLookup_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (id : cml_id m n), nsLookup (nsEmpty : «namespace» m n v) id = none := by
  intro id; cases id <;> simp [nsLookup, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none := by
  intro x y; simp [nsLookupMod, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env; cases env with | Bind v m => simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := by
  simp [alist_to_ns, nsEmpty]
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  constructor
  · intro id_ v1_ h; cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at h
  · intro path h; cases path with
    | nil => simp [nsLookupMod] at h
    | cons x xs => simp [nsLookupMod, nsEmpty, ALOOKUP]
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty {m n v : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id_ val_ h; cases id_ <;> simp [nsLookup, nsEmpty, ALOOKUP] at h
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [BEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := by
  intro f; exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) := by
  intro k val_ l; simp [alist_to_ns, nsBind]
/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intro k val_ e1 e2
  cases e1 with | Bind v1 m1 => cases e2 with | Bind v2 m2 =>
    simp [nsBind, nsAppend]
/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3
  cases e1 with | Bind v1 m1 => cases e2 with | Bind v2 m2 => cases e3 with | Bind v3 m3 =>
    simp [nsAppend, List.append_assoc]

/-
HOL4: Theorem nsLookup_nsBind[simp]
-/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] [LawfulBEq m] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
        constructor;
        · intros n_ val_ e
          unfold nsLookup nsBind;
          cases e ; simp +decide [ ALOOKUP ];
        · rintro id_ n_ val_ e h;
          cases id_ <;> simp_all +decide [ nsBind ];
          · cases e ; simp_all +decide [ nsLookup ];
            unfold ALOOKUP; aesop;
          · cases e ; simp +decide [ nsLookup ]

/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intro n_ x e; cases e with | Bind v1 m1 => simp [nsSing, nsAppend, nsBind]

/-
HOL4: Theorem nsLookup_nsSing[simp]
-/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := by
          intro n_ val_ id_;
          induction' id_ with m id_ ih;
          · unfold nsLookup nsSing;
            unfold ALOOKUP;
            convert rfl;
            exact?;
          · exact?

/-
HOL4: Theorem nsAll_nsSing[simp]
-/
theorem nsAll_nsSing {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (n_ : n) (val_ : v),
      nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := by
        unfold nsAll
        simp [nsSing];
        intro R n_ val_;
        constructor <;> intro h;
        · convert h _ _ _;
          convert nsLookup_nsBind.1 n_ val_ _;
          rotate_right;
          exact nsEmpty;
          · exact?;
          · infer_instance;
        · unfold nsLookup;
          rintro ( _ | _ ) <;> simp +decide [ ALOOKUP ];
          aesop

/-
HOL4: Theorem nsAll2_nsSing[simp]
-/
theorem nsAll2_nsSing {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (n1 : n) (v1_ : v1) (n2 : n) (v2_ : v2),
      nsAll2 R (nsSing n1 v1_ : «namespace» m n v1) (nsSing n2 v2_ : «namespace» m n v2) ↔
        n1 = n2 ∧ R (cml_id.Short n1) v1_ v2_ := by
          -- By definition of nsAll2, we can split the goal into two parts: the components are equal and the relation holds.
          intro R n1 v1_ n2 v2_
          simp [nsAll2];
          constructor <;> intro h;
          · have := h.1.1 ( cml_id.Short n1 ) v1_;
            unfold nsLookup at this; simp_all +decide [ nsSing ] ;
            unfold ALOOKUP at this; simp_all +decide [ BEq.beq ] ;
            unfold ALOOKUP at this; simp_all +decide [ BEq.beq ] ;
          · unfold nsSub;
            unfold nsLookup nsLookupMod; simp_all +decide [ nsSing ] ;
            constructor;
            · constructor;
              · rintro ( _ | _ ) <;> simp +decide [ ALOOKUP ];
                grind;
              · rintro ( _ | ⟨ mn, path ⟩ ) <;> simp +decide [ ALOOKUP ];
            · constructor;
              · rintro ( _ | _ ) <;> simp +decide [ ALOOKUP ];
                grind;
              · rintro ( _ | ⟨ mn, path ⟩ ) <;> simp +decide [ ALOOKUP ]

/-
HOL4: Theorem nsBind_11[simp]
-/
theorem nsBind_11 {m n v : Type} :
    ∀ (x : n) (y : v) (ns : «namespace» m n v) (x' : n) (y' : v) (ns' : «namespace» m n v),
      nsBind x y ns = nsBind x' y' ns' ↔ x = x' ∧ y = y' ∧ ns = ns' := by
        intros x y ns x' y' ns';
        constructor;
        · cases ns ; cases ns' ; simp_all +decide [ nsBind ];
        · grind +revert

/- HOL4: Theorem alist_to_ns_11[simp] -/
theorem alist_to_ns_11 {m n v : Type} :
    ∀ (l1 l2 : List (n × v)),
      (alist_to_ns l1 : «namespace» m n v) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2; simp [alist_to_ns, «namespace».Bind.injEq]

/-
HOL4: Theorem nsLookup_nsLift
-/
theorem nsLookup_nsLift {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (mn : m) (e : «namespace» m n v) (id_ : cml_id m n),
      nsLookup (nsLift mn e) id_ =
        match id_ with
        | cml_id.Long mn' id' => if mn == mn' then nsLookup e id' else none
        | cml_id.Short _ => none := by
          intros mn e id_;
          cases id_ <;> simp +decide [ nsLift ];
          · unfold nsLookup; aesop;
          · rw [nsLookup];
            split_ifs <;> simp_all +decide [ ALOOKUP ]

/-
HOL4: Theorem nsLookupMod_nsLift
-/
theorem nsLookupMod_nsLift {m n v : Type} [BEq m] :
    ∀ (mn : m) (e : «namespace» m n v) (path : List m),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn == mn' then nsLookupMod e path' else none := by
          unfold nsLift;
          intro mn e path;
          cases path <;> simp +decide [ nsLookupMod ];
          rw [ ALOOKUP ];
          split_ifs <;> rfl

/-
HOL4: Theorem nsLookup_nsAppend_some
-/
theorem nsLookup_nsAppend_some {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (e1 : «namespace» m n v) (id_ : cml_id m n) (e2 : «namespace» m n v) (val_ : v),
      nsLookup (nsAppend e1 e2) id_ = some val_ ↔
        nsLookup e1 id_ = some val_ ∨
        (nsLookup e1 id_ = none ∧ nsLookup e2 id_ = some val_ ∧
         ∀ (p1 p2 : List m), p1 ≠ [] ∧ id_to_mods id_ = p1 ++ p2 →
           nsLookupMod e1 p1 = none) := by
             intros e1 id_ e2 val_;
             induction' id_ with mn i ih generalizing e1 e2;
             · cases e1 ; cases e2 ; simp +decide [ nsLookup, nsAppend ];
               have h_alookup_append : ∀ (l1 l2 : List (n × v)) (mn : n) (val_ : v), ALOOKUP (l1 ++ l2) mn = some val_ ↔ ALOOKUP l1 mn = some val_ ∨ ALOOKUP l1 mn = none ∧ ALOOKUP l2 mn = some val_ := by
                 intros l1 l2 mn val_;
                 induction' l1 with l1 ih generalizing mn val_ <;> simp_all +decide [ ALOOKUP ];
                 grind;
               simp +decide [ id_to_mods ];
               grind;
             · cases e1 ; cases e2 ; simp +decide [ nsLookup, nsAppend ];
               rename_i k l;
               rename_i a b;
               rename_i h;
               rw [ show ALOOKUP ( b ++ l ) i = match ALOOKUP b i with | none => ALOOKUP l i | some env => some env from ?_ ];
               · cases h : ALOOKUP b i <;> cases h' : ALOOKUP l i <;> simp +decide [ h, h' ];
                 · intro h'' p1 p2 hp1 hp2;
                   rcases p1 with ( _ | ⟨ mn, p1 ⟩ ) <;> simp_all +decide [ id_to_mods ];
                   unfold nsLookupMod; aesop;
                 · intro h₁ h₂ h₃; specialize h₃ [ i ] ( id_to_mods ih ) ; simp_all +decide ;
                   unfold nsLookupMod at h₃; simp_all +decide [ ALOOKUP ] ;
                   exact absurd ( h₃ rfl ) ( by unfold nsLookupMod; aesop );
               · have h_append : ∀ (l1 l2 : List (m × «namespace» m n v)) (i : m), ALOOKUP (l1 ++ l2) i = match ALOOKUP l1 i with | none => ALOOKUP l2 i | some env => some env := by
                   intros l1 l2 i; induction' l1 with l1 ih generalizing l2 i; simp +decide [ ALOOKUP ] ;
                   simp +decide [ ALOOKUP ];
                   grind;
                 exact h_append b l i

/-
HOL4: Theorem nsAppend_to_nsBindList
-/
theorem nsAppend_to_nsBindList {m n v : Type} :
    ∀ (l : List (n × v)) (e : «namespace» m n v),
      nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l e
  induction l with
  | nil => cases e with | Bind v1 m1 => simp [alist_to_ns, nsAppend, nsBindList, nsEmpty]
  | cons p ps ih =>
    simp [alist_to_ns, nsBindList, nsBind]
    cases e with | Bind v1 m1 =>
      simp [nsAppend, nsBind, nsBindList]
      convert congr_arg _ ?_;
      rotate_left;
      exact m1;
      · rfl;
      · exact?

/-
need to unfold foldr carefully

HOL4: Theorem nsLookupMod_nsAppend_none
-/
theorem nsLookupMod_nsAppend_none {m n v : Type} [BEq m] :
    ∀ (e1 e2 : «namespace» m n v) (path : List m),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
         (nsLookupMod e2 path = none ∨
          ∃ (p1 p2 : List m) (e3 : «namespace» m n v),
            p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
              -- To prove the equivalence, we first unfold the definition of nsAppend.
              intros e1 e2 path
              cases' e1 with val1 mods1
              cases' e2 with val2 mods2
              simp [nsAppend];
              induction' path with mn path ih generalizing mods1 mods2;
              · simp +decide [ nsLookupMod ];
              · -- By definition of `nsLookupMod`, we can split into cases based on whether `mn` is in `mods1` or `mods2`.
                by_cases hmn : ∃ e1, ALOOKUP mods1 mn = some e1;
                · obtain ⟨ e1, he1 ⟩ := hmn; simp_all +decide [ nsLookupMod ] ;
                  rw [ show ALOOKUP ( mods1 ++ mods2 ) mn = some e1 from ?_ ];
                  · cases h : ALOOKUP mods2 mn <;> simp +decide [ h ];
                    intro h';
                    refine Or.inr ⟨ [ mn ], by simp +decide, ⟨ path, by simp +decide ⟩, e1, ?_ ⟩;
                    unfold nsLookupMod; aesop;
                  · induction mods1 <;> simp_all +decide [ ALOOKUP ];
                    grind;
                · rw [ nsLookupMod, nsLookupMod, nsLookupMod ];
                  rw [ show ALOOKUP ( mods1 ++ mods2 ) mn = ALOOKUP mods2 mn from ?_ ];
                  · cases h : ALOOKUP mods1 mn <;> cases h' : ALOOKUP mods2 mn <;> simp +decide [ h, h' ] at hmn ⊢;
                    rintro ( _ | ⟨ mn', path' ⟩ ) <;> simp_all +decide [ List.append_eq_cons_iff ];
                    unfold nsLookupMod; aesop;
                  · have h_lookup_mods : ∀ (mods : List (m × «namespace» m n v)), ALOOKUP mods mn = none → ALOOKUP (mods ++ mods2) mn = ALOOKUP mods2 mn := by
                      intros mods hmods; induction' mods with mods ih <;> simp_all +decide [ ALOOKUP ] ;
                      grind;
                    exact h_lookup_mods mods1 ( by cases h : ALOOKUP mods1 mn <;> tauto )

/- HOL4: Theorem eALL_T[simp] -/
theorem eALL_T {m n v : Type} [BEq m] [BEq n] :
    ∀ (e : «namespace» m n v), nsAll (fun (_n : cml_id m n) (_x : v) => True) e := by
  intro e id_ val_ h; trivial
/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll {m n v : Type} [BEq m] [BEq n] :
    ∀ (env : «namespace» m n v) (x : cml_id m n) (P : cml_id m n → v → Prop) (val_ : v),
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ := by
  intro env x P val_ ⟨hall, hlookup⟩; exact hall x val_ hlookup

/-
HOL4: Theorem nsAll_nsAppend
-/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
        -- Let's unfold the definition of `nsAll`.
        unfold nsAll;
        grind +suggestions

/-
depends on nsLookup_nsAppend_some

HOL4: Theorem nsAll_alist_to_ns
-/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := by
          intro R l hl;
          intro x y;
          induction' l with p l ih generalizing x y;
          · cases x <;> tauto;
          · rw [ alist_to_ns_cons ];
            by_cases hx : x = cml_id.Short p.1 <;> simp_all +decide [ nsLookup_nsBind ];
            grind

/-
HOL4: Theorem nsAll_nsLift[simp]
-/
theorem nsAll_nsLift {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := by
        intro R mn e;
        constructor <;> intro h;
        · intro id_ val_ hval_;
          convert h ( cml_id.Long mn id_ ) val_ _;
          rw [ nsLookup_nsLift ];
          grind;
        · intro id_ val_ h_id_val
          rw [nsLookup_nsLift] at h_id_val;
          cases id_ <;> aesop

/-
HOL4: Theorem nsAll_nsAppend_left
-/
theorem nsAll_nsAppend_left {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (n1 n2 : «namespace» m n v),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
        intros P n1 n2 h_append
        unfold nsAll at h_append;
        exact fun id_ val_ h => h_append id_ val_ ( by
          rw [nsLookup_nsAppend_some];
          exact Or.inl h )

/-
HOL4: Theorem nsSub_conj
-/
theorem nsSub_conj {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop) (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsSub (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
          unfold nsSub;
          grind

/-
HOL4: Theorem nsSub_refl
-/
theorem nsSub_refl {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := by
          intros P R hR e he;
          constructor <;> intros <;> aesop

/-
HOL4: Theorem nsSub_nsBind
-/
theorem nsSub_nsBind {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsSub R e1 e2 →
        nsSub R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
          intros R x v1_ v2_ e1 e2 hR;
          constructor;
          · intro id_ v1__1 h;
            by_cases h' : id_ = cml_id.Short x;
            · have h' : nsLookup (nsBind x v1_ e1) (cml_id.Short x) = some v1_ := by
                exact nsLookup_nsBind.1 x v1_ e1;
              have h'' : nsLookup (nsBind x v2_ e2) (cml_id.Short x) = some v2_ := by
                exact nsLookup_nsBind.1 _ _ _;
              grind;
            · have h_lookup : nsLookup (nsBind x v1_ e1) id_ = nsLookup e1 id_ ∧ nsLookup (nsBind x v2_ e2) id_ = nsLookup e2 id_ := by
                exact ⟨ nsLookup_nsBind.2 id_ x v1_ e1 h', nsLookup_nsBind.2 id_ x v2_ e2 h' ⟩;
              have := hR.2.1 id_ v1__1; aesop;
          · intros path hpath
            cases' path with mn path';
            · cases hpath;
            · convert hR.2.2 ( mn :: path' ) _ using 1;
              · cases e1 ; cases e2 ; aesop;
              · unfold nsBind at hpath; aesop;

/-
HOL4: Theorem nsSub_nsAppend2
-/
theorem nsSub_nsAppend2 {m n v_ : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v_ → v_ → Prop)
      (e1 : «namespace» m n v_) (e2 : «namespace» m n v_) (e2' : «namespace» m n v_),
      nsSub R e1 e1 ∧ nsSub R e2 e2' →
        nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
          intro R e1 e2 e2' h;
          have := @nsLookup_nsAppend_some;
          constructor;
          · intro id_ v1_ hv1_;
            by_cases h : nsLookup e1 id_ = some v1_;
            · have := ‹nsSub R e1 e1 ∧ nsSub R e2 e2'›.1.1 id_ v1_ h;
              grind;
            · have := ‹nsSub R e1 e1 ∧ nsSub R e2 e2'›.2.1 id_ v1_;
              grind +splitImp;
          · intro path hpath;
            rw [ nsLookupMod_nsAppend_none ] at *;
            cases hpath.2 <;> simp_all +decide [ nsSub ]

/-
HOL4: Theorem alist_rel_restr_thm
-/
theorem alist_rel_restr_thm {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) (keys : List k),
      alist_rel_restr R e1 e2 keys ↔
        ∀ (k_ : k), MEM k_ keys = true →
          ∃ (val1 : v1) (val2 : v2),
            ALOOKUP e1 k_ = some val1 ∧ ALOOKUP e2 k_ = some val2 ∧ R k_ val1 val2 := by
              intro R e1 e2 keys;
              induction' keys with k keys ih generalizing e1 e2 <;> simp +decide [ *, ALOOKUP ];
              · simp +decide [ MEM, alist_rel_restr ];
              · unfold alist_rel_restr MEM; simp +decide [ List.any_cons ] ;
                cases h : ALOOKUP e1 k <;> cases h' : ALOOKUP e2 k <;> simp +decide [ h, h' ];
                · exact ⟨ k, Or.inl rfl, by aesop ⟩;
                · exact ⟨ k, Or.inl rfl, by aesop ⟩;
                · exact ⟨ k, Or.inl rfl, by aesop ⟩;
                · constructor <;> intro h' <;> simp_all +decide [ MEM ];
                  · grind;
                  · specialize h' k ; aesop

/-
HOL4: Theorem alistSub_cong
-/
theorem alistSub_cong {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (l1 l1' : List (k × v1)) (l2 l2' : List (k × v2))
      (R R' : k → v1 → v2 → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ (n_ : k) (x : v1) (y : v2),
          ALOOKUP l1' n_ = some x ∧ ALOOKUP l2' n_ = some y → R n_ x y = R' n_ x y) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
          intros l1 l1' l2 l2' R R' h_congr
          rw [h_congr.left, h_congr.right.left];
          convert ( alist_rel_restr_thm R l1' l2' ( l1'.map Prod.fst ) ) using 1;
          convert ( alist_rel_restr_thm R' l1' l2' ( l1'.map Prod.fst ) ) using 1;
          grind

/-
HOL4: Theorem nsLookup_FOLDR_nsLift
-/
theorem nsLookup_FOLDR_nsLift {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (k : n),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (cml_id.Short k) := by
        intro e p k;
        induction' p with mn p ih generalizing e k <;> simp_all +decide [ FOLDR ];
        · rfl;
        · convert ih _ _ using 1;
          convert nsLookup_nsLift mn ( List.foldr nsLift e p ) ( mk_id ( mn :: p ) k ) using 1;
          simp +decide [ mk_id ]

/-
HOL4: Theorem nsLookup_FOLDR_nsLift_some
-/
theorem nsLookup_FOLDR_nsLift_some {m n v : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (id_ : cml_id m n) (val_ : v),
      nsLookup (FOLDR nsLift e p) id_ = some val_ ↔
        (p = [] ∧ nsLookup e id_ = some val_) ∨
        (p ≠ [] ∧ ∃ (p2 : List m) (n_ : n),
          id_ = mk_id (p ++ p2) n_ ∧ nsLookup e (mk_id p2 n_) = some val_) := by
            intro e p id_ val_;
            induction' p with mn p ih generalizing id_ val_;
            · aesop;
            · convert nsLookup_nsLift mn ( FOLDR nsLift e p ) id_ using 1;
              cases id_ <;> simp +decide [ FOLDR ];
              · rw [ nsLookup_nsLift ] ; simp +decide [ mk_id ];
              · split_ifs <;> simp_all +decide [ nsLookup_nsLift ];
                · convert ih _ _ using 1;
                  cases p <;> simp +decide [ mk_id ];
                  exact ⟨ fun ⟨ p2, n_, h1, h2 ⟩ => h1 ▸ h2, fun h => by obtain ⟨ p2, n_, h1 ⟩ := mk_id_surj ‹_›; exact ⟨ p2, n_, h1, h1 ▸ h ⟩ ⟩;
                · rintro x y h; cases h;
                  tauto

/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none -/
theorem nsLookupMod_FOLDR_nsLift_none {m n v : Type} [BEq m] :
    ∀ (e : «namespace» m n v) (p1 p2 : List m),
      nsLookupMod (FOLDR nsLift e p1) p2 = none ↔
        (IS_PREFIX p1 p2 = true ∨ IS_PREFIX p2 p1 = true) →
          ∃ (p3 : List m), p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := sorry

/-
HOL4: Theorem nsAll2_conj
-/
theorem nsAll2_conj {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
          unfold nsAll2 at *;
          unfold nsSub at *;
          grind +splitImp

/-
HOL4: Theorem nsAll2_nsLookup2
-/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
          intros R e1 e2 n_ v2_ h;
          rcases h with ⟨ h₁, h₂ ⟩;
          obtain ⟨ h₃, h₄ ⟩ := h₂;
          exact h₄.1 n_ v2_ h₁

/-
HOL4: Theorem nsAll2_nsLookup_none
-/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
          intros R e1 e2 n_ h
          obtain ⟨h1, h2⟩ := h;
          constructor <;> intro hn <;> have := h1.1 n_ <;> have := h2.1 n_ <;> aesop

/-
HOL4: Theorem nsAll2_nsBind
-/
theorem nsAll2_nsBind {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
          intro R x v1_ v2_ e1 e2 hR
          obtain ⟨hR1, hR2⟩ := hR;
          constructor;
          · apply nsSub_nsBind;
            exact ⟨ hR1, hR2.1 ⟩;
          · exact nsSub_nsBind _ _ _ _ _ _ ⟨ hR1, hR2.2 ⟩

/-
HOL4: Theorem nsAll2_nsBindList
-/
theorem nsAll2_nsBindList {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (l1 : List (n × v1)) (l2 : List (n × v2))
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 ∧
      nsAll2 R e1 e2 →
        nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
          intros R l1 l2 e1 e2 h;
          induction' l1 with p1 l1 ih generalizing l2 e1 e2;
          · cases l2 <;> tauto;
          · rcases l2 with ( _ | ⟨ p2, l2 ⟩ ) <;> simp_all +decide [ LIST_REL ];
            · cases h.1;
            · convert nsAll2_nsBind R p1.1 p1.2 p2.2 ( nsBindList l1 e1 ) ( nsBindList l2 e2 ) _ using 1;
              · cases h.1 ; aesop;
              · grind +splitIndPred

/-
HOL4: Theorem nsAll2_nsAppend
-/
theorem nsAll2_nsAppend {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
      (e1' : «namespace» m n v1) (e2' : «namespace» m n v2),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
        nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
          intro R e1 e2 e1' e2' h; exact ⟨by
          obtain ⟨h1, h2⟩ := h;
          constructor;
          · intro id_ v1_ hv1_;
            rw [ nsLookup_nsAppend_some ] at hv1_;
            rcases hv1_ with ( hv1_ | ⟨ hv1_, hv2_, hv3_ ⟩ );
            · have := h1.1;
              have := this.1 id_ v1_ hv1_;
              obtain ⟨ v2_, hv2_, hv2'' ⟩ := this; use v2_; rw [ nsLookup_nsAppend_some ] ; aesop;
            · have := nsAll2_nsLookup2 R e1' e2' id_;
              have := nsAll2_nsLookup_none R e1' e2' id_;
              have := nsAll2_nsLookup2 R e1 e2 id_; simp_all +decide [ nsAll2 ] ;
              obtain ⟨ v2_, hv2_ ⟩ := Option.ne_none_iff_exists'.mp ‹_›; use v2_; simp_all +decide [ nsLookup_nsAppend_some ] ;
              have := h1.1.2; simp_all +decide [ nsSub ] ;
              exact?;
          · intro path hpath
            rw [nsLookupMod_nsAppend_none] at *;
            have := h1.1; have := h2.1; simp_all +decide [ nsAll2 ] ;
            have := h1.2 path; have := h2.2 path; simp_all +decide [ nsSub ] ;
            grind +extAll, by
            constructor;
            · intro id_ v1_ hv1_;
              by_cases h_cases : nsLookup e2 id_ = some v1_ ∨ nsLookup e2' id_ = some v1_;
              · cases' h_cases with h_cases h_cases;
                · obtain ⟨ v2_, hv2_, hv2_ ⟩ := nsAll2_nsLookup2 R e1 e2 id_ v1_ ⟨ h_cases, h.1 ⟩;
                  use v2_;
                  rw [ nsLookup_nsAppend_some ] ; aesop;
                · have := nsAll2_nsLookup2 R e1' e2' id_ v1_ ⟨ h_cases, h.2 ⟩;
                  obtain ⟨ v2_, hv2_, hv2'' ⟩ := this;
                  have := nsAll2_nsLookup_none R e1 e2 id_;
                  by_cases h_cases : nsLookup e1 id_ = none <;> simp_all +decide [ nsLookup_nsAppend_some ];
                  · intro p1 p2 hp1 hp2; specialize hv1_ p1 p2 hp1 hp2; have := h.1; simp_all +decide [ nsSub ] ;
                    have := this.1; simp_all +decide [ nsSub ] ;
                  · have := nsAll2_nsLookup2 R e1 e2 id_ v1_ ⟨ hv1_, h.1 ⟩ ; aesop;
              · rw [ nsLookup_nsAppend_some ] at hv1_ ; aesop;
            · intro path hpath;
              have := nsLookupMod_nsAppend_none e1 e1' path;
              have := nsLookupMod_nsAppend_none e2 e2' path; simp_all +decide ;
              cases hpath.2 <;> simp_all +decide [ nsAll2 ];
              · have := h.1.1.2 path; have := h.1.2.2 path; simp_all +decide [ nsSub ] ;
              · obtain ⟨ p1, hp1, ⟨ x, hx ⟩, y, hy ⟩ := ‹_›; have := h.1.2.2 p1; simp_all +decide ;
                have := h.1.1.2 p1; simp_all +decide [ nsSub ] ;
                exact Or.inr ⟨ p1, hp1, ⟨ x, rfl ⟩, by cases h : nsLookupMod e2 p1 <;> tauto ⟩⟩;

/-
HOL4: Theorem nsAll2_alist_to_ns
-/
theorem nsAll2_alist_to_ns {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (l1 : List (n × v1)) (l2 : List (n × v2)),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 →
        nsAll2 R (alist_to_ns l1 : «namespace» m n v1) (alist_to_ns l2 : «namespace» m n v2) := by
          intro R l1 l2 h;
          induction' h with l1 l2 h ih;
          · exact nsAll2_nsEmpty R;
          · convert nsAll2_nsBind R l1.1 l1.2 l2.2 ( alist_to_ns h ) ( alist_to_ns ih ) _ using 1;
            · unfold alist_to_ns; aesop;
            · grind

/-
HOL4: Theorem nsAll2_nsLift[simp]
-/
theorem nsAll2_nsLift {m n v1 v2 : Type} [BEq m] [BEq n] [LawfulBEq m] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (mn : m)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
        nsAll2 (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := by
          intro R mn e1 e2;
          constructor <;> intro h;
          · obtain ⟨h_sub, h_sub_flip⟩ := h;
            constructor;
            · constructor;
              · intro id_ v1_ hv1_;
                have := h_sub.1 ( cml_id.Long mn id_ ) v1_ ?_;
                · obtain ⟨ v2_, hv2_, hv2'' ⟩ := this; use v2_; simp_all +decide [ nsLookup_nsLift ] ;
                · rw [ nsLookup_nsLift ] ; aesop;
              · intro path hpath
                have hpath_lift : nsLookupMod (nsLift mn e2) (mn :: path) = none := by
                  rw [ nsLookupMod_nsLift ] ; aesop;
                have := h_sub.2 ( mn :: path ) hpath_lift; simp_all +decide [ nsLookupMod_nsLift ] ;
            · constructor;
              · intro id_ v1_ hv1_;
                have := h_sub_flip.1 ( cml_id.Long mn id_ ) v1_ ?_;
                · rw [ nsLookup_nsLift ] at this ; aesop;
                · rw [ nsLookup_nsLift ] ; aesop;
              · intro path hpath
                have hpath_lift : nsLookupMod (nsLift mn e1) (mn :: path) = none := by
                  rw [ nsLookupMod_nsLift ] ; aesop;
                have := h_sub_flip.2 ( mn :: path ) hpath_lift; simp_all +decide [ nsLookupMod_nsLift ] ;
          · unfold nsAll2 at h ⊢;
            unfold nsSub at *;
            grind +suggestions
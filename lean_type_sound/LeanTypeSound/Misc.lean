/-
  Translation of miscScript.sml
  Miscellaneous definitions and minor lemmas.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.LprefixLub
import Batteries.Data.List.Perm

open HOL4

/- HOL4:
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE = x
End
-/
def the {α : Type} (d : α) : Option α → α
  | some x => x
  | none => d

/- HOL4:
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End
-/
inductive app_list (α : Type) where
  | List : List α → app_list α
  | Append : app_list α → app_list α → app_list α
  | Nil : app_list α

/- HOL4:
Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End
-/
def append_aux {α : Type} : app_list α → List α → List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ aux
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4:
Definition append_def:
  append l = append_aux l []
End
-/
def cml_append {α : Type} (l : app_list α) : List α :=
  append_aux l []

/- HOL4:
Definition MAP3_def[simp]:
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
End
-/
def MAP3 {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | [], [], [] => []
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => []

/- HOL4:
Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End
-/
def tlookup (m : Sptree Nat) (k : Nat) : Nat :=
  match Sptree.lookup k m with
  | none => k
  | some k' => k'

/- HOL4:
Definition max3_def[simp]:
  max3 (x:num) y z = ...
End
-/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x)
  else (if z > y then z else y)

/- HOL4:
Type num_set = ``:unit spt``
-/
abbrev num_set := Sptree Unit

/- HOL4:
Type num_map = ``:'a spt``
-/
abbrev num_map (α : Type) := Sptree α

/- HOL4:
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End
-/
def find_index {α : Type} [BEq α] (y : α) : List α → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x == y then some n else find_index y xs (n + 1)

/- HOL4:
Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End
-/
def between (x y z : Nat) : Prop :=
  x ≤ z ∧ z < y

/- HOL4:
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1) xs)
End
-/
def enumerate {α : Type} (n : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (n, x) :: enumerate (n + 1) xs

/- HOL4:
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
-/
def UPDATE_LIST {α : Type} (f : Nat → α) (updates : List (Nat × α)) : Nat → α :=
  updates.foldl (fun g (k, v) => fun n => if n == k then v else g n) f

/- HOL4:
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End
-/
def lookup_vars {α : Type} [Inhabited α] : List Nat → List α → Option (List α)
  | [], _ => some []
  | v :: vs, env =>
    if v < env.length then
      match lookup_vars vs env with
      | some xs => some (EL v env :: xs)
      | none => none
    else none

/- HOL4:
Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End
-/
def range {α : Type} (s : Sptree α) : Set α :=
  fun v => ∃ n, Sptree.lookup n s = some v

-- ============================================================
-- Theorem stubs
-- ============================================================

-- ============================================================
-- Auxiliary lemmas (finite sets, lists, sptrees)
-- ============================================================

theorem exists_nodup_enum {α : Type} (l : List α) :
    ∃ m : List α, m.Nodup ∧ ∀ a, a ∈ m ↔ a ∈ l := by
  classical
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
    obtain ⟨m, hm, hmem⟩ := ih
    by_cases hx : x ∈ m
    · refine ⟨m, hm, fun a => ⟨fun h => List.mem_cons_of_mem _ ((hmem a).1 h), fun h => ?_⟩⟩
      rcases List.mem_cons.1 h with rfl | h
      · exact hx
      · exact (hmem a).2 h
    · exact ⟨x :: m, List.nodup_cons.2 ⟨hx, hm⟩, fun a => by simp [hmem]⟩

theorem CARD_eq_of_nodup {α : Type} {s : Set α} {l : List α} (hl : l.Nodup)
    (hs : ∀ a, s a ↔ a ∈ l) : CARD s = l.length := by
  have h : ∃ l : List α, l.Nodup ∧ ∀ a, s a ↔ a ∈ l := ⟨l, hl, hs⟩
  unfold CARD
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup h1 hl]
  intro a; rw [← h2, hs]

theorem nodup_of_subset_length {α : Type} {m L : List α} (hm : m.Nodup) (hsub : m ⊆ L)
    (hlen : L.length ≤ m.length) : L.Nodup :=
  ((List.subperm_of_subset hm hsub).perm_of_length_le hlen).nodup_iff.1 hm

theorem inj_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a1 a2 : α} (h1 : a1 ∈ l) (h2 : a2 ∈ l) (he : f a1 = f a2) : a1 = a2 := by
  induction l with
  | nil => simp at h1
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    simp only [List.mem_cons] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · exact absurd (List.mem_map.2 ⟨a2, h2, he.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨a1, h1, he⟩) h.1
    · exact ih h.2 h1 h2

theorem Sptree.lookup_eq_some_iff {α : Type} {t : List (Nat × α)}
    (hnd : (t.map Prod.fst).Nodup) {k : Nat} {x : α} :
    Sptree.lookup k t = some x ↔ (k, x) ∈ t := by
  unfold Sptree.lookup
  induction t with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.find?_cons, List.mem_cons]
    by_cases hak : a = k
    · subst hak
      simp only [decide_true, Option.map_some, Option.some.injEq]
      constructor
      · intro h; exact Or.inl (by rw [h])
      · rintro (h | h)
        · cases h; rfl
        · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hnd.1
    · simp only [hak, decide_false]
      rw [ih hnd.2]; simp [Prod.mk.injEq, Ne.symm hak]

theorem Sptree.lookup_isSome_iff {α : Type} {t : List (Nat × α)} {k : Nat} :
    (Sptree.lookup k t).isSome ↔ k ∈ t.map Prod.fst := by
  unfold Sptree.lookup
  induction t with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases hak : a = k
    · subst hak; simp
    · simp [hak, Ne.symm hak]

theorem tlookup_of_not_mem {names : List (Nat × Nat)} {a : Nat}
    (ha : a ∉ names.map Prod.fst) : tlookup names a = a := by
  have : Sptree.lookup a names = none := by
    cases h' : Sptree.lookup a names with
    | none => rfl
    | some _ => exact absurd (Sptree.lookup_isSome_iff.1 (by simp [h'])) ha
  simp [tlookup, this]

theorem find_index_shift {α : Type} [BEq α] (ls : List α) (n : α) (m : Nat) :
    find_index n ls m = (find_index n ls 0).map (· + m) := by
  induction ls generalizing m with
  | nil => simp [find_index]
  | cons x xs ih =>
    simp only [find_index]
    split
    · simp
    · rw [ih, ih 1]; simp [Option.map_map, Function.comp_def]; congr 1; funext a; omega

/- HOL4:
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s
-/
theorem CARD_IMAGE_ID_BIJ {α : Type} {f : α → α} {s : Set α} :
    FINITE s →
    (∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s →
    BIJ f s s := by
  rintro ⟨l0, hl0⟩ ⟨hmap, hcard⟩
  obtain ⟨l, hl, hlm⟩ := exists_nodup_enum l0
  have hs : ∀ a, s a ↔ a ∈ l := fun a => by rw [hl0, hlm]
  obtain ⟨m, hm, hmm⟩ := exists_nodup_enum (l.map f)
  have him : ∀ b, IMAGE f s b ↔ b ∈ m := by
    intro b; rw [hmm]; simp only [IMAGE, Set.image, List.mem_map, hs]
  rw [CARD_eq_of_nodup hm him, CARD_eq_of_nodup hl hs] at hcard
  have hmapnd : (l.map f).Nodup :=
    nodup_of_subset_length hm (fun b hb => (hmm b).1 hb) (by simp; omega)
  have hml : m ⊆ l := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ((hmm b).1 hb)
    exact (hs _).1 (hmap a ((hs a).2 ha))
  have hperm := (List.subperm_of_subset hm hml).perm_of_length_le (by omega)
  refine ⟨fun a ha => hmap a ha,
    fun a1 a2 h1 h2 he => inj_of_nodup_map hmapnd ((hs _).1 h1) ((hs _).1 h2) he, ?_⟩
  intro b hb
  have : b ∈ m := hperm.mem_iff.2 ((hs b).1 hb)
  obtain ⟨a, ha, hab⟩ := (him b).2 this
  exact ⟨a, ha, hab⟩
/- HOL4:
Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒ BIJ (tlookup names) UNIV UNIV
-/
/- The original translation below is false: `Sptree` is represented as an
   association list in which a key may occur several times (only the first
   occurrence is visible to `Sptree.lookup`), whereas HOL4 sptrees never
   contain shadowed entries.  Counterexample: for
   `names = [(0,1), (1,1), (1,0)]` the values `{1, 0}` coincide with the
   domain `{0, 1}`, yet `tlookup names 0 = tlookup names 1 = 1`.

theorem tlookup_bij_suff {names : Sptree Nat} :
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names →
    BIJ (tlookup names) Set.univ Set.univ := sorry
-/

/-- Corrected version of `tlookup_bij_suff`: we add the well-formedness
    hypothesis that the keys of the sptree are distinct (which always holds
    for genuine HOL4 sptrees). -/
theorem tlookup_bij_suff {names : Sptree Nat}
    (hnd : (List.map Prod.fst (names : List (Nat × Nat))).Nodup) :
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names →
    BIJ (tlookup names) Set.univ Set.univ := by
  change List (Nat × Nat) at names
  intro h
  have hV : ∀ x, x ∈ names.map Prod.snd ↔ x ∈ names.map Prod.fst := by
    intro x
    have := congrFun h x
    simp only [Sptree.toList, Sptree.domain] at this
    rw [← Sptree.lookup_isSome_iff]
    exact Iff.of_eq this
  have hVnd : (names.map Prod.snd).Nodup :=
    nodup_of_subset_length hnd (fun x hx => (hV x).2 hx) (by simp)
  have tl_dom : ∀ a, a ∈ names.map Prod.fst →
      ∃ v, (a, v) ∈ names ∧ tlookup names a = v := by
    intro a ha
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (Sptree.lookup_isSome_iff.2 ha)
    exact ⟨v, (Sptree.lookup_eq_some_iff hnd).1 hv, by simp [tlookup, hv]⟩
  refine ⟨fun _ _ => trivial, fun a1 a2 _ _ he => ?_, fun b _ => ?_⟩
  · by_cases h1 : a1 ∈ names.map Prod.fst <;>
    by_cases h2 : a2 ∈ names.map Prod.fst
    · obtain ⟨v1, hv1, e1⟩ := tl_dom a1 h1
      obtain ⟨v2, hv2, e2⟩ := tl_dom a2 h2
      have := inj_of_nodup_map hVnd hv1 hv2 (by simp only; rw [← e1, ← e2, he])
      exact (Prod.mk.inj this).1
    · obtain ⟨v1, hv1, e1⟩ := tl_dom a1 h1
      rw [tlookup_of_not_mem h2, e1] at he; subst he
      exact absurd ((hV v1).1 (List.mem_map.2 ⟨_, hv1, rfl⟩)) h2
    · obtain ⟨v2, hv2, e2⟩ := tl_dom a2 h2
      rw [tlookup_of_not_mem h1, e2] at he; subst he
      exact absurd ((hV a1).1 (List.mem_map.2 ⟨_, hv2, rfl⟩)) h1
    · rwa [tlookup_of_not_mem h1, tlookup_of_not_mem h2] at he
  · by_cases hb : b ∈ names.map Prod.fst
    · obtain ⟨⟨a, b'⟩, hab, rfl⟩ := List.mem_map.1 ((hV b).2 hb)
      obtain ⟨v, hv, e⟩ := tl_dom a (List.mem_map.2 ⟨_, hab, rfl⟩)
      refine ⟨a, trivial, ?_⟩
      rw [e]
      have := inj_of_nodup_map hnd hv hab rfl
      exact (Prod.mk.inj this).2
    · exact ⟨b, trivial, tlookup_of_not_mem hb⟩
/- HOL4:
Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔ set (toList names) = domain names
-/
/- The original translation below is false for the same reason as
   `tlookup_bij_suff` (shadowed entries).  Counterexample for the
   left-to-right direction: `names = [(0,0), (0,5)]`, where `tlookup names`
   is the identity but `Sptree.toList names = [0, 5]` while the domain is `{0}`.

theorem tlookup_bij_iff {names : Sptree Nat} :
    BIJ (tlookup names) Set.univ Set.univ ↔
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names := sorry
-/

/-- Corrected version of `tlookup_bij_iff`, assuming the keys of the sptree
    are distinct. -/
theorem tlookup_bij_iff {names : Sptree Nat}
    (hnd : (List.map Prod.fst (names : List (Nat × Nat))).Nodup) :
    BIJ (tlookup names) Set.univ Set.univ ↔
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names := by
  refine ⟨fun hb => ?_, tlookup_bij_suff hnd⟩
  change List (Nat × Nat) at names
  funext x
  simp only [Sptree.toList, Sptree.domain]
  apply propext
  rw [Sptree.lookup_isSome_iff]
  constructor
  · intro hx
    obtain ⟨⟨k, x'⟩, hkx, rfl⟩ := List.mem_map.1 hx
    have hl : Sptree.lookup k names = some x' := (Sptree.lookup_eq_some_iff hnd).2 hkx
    have htk : tlookup names k = x' := by simp [tlookup, hl]
    refine Classical.byContradiction fun hn => ?_
    have := hb.2.1 k x' trivial trivial (by rw [htk, tlookup_of_not_mem hn])
    subst this
    exact hn (List.mem_map.2 ⟨_, hkx, rfl⟩)
  · intro hx
    obtain ⟨a, _, ha⟩ := hb.2.2 x trivial
    by_cases hadom : a ∈ names.map Prod.fst
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (Sptree.lookup_isSome_iff.2 hadom)
      have : tlookup names a = v := by simp [tlookup, hv]
      rw [this] at ha; subst ha
      exact List.mem_map.2 ⟨_, (Sptree.lookup_eq_some_iff hnd).1 hv, rfl⟩
    · rw [tlookup_of_not_mem hadom] at ha; subst ha; exact absurd hx hadom
/- HOL4:
Theorem find_index_LESS_LENGTH:
   ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)
-/
theorem find_index_LESS_LENGTH {α : Type} [BEq α] [LawfulBEq α]
    (ls : List α) (n : α) (m i : Nat) :
    find_index n ls m = some i → m ≤ i ∧ i < m + ls.length := by
  induction ls generalizing m with
  | nil => simp [find_index]
  | cons x xs ih =>
    simp only [find_index]
    split
    · intro h; cases h; simp
    · intro h; have := ih (m+1) h; simp; omega
/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧ i < LENGTH env ∧ (v = SND (EL i env))
-/
theorem ALOOKUP_find_index_SOME {α β : Type} [BEq α] [LawfulBEq α] [Inhabited α] [Inhabited β]
    {env : List (α × β)} {k : α} {val_ : β} :
    ALOOKUP env k = some val_ →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ val_ = (EL i env).2 := by
  induction env with
  | nil => simp [ALOOKUP]
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP, List.map_cons, find_index]
    split
    · intro h; cases h; exact ⟨0, by simp, by simp, by simp [EL]⟩
    · intro h
      obtain ⟨i, h1, h2, h3⟩ := ih h
      refine ⟨i+1, ?_, by simp; omega, by simpa [EL] using h3⟩
      rw [find_index_shift, h1]; rfl
/- HOL4:
Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
-/
theorem IS_PREFIX_THM {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    (l2 l1 : List α) :
    IS_PREFIX l1 l2 = true ↔
    l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1 := by
  unfold IS_PREFIX
  induction l2 generalizing l1 with
  | nil => simp
  | cons x xs ih =>
    cases l1 with
    | nil => simp [List.isPrefixOf]
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq, ih, List.length_cons]
      constructor
      · rintro ⟨rfl, h1, h2⟩
        refine ⟨by omega, fun n hn => ?_⟩
        cases n with
        | zero => rfl
        | succ n => simpa [EL] using h2 n (by omega)
      · rintro ⟨h1, h2⟩
        refine ⟨by simpa [EL] using h2 0 (by omega), by omega, fun n hn => ?_⟩
        simpa [EL] using h2 (n+1) (by omega)
/- HOL4:
Theorem FST_pair:
  (λ(n,v). n) = FST
-/
theorem FST_pair {α β : Type} :
    (fun (p : α × β) => p.1) = Prod.fst := rfl
/- HOL4:
Theorem LESS_1[simp]:
  x < 1 ⇔ (x = 0:num)
-/
theorem LESS_1 {x : Nat} :
    x < 1 ↔ x = 0 := by omega
/- HOL4:
Theorem map_some_eq:
  !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)
-/
theorem map_some_eq {α : Type} (l1 l2 : List α) :
    l1.map some = l2.map some ↔ l1 = l2 :=
  List.map_inj_right (fun _ _ h => Option.some.inj h)
/- HOL4:
Theorem map_some_eq_append:
  !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
-/
theorem map_some_eq_append {α : Type} (l1 l2 l3 : List α) :
    l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  rw [← List.map_append]; exact List.map_inj_right (fun _ _ h => Option.some.inj h)
/- HOL4:
Theorem MAP_EQ_MAP_IMP:
   !xs ys f. (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
     (MAP f xs = MAP f ys) ==> (xs = ys)
-/
theorem MAP_EQ_MAP_IMP {α β : Type} (xs ys : List α) (f : α → β) :
    (∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) →
    xs.map f = ys.map f → xs = ys := by
  induction xs generalizing ys with
  | nil => intro _ h; cases ys <;> simp_all
  | cons x xs ih =>
    intro hinj h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have : x = y := hinj x y ⟨by simp, by simp, h.1⟩
      subst this
      congr 1
      exact ih ys (fun a b ⟨ha, hb, he⟩ => hinj a b ⟨by simp [ha], by simp [hb], he⟩) h.2
/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
-/
theorem FDOM_FLOOKUP {α β : Type} {x : α} {f : Finmap α β} :
    x ∈ Finmap.FDOM f ↔ ∃ val_, Finmap.FLOOKUP f x = some val_ := by
  show (f x).isSome = true ↔ _
  simp [Finmap.FLOOKUP, Option.isSome_iff_exists]
/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
-/
theorem DROP_EMPTY {α : Type} (ls : List α) (n : Nat) :
    DROP n ls = [] → n ≥ ls.length := by simp [DROP]
/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I
-/
theorem plus_0_I :
    (fun (n : Nat) => 0 + n) = id := by funext n; simp

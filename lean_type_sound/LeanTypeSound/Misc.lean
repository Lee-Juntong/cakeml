/-
  Translation of miscScript.sml
  Miscellaneous definitions and minor lemmas.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.LprefixLub

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

/- HOL4:
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s
-/
theorem CARD_IMAGE_ID_BIJ {α : Type} {f : α → α} {s : Set α} :
    FINITE s →
    (∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s →
    BIJ f s s := sorry
/- HOL4:
Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒ BIJ (tlookup names) UNIV UNIV
-/
theorem tlookup_bij_suff {names : Sptree Nat} :
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names →
    BIJ (tlookup names) Set.univ Set.univ := sorry
/- HOL4:
Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔ set (toList names) = domain names
-/
theorem tlookup_bij_iff {names : Sptree Nat} :
    BIJ (tlookup names) Set.univ Set.univ ↔
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names := sorry
/- HOL4:
Theorem find_index_LESS_LENGTH:
   ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)
-/
theorem find_index_LESS_LENGTH {α : Type} [BEq α]
    (ls : List α) (n : α) (m i : Nat) :
    find_index n ls m = some i → m ≤ i ∧ i < m + ls.length := by
  induction ls generalizing m i with
  | nil => simp [find_index]
  | cons x xs ih =>
    simp only [find_index, List.length_cons]
    split
    · intro h; simp at h; omega
    · intro h
      have := ih (m + 1) i h
      omega
/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧ i < LENGTH env ∧ (v = SND (EL i env))
-/
theorem find_index_shift {α : Type} [BEq α] (ls : List α) (n : α) (m : Nat) :
    find_index n ls m = (find_index n ls 0).map (· + m) := by
  induction ls generalizing m with
  | nil => simp [find_index]
  | cons x xs ih =>
    simp only [find_index]
    split
    · simp
    · rw [ih (m + 1), ih 1]
      cases find_index n xs 0 <;> simp <;> omega

theorem ALOOKUP_find_index_SOME {α β : Type} [BEq α] [LawfulBEq α] [Inhabited α] [Inhabited β]
    {env : List (α × β)} {k : α} {val_ : β} :
    ALOOKUP env k = some val_ →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ val_ = (EL i env).2 := by
  induction env with
  | nil => simp [ALOOKUP]
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    intro hlk
    simp only [ALOOKUP] at hlk
    by_cases hak : a == k
    · simp [hak] at hlk
      refine ⟨0, ?_, ?_, ?_⟩
      · simp [find_index, hak]
      · simp
      · simp at hak; simp [EL, hlk]
    · simp [hak] at hlk
      obtain ⟨i, hfi, hilt, hvi⟩ := ih hlk
      refine ⟨i + 1, ?_, ?_, ?_⟩
      · simp [find_index, hak]
        rw [find_index_shift]
        rw [hfi]
        simp
      · simp; omega
      · simp [EL] at hvi ⊢
        exact hvi
/- HOL4:
Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
-/
theorem IS_PREFIX_THM {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    (l2 l1 : List α) :
    IS_PREFIX l1 l2 = true ↔
    l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1 := by
  unfold IS_PREFIX EL
  induction l2 generalizing l1 with
  | nil =>
    simp [List.isPrefixOf]
  | cons x xs ih =>
    cases l1 with
    | nil =>
      simp [List.isPrefixOf]
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq, List.length_cons]
      constructor
      · rintro ⟨hxy, hpref⟩
        subst hxy
        rw [ih ys] at hpref
        obtain ⟨hle, helem⟩ := hpref
        refine ⟨by omega, ?_⟩
        intro n hn
        cases n with
        | zero =>
          show (x :: xs)[0]! = (x :: ys)[0]!
          rfl
        | succ k =>
          have hk : k < xs.length := by simp at hn; omega
          have hh := helem k hk
          show (x :: xs)[k+1]! = (x :: ys)[k+1]!
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD] at hh
          simp only [List.getElem?_cons_succ]
          exact hh
      · rintro ⟨hle, helem⟩
        have hxy : x = y := by
          have := helem 0 (by simp)
          show x = y
          have h := this
          show x = y
          have : (x :: xs)[0]! = (y :: ys)[0]! := h
          simpa using this
        refine ⟨hxy, ?_⟩
        rw [ih ys]
        refine ⟨by omega, ?_⟩
        intro n hn
        have := helem (n + 1) (by simp; omega)
        show xs[n]! = ys[n]!
        have : (x :: xs)[n+1]! = (y :: ys)[n+1]! := this
        simpa using this
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
    l1.map some = l2.map some ↔ l1 = l2 := by
  constructor
  · intro h
    induction l1 generalizing l2 with
    | nil => cases l2 <;> simp_all
    | cons a as ih =>
      cases l2 with
      | nil => simp at h
      | cons b bs =>
        simp at h
        obtain ⟨rfl, h2⟩ := h
        rw [ih bs h2]
  · intro h; rw [h]
/- HOL4:
Theorem map_some_eq_append:
  !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
-/
theorem map_some_eq_append {α : Type} (l1 l2 l3 : List α) :
    l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  rw [← List.map_append, map_some_eq]
/- HOL4:
Theorem MAP_EQ_MAP_IMP:
   !xs ys f. (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
     (MAP f xs = MAP f ys) ==> (xs = ys)
-/
theorem MAP_EQ_MAP_IMP {α β : Type} (xs ys : List α) (f : α → β) :
    (∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) →
    xs.map f = ys.map f → xs = ys := by
  induction xs generalizing ys with
  | nil =>
    intro _ h
    cases ys <;> simp_all
  | cons a as ih =>
    intro hfn h
    cases ys with
    | nil => simp at h
    | cons b bs =>
      simp at h
      obtain ⟨hfab, hmap⟩ := h
      have hab : a = b := hfn a b ⟨List.mem_cons_self, List.mem_cons_self, hfab⟩
      have ihres : as = bs := ih bs (fun x y ⟨hx, hy, hfxy⟩ =>
        hfn x y ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy, hfxy⟩) hmap
      rw [hab, ihres]
/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
-/
theorem FDOM_FLOOKUP {α β : Type} {x : α} {f : Finmap α β} :
    x ∈ Finmap.FDOM f ↔ ∃ val_, Finmap.FLOOKUP f x = some val_ := by
  unfold Finmap.FDOM Finmap.FLOOKUP
  simp [Option.isSome_iff_exists]
  rfl
/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
-/
theorem DROP_EMPTY {α : Type} (ls : List α) (n : Nat) :
    DROP n ls = [] → n ≥ ls.length := by
  unfold DROP
  intro h
  have := List.length_drop (l := ls) (i := n)
  rw [h] at this
  simp at this
  omega
/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I
-/
theorem plus_0_I :
    (fun (n : Nat) => 0 + n) = id := by funext n; simp

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
  | nil => intro h; simp [find_index] at h
  | cons x xs ih =>
    intro h
    unfold find_index at h
    split at h
    · injection h with h
      subst h
      simp [List.length_cons]
    · have := ih (m + 1) i h
      simp [List.length_cons]; omega
/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧ i < LENGTH env ∧ (v = SND (EL i env))
-/
theorem ALOOKUP_find_index_SOME {α β : Type} [BEq α] [Inhabited α] [Inhabited β]
    {env : List (α × β)} {k : α} {val_ : β} :
    ALOOKUP env k = some val_ →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ val_ = (EL i env).2 := sorry
/- HOL4:
Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
-/
theorem IS_PREFIX_THM {α : Type} [BEq α] [Inhabited α]
    (l2 l1 : List α) :
    IS_PREFIX l1 l2 = true ↔
    l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1 := sorry
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
    | cons x xs ih =>
      cases l2 with
      | nil => simp at h
      | cons y ys =>
        simp at h
        obtain ⟨hxy, hxs⟩ := h
        rw [hxy, ih ys hxs]
  · intro h; rw [h]
/- HOL4:
Theorem map_some_eq_append:
  !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
-/
theorem map_some_eq_append {α : Type} (l1 l2 l3 : List α) :
    l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  rw [← List.map_append]
  exact map_some_eq _ _
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
  | cons x xs ih =>
    intro hinj h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp at h
      obtain ⟨hfxy, hmap⟩ := h
      have hxy : x = y := hinj x y ⟨by simp, by simp, hfxy⟩
      rw [hxy]
      congr 1
      apply ih ys
      · intro a b hab
        exact hinj a b ⟨List.mem_cons_of_mem _ hab.1, List.mem_cons_of_mem _ hab.2.1, hab.2.2⟩
      · exact hmap
/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
-/
theorem FDOM_FLOOKUP {α β : Type} {x : α} {f : Finmap α β} :
    x ∈ Finmap.FDOM f ↔ ∃ val_, Finmap.FLOOKUP f x = some val_ := by
  simp only [Finmap.FDOM, Finmap.FLOOKUP, Membership.mem]
  constructor
  · intro h
    cases hfx : f x with
    | none => simp [hfx] at h
    | some v => exact ⟨v, rfl⟩
  · rintro ⟨v, hv⟩
    rw [hv]; rfl
/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
-/
theorem DROP_EMPTY {α : Type} (ls : List α) (n : Nat) :
    DROP n ls = [] → n ≥ ls.length := by
  intro h
  simp [DROP] at h
  omega
/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I
-/
theorem plus_0_I :
    (fun (n : Nat) => 0 + n) = id := by
  funext n; simp

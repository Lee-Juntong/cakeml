import LeanTypeSound.TypeSound
open HOL4

theorem LIST_REL_of_getElem_bang {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ i, i < xs.length → R xs[i]! ys[i]!) → LIST_REL R xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h => .cons _ _ _ _ (by simpa using h 0 (by simp))
      (LIST_REL_of_getElem_bang (by simpa using hl) (fun i hi => by
        simpa using h (i + 1) (by simpa using hi)))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem LIST_REL_REPLICATE_of_all {α β : Type} {R : α → β → Prop} {t : β} :
    ∀ {xs : List α}, (∀ x, x ∈ xs → R x t) → LIST_REL R xs (REPLICATE xs.length t)
  | [], _ => by simp [REPLICATE]; exact .nil
  | x :: xs, h => by
    simp only [List.length_cons, REPLICATE, List.replicate_succ]
    exact .cons _ _ _ _ (h x (by simp)) (LIST_REL_REPLICATE_of_all (fun y hy => h y (by simp [hy])))

mutual
theorem eq_same_type_v {tvs : Nat} {ctMap_ : ctMap} {tenvS : tenv_store} (hok : ctMap_ok ctMap_) :
    ∀ (v1 v2 : v) (t : sem_t), type_v tvs ctMap_ tenvS v1 t → type_v tvs ctMap_ tenvS v2 t →
      do_eq v1 v2 ≠ .Eq_type_error
  | v1, v2, t, h1, h2 => by
    generalize hT : t = T at h2
    cases h1 <;> cases h2 <;> (try tv_unfold) <;> tv_close
    all_goals (try simp [do_eq, lit_same_type])
    all_goals trace_state
    all_goals sorry
  termination_by v1 => sizeOf v1

theorem eq_same_type_list {tvs : Nat} {ctMap_ : ctMap} {tenvS : tenv_store} (hok : ctMap_ok ctMap_) :
    ∀ (vs1 vs2 : List v) (ts : List sem_t), LIST_REL (type_v tvs ctMap_ tenvS) vs1 ts →
      LIST_REL (type_v tvs ctMap_ tenvS) vs2 ts → do_eq_list vs1 vs2 ≠ .Eq_type_error
  | [], [], _, _, _ => by simp [do_eq_list]
  | v1 :: vs1, v2 :: vs2, _, .cons _ _ _ _ h1 r1, .cons _ _ _ _ h2 r2 => by
    have := eq_same_type_v hok v1 v2 _ h1 h2
    have ih := eq_same_type_list hok vs1 vs2 _ r1 r2
    simp only [do_eq_list]
    split
    · split <;> simp_all
    · simp_all
  | [], _ :: _, _, .nil, h => by cases h
  | _ :: _, [], _, h, .nil => by cases h
  termination_by vs1 => sizeOf vs1
end

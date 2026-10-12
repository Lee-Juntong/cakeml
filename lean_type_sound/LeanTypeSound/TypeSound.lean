/-
  Translation of typeSoundScript.sml (part 3)
  Proof of type soundness: a type-correct program does not crash.
-/
import LeanTypeSound.TypeSoundExp

open HOL4

/- HOL4:
Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F)
-/
theorem exp_type_sound :
    ∀ (ctMap_ : ctMap),
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (es : List exp)
       (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env)
       (tenvE : tenv_val_exp) (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => LIST_REL (type_v tvs ctMap_ tenvS') vs ts
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) ∧
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (val_ : v)
       (pes : List (pat × exp)) (err_v : v) (r : result (List v) v)
       (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
       (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env val_ pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      type_v tvs ctMap_ tenvS val_ t1 ∧
      type_v 0 ctMap_ tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => type_v tvs ctMap_ tenvS' vs.head! t2
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) := by
  intro ctMap_
  constructor
  · intro ffi s env es r s' tenv tenvE ts tvs tenvS ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    obtain ⟨S, a, b, c, d, e⟩ :=
      (exp_type_sound_aux (ffi := ffi) ctMap_).1 s env es r s' tenv tenvE ts tvs tenvS h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨S, a, b, c, d, by rcases r with _ | (_ | (_ | _ | _)) <;> exact e⟩
  · intro ffi s env val_ pes err_v r s' tenv tenvE t1 t2 tvs tenvS ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    obtain ⟨S, a, b, c, d, e⟩ := (exp_type_sound_aux (ffi := ffi) ctMap_).2.2 s env val_ pes err_v r s' tenv
      tenvE t1 t2 tvs tenvS h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨S, a, b, c, d, by rcases r with _ | (_ | (_ | _ | _)) <;> exact e⟩

theorem FUPDATE_LIST_reverse_apply {α β : Type} [BEq α] [LawfulBEq α] (m : Finmap α β) :
    ∀ (l : List (α × β)) (k : α),
      Finmap.FUPDATE_LIST m l.reverse k = (ALOOKUP l k).or (m k)
  | [], k => by simp [Finmap.FUPDATE_LIST, ALOOKUP]
  | (a, b) :: l, k => by
    have ih := FUPDATE_LIST_reverse_apply m l k
    simp only [Finmap.FUPDATE_LIST, List.reverse_cons, List.foldl_append, List.foldl] at ih ⊢
    simp only [Finmap.FUPDATE, ALOOKUP, ih]
    by_cases h : a = k
    · subst h; simp
    · have h' : k ≠ a := fun e => h e.symm
      simp [h, h']

theorem build_tdefs_no_mods (next : Nat) (tds : type_def) :
    ∃ L, build_tdefs next tds = .Bind L [] := by
  induction tds generalizing next with
  | nil => exact ⟨[], rfl⟩
  | cons td tds ih =>
    obtain ⟨_, _, ctors⟩ := td
    obtain ⟨L, hL⟩ := ih (next + 1)
    exact ⟨L ++ (build_constrs next ctors).reverse, by simp [build_tdefs, hL, nsAppend, alist_to_ns]⟩

theorem build_ctor_tenv_no_mods (tenvT : tenv_abbrev) :
    ∀ (tds : type_def) (tids : List type_ident),
    ∃ L, build_ctor_tenv tenvT tds tids = .Bind L []
  | [], [] => ⟨[], rfl⟩
  | (tvs, _, ctors) :: tds, id_ :: ids => by
    obtain ⟨L, hL⟩ := build_ctor_tenv_no_mods tenvT tds ids
    exact ⟨L ++ (ctors.map fun (p : conN × List ast_t) =>
        (p.1, (tvs, p.2.map (type_name_subst tenvT), id_))).reverse,
      by simp [build_ctor_tenv, hL, nsAppend, alist_to_ns]⟩
  | [], _ :: _ => ⟨[], rfl⟩
  | _ :: _, [] => ⟨[], rfl⟩

theorem nsLookup_nsAppend_alist_Short {α : Type} (X : «namespace» modN conN α)
    (Y : List (conN × α)) (cn : conN) :
    nsLookup (nsAppend X (alist_to_ns Y)) (.Short cn) = (nsLookup X (.Short cn)).or (ALOOKUP Y cn) := by
  cases X; simp [nsAppend, alist_to_ns, nsLookup, ALOOKUP_append]

theorem ALOOKUP_map_key {κ γ : Type} [BEq κ] (key : conN → κ) (f : conN × List ast_t → γ)
    (cn : conN) (hkey : ∀ a, (key a == key cn) = (a == cn)) :
    ∀ (l : List (conN × List ast_t)),
      ALOOKUP (l.map fun p => (key p.1, f p)) (key cn) = (l.find? (fun p => p.1 == cn)).map f
  | [] => rfl
  | (a, ts) :: l => by
    simp only [List.map_cons, ALOOKUP, List.find?_cons, hkey]
    cases h : (a == cn) <;> simp [ALOOKUP_map_key key f cn hkey l]

theorem build_tdefs_lookup_rel (tenvT : tenv_abbrev) :
    ∀ (tds : type_def) (tids : List type_ident) (next : Nat), tds.length = tids.length →
    (∀ cn, (nsLookup (build_tdefs next tds) (.Short cn) = none ∧
            nsLookup (build_ctor_tenv tenvT tds tids) (.Short cn) = none) ∨
      ∃ k st p, nsLookup (build_tdefs next tds) (.Short cn) = some (k, st) ∧
        nsLookup (build_ctor_tenv tenvT tds tids) (.Short cn) = some p ∧
        p.2.1.length = k ∧ ALOOKUP (type_def_to_ctMap tenvT next tds tids) st = some p) ∧
    (∀ st p, (st, p) ∈ type_def_to_ctMap tenvT next tds tids →
      ∃ cn j, st = .TypeStamp cn j ∧ next ≤ j)
  | [], [], next, _ => by
    refine ⟨fun cn => Or.inl ?_, fun st p h => by simp [type_def_to_ctMap] at h⟩
    simp [build_tdefs, build_ctor_tenv, alist_to_ns, nsLookup, ALOOKUP]
  | (tvs, tn, ctors) :: tds, id_ :: ids, next, hlen => by
    obtain ⟨ih1, ih2⟩ := build_tdefs_lookup_rel tenvT tds ids (next + 1) (by simpa using hlen)
    refine ⟨fun cn => ?_, fun st p h => ?_⟩
    · simp only [build_tdefs, build_ctor_tenv, type_def_to_ctMap, nsLookup_nsAppend_alist_Short,
        build_constrs, ← List.map_reverse, ALOOKUP_append]
      have e1 := ALOOKUP_map_key (fun c => c) (fun p => (p.2.length, stamp.TypeStamp p.1 next))
        cn (fun _ => rfl) ctors.reverse
      have e2 := ALOOKUP_map_key (fun c => c)
        (fun p => (tvs, p.2.map (type_name_subst tenvT), id_)) cn (fun _ => rfl) ctors.reverse
      have e3 := ALOOKUP_map_key (fun c => stamp.TypeStamp c next)
        (fun p => (tvs, p.2.map (type_name_subst tenvT), id_)) cn
        (fun a => by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, stamp.TypeStamp.injEq]; simp)
        ctors.reverse
      simp only at e1 e2 e3
      rcases ih1 cn with ⟨h1, h2⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h1, h2]
        simp only [Option.none_or]
        rw [e1, e2]
        have hnone : ALOOKUP (type_def_to_ctMap tenvT (next + 1) tds ids)
            (stamp.TypeStamp cn next) = none := by
          rw [ALOOKUP_none_iff]
          intro hm
          obtain ⟨⟨st, p⟩, hm, rfl⟩ := List.mem_map.1 hm
          obtain ⟨_, j, hj, hle⟩ := ih2 _ _ hm
          simp only [stamp.TypeStamp.injEq] at hj
          omega
        cases hf : List.find? (fun p => p.1 == cn) ctors.reverse with
        | none => left; simp
        | some q =>
          right
          refine ⟨_, _, _, rfl, rfl, by simp, ?_⟩
          have hq : q.1 = cn := by simpa using List.find?_some hf
          rw [hq, hnone, Option.none_or, e3, hf]; rfl
      · right
        refine ⟨k, st, p, by rw [h1]; rfl, by rw [h2]; rfl, h3, by rw [h4]; rfl⟩
    · simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h
      rcases h with h | ⟨q, _, hq⟩
      · obtain ⟨cn, j, hj, hle⟩ := ih2 st p h
        exact ⟨cn, j, hj, by omega⟩
      · simp only [Prod.mk.injEq] at hq
        exact ⟨q.1, next, hq.1.symm, Nat.le_refl _⟩
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/- HOL4:
Theorem build_tdefs_build_tenv[local]:
  !tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids)
-/
theorem build_tdefs_build_tenv :
    ∀ (tenvT : tenv_abbrev) (tds : type_def) (tids : List type_ident)
      (next : Nat) (ctMap_ : ctMap),
      EVERY (fun (p : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (p.2.2.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by
  intro tenvT tds tids next ctMap_ ⟨_, hlen⟩
  obtain ⟨hrel, _⟩ := build_tdefs_lookup_rel tenvT tds tids next hlen
  obtain ⟨L1, hL1⟩ := build_tdefs_no_mods next tds
  obtain ⟨L2, hL2⟩ := build_ctor_tenv_no_mods tenvT tds tids
  have hflook : ∀ st p, ALOOKUP (type_def_to_ctMap tenvT next tds tids) st = some p →
      Finmap.FLOOKUP (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse)
        st = some p := by
    intro st p h
    simp only [Finmap.FLOOKUP]
    rw [FUPDATE_LIST_reverse_apply, h]; rfl
  refine ⟨⟨fun id_ v1 h => ?_, fun path hp => ?_⟩, ⟨fun id_ v2 h => ?_, fun path hp => ?_⟩⟩
  · cases id_ with
    | Short cn =>
      rcases hrel cn with ⟨h1, _⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h1] at h; cases h
      · rw [h1] at h; cases h
        exact ⟨p, h2, hflook _ _ h4, h3⟩
    | Long mn i => rw [hL1] at h; simp [nsLookup, ALOOKUP] at h
  · cases path with
    | nil => simp [nsLookupMod] at hp
    | cons mn path => rw [hL1]; simp [nsLookupMod, ALOOKUP]
  · cases id_ with
    | Short cn =>
      rcases hrel cn with ⟨_, h2⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h2] at h; cases h
      · rw [h2] at h; cases h
        exact ⟨(k, st), h1, hflook _ _ h4, h3⟩
    | Long mn i => rw [hL2] at h; simp [nsLookup, ALOOKUP] at h
  · cases path with
    | nil => simp [nsLookupMod] at hp
    | cons mn path => rw [hL2]; simp [nsLookupMod, ALOOKUP]
/- HOL4:
Theorem type_sound_invariant_union[local]:
  type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv
-/
theorem type_sound_invariant_union :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tids1 tids2 : Set type_ident) (tenv : type_env),
      type_sound_invariant st env ctMap_ tenvS (tids1 ∪ tids2) tenv →
      type_sound_invariant st env ctMap_ tenvS tids1 tenv := by
  intro ffi st env ctMap_ tenvS tids1 tids2 tenv ⟨h1, h2, ⟨h3, h3'⟩, h4, h5⟩
  exact ⟨h1, h2, ⟨fun x hx => h3 x ⟨Or.inl hx.1, hx.2⟩, h3'⟩, h4, h5⟩
/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds
-/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : tenv_abbrev) (tds : type_def),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by
  intro tenvT tds
  induction tds with
  | nil => intro; rfl
  | cons td tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := td
    intro h
    simp only [check_ctor_tenv, Bool.and_eq_true] at h
    simp only [EVERY, List.all_cons, Bool.and_eq_true] at ih ⊢
    exact ⟨h.1.1.1.1, ih h.2⟩
/- HOL4:
Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    ∧ type_all_env ctMap tenvS env2 tenv2
    ⇒ type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2)
-/
theorem type_all_env_extend :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (env1 env2 : sem_env)
      (tenv1 tenv2 : type_env),
      type_all_env ctMap_ tenvS env1 tenv1 ∧
      type_all_env ctMap_ tenvS env2 tenv2 →
      type_all_env ctMap_ tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) := by
  intro ctMap_ tenvS env1 env2 tenv1 tenv2 ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨nsAll2_nsAppend _ _ _ _ _ ⟨h1, h3⟩, nsAll2_nsAppend _ _ _ _ _ ⟨h2, h4⟩⟩
/- HOL4:
Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs)
-/
theorem type_e_con_check :
    ∀ (ctMap_ : ctMap) (envc : env_ctor),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      every_exp (one_con_check envc) e) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env_ : List (varN × sem_t)),
      type_funs tenv tenvE funs env_ →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs) := by
  intro ctMap_ envc
  have key : ∀ (tenv : type_env), nsAll2 (type_ctor ctMap_) envc tenv.c →
      (∀ {tenvE e t}, type_e tenv tenvE e t → every_exp (one_con_check envc) e) ∧
      (∀ {tenvE es ts}, type_es tenv tenvE es ts →
        ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es) ∧
      (∀ {tenvE funs env_}, type_funs tenv tenvE funs env_ →
        EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs) := by
    intro tenv hc
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    all_goals
      first
      | refine type_e.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
      | refine type_es.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
      | refine type_funs.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    all_goals (intros; try simp_all [every_exp, one_con_check, EVERY])
    all_goals first
      | assumption
      | simp [do_con_check]; done
      | (rename_i hl ih
         obtain ⟨⟨k, st⟩, h1, _, h3⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, hc⟩
         simp only at h3
         simp [do_con_check, h1, ← h3, ih.1])
  exact ⟨fun tenv _ _ _ h hc => (key tenv hc).1 h,
    fun tenv _ _ _ h hc => ((key tenv hc).2.1 h).2,
    fun tenv _ _ _ h hc => (key tenv hc).2.2 h⟩
/- HOL4:
Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T
-/
theorem decs_type_sound_no_check :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (st' : cml_state ffi) (r : result sem_env v) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True := sorry
/- HOL4:
Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
-/
theorem decs_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (extra_checks : Bool) (st' : cml_state ffi) (r : result sem_env v)
      (ctMap_ : ctMap) (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtimeout_error) => True := sorry
/- HOL4:
Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail
-/
theorem semantics_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (tops : List dec)
      (r : behaviour) (checks : Bool) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      r ≠ .Fail := sorry

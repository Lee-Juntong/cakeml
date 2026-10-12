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
-- ============================================================
-- Soundness of declarations: auxiliary development
-- ============================================================

/-- The conclusion of the declaration soundness theorem. -/
def decs_sound_concl {ffi : Type} (st' : cml_state ffi) (env : sem_env) (r : result sem_env v)
    (ctMap_ : ctMap) (tenvS : tenv_store) (tids : Set type_ident) (tenv tenv' : type_env) : Prop :=
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
    | .Rerr (.Rabort (.Rffi_error _)) => True

/-- The induction motive for declaration soundness. -/
def decs_sound_motive (tenv : type_env) (ds : List dec) (tids : Set type_ident)
    (tenv' : type_env) : Prop :=
  ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (st' : cml_state ffi)
    (r : result sem_env v) (ctMap_ : ctMap) (tenvS : tenv_store),
    evaluate_decs st env ds = (st', r) →
    type_sound_invariant st env ctMap_ tenvS tids tenv →
    decs_sound_concl st' env r ctMap_ tenvS tids tenv tenv'


theorem extend_dec_env_empty (env : sem_env) :
    extend_dec_env (.mk nsEmpty nsEmpty) env = env := by
  cases env; simp [extend_dec_env, sem_env.v_, sem_env.c, nsAppend_nsEmpty]

theorem extend_dec_tenv_empty (tenv : type_env) :
    extend_dec_tenv { v := nsEmpty, c := nsEmpty, t := nsEmpty } tenv = tenv := by
  cases tenv; simp [extend_dec_tenv, nsAppend_nsEmpty]

theorem set_union_empty {α : Type} (s : Set α) : s ∪ ∅ = s :=
  funext fun _ => propext ⟨fun h => h.elim id False.elim, Or.inl⟩

theorem extend_dec_tenv_assoc (t1 t2 t3 : type_env) :
    extend_dec_tenv t1 (extend_dec_tenv t2 t3) =
    extend_dec_tenv (extend_dec_tenv t1 t2) t3 := by
  simp [extend_dec_tenv, nsAppend_assoc]

theorem combine_dec_result_Rval (env1 env2 : sem_env) :
    (combine_dec_result env1 (.Rval env2) : result sem_env v) = .Rval (extend_dec_env env2 env1) :=
  rfl

theorem consistent_ctMap_empty {ffi : Type} {st : cml_state ffi} {tids : Set type_ident}
    {ctMap_ : ctMap} (h : consistent_ctMap st tids ctMap_) : consistent_ctMap st ∅ ctMap_ :=
  ⟨fun _ hx => hx.1, h.2⟩

theorem range_diff_self (c : ctMap) (tids : Set type_ident) :
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ tids :=
  fun _ hx => absurd hx.1 hx.2

/-- Restoring the invariant for the outer environment after an inner step raised. -/
theorem inv_restore {ffi : Type} {st2 : cml_state ffi} {env env' : sem_env} {c0 c2 : ctMap}
    {s0 s2 : tenv_store} {tenv tenv' : type_env}
    (h2 : type_sound_invariant st2 env' c2 s2 ∅ tenv')
    (hok : tenv_ok tenv) (hall : type_all_env c0 s0 env tenv)
    (hw : weakCT c2 c0) (hs : store_type_extension s0 s2) :
    type_sound_invariant st2 env c2 s2 ∅ tenv :=
  ⟨hok, h2.2.1, h2.2.2.1,
    type_all_env_weakening _ _ _ _ _ _ ⟨hw, store_type_extension_weakS _ _ hs, hall⟩,
    h2.2.2.2.2⟩

theorem decs_seq_invariant {ffi : Type} {st : cml_state ffi} {env : sem_env} {ctMap_ : ctMap}
    {tenvS : tenv_store} {tenv : type_env} {st1 : cml_state ffi} {env1 : sem_env}
    {ctMap1 : ctMap} {tenvS1 : tenv_store} {tenv1 : type_env} {decls1 decls2 : Set type_ident}
    (hinv : type_sound_invariant st env ctMap_ tenvS (decls1 ∪ decls2) tenv)
    (hdisj : Set.Disjoint decls1 decls2)
    (hr : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap1) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ decls1)
    (hinv1 : type_sound_invariant st1 env1 ctMap1 tenvS1 ∅ tenv1) :
    type_sound_invariant st1 env1 ctMap1 tenvS1 decls2 tenv1 := by
  refine ⟨hinv1.1, hinv1.2.1, ⟨?_, hinv1.2.2.1.2⟩, hinv1.2.2.2⟩
  rintro x ⟨hx2, hxr⟩
  by_cases hx0 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) x
  · exact hinv.2.2.1.1 x ⟨Or.inr hx2, hx0⟩
  · exact hdisj x ⟨hr x ⟨hxr, hx0⟩, hx2⟩

theorem decs_seq_frame {c0 c1 c2 : ctMap} {s0 s1 s2 : tenv_store} {d1 d2 : Set type_ident}
    (h01 : weakCT c1 c0) (h12 : weakCT c2 c1)
    (hr1 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c0) ⊆ d1)
    (hr2 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c2) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) ⊆ d2)
    (hs1 : store_type_extension s0 s1) (hs2 : store_type_extension s1 s2) :
    weakCT c2 c0 ∧
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c2) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c0) ⊆ d1 ∪ d2 ∧
    store_type_extension s0 s2 := by
  refine ⟨weakCT_trans _ _ _ ⟨h12, h01⟩, ?_, store_type_extension_trans _ _ _ ⟨hs1, hs2⟩⟩
  rintro x ⟨hx2, hx0⟩
  by_cases hx1 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) x
  · exact Or.inl (hr1 x ⟨hx1, hx0⟩)
  · exact Or.inr (hr2 x ⟨hx2, hx1⟩)

theorem decs_sound_concl_err_mono {ffi : Type} {st' : cml_state ffi} {env : sem_env}
    {e : error_result v} {ctMap_ : ctMap} {tenvS : tenv_store} {d1 d2 : Set type_ident}
    {tenv tenvA tenvB : type_env}
    (h : decs_sound_concl st' env (.Rerr e) ctMap_ tenvS d1 tenv tenvA) (hsub : d1 ⊆ d2) :
    decs_sound_concl st' env (.Rerr e) ctMap_ tenvS d2 tenv tenvB := by
  obtain ⟨c, s, h1, h2, h3, h4⟩ := h
  exact ⟨c, s, h1, fun x hx => hsub x (h2 x hx), h3, by rcases e with _ | (_ | _ | _) <;> exact h4⟩

theorem decs_concl_simple {ffi : Type} {st : cml_state ffi} {env env' : sem_env}
    {ctMap_ : ctMap} {tenvS : tenv_store} {tids : Set type_ident} {tenv tenv' : type_env}
    (hinv : type_sound_invariant st env ctMap_ tenvS tids tenv)
    (hok : tenv_ok (extend_dec_tenv tenv' tenv))
    (hall : type_all_env ctMap_ tenvS env' tenv') :
    decs_sound_concl st env (.Rval env') ctMap_ tenvS tids tenv tenv' :=
  ⟨ctMap_, tenvS, weakCT_refl _, range_diff_self _ _, store_type_extension_refl _, hall,
    hok, hinv.2.1, consistent_ctMap_empty hinv.2.2.1,
    type_all_env_extend _ _ _ _ _ _ ⟨hall, hinv.2.2.2.1⟩, hinv.2.2.2.2⟩

theorem inv_after_exp {ffi : Type} {st st1 : cml_state ffi} {env : sem_env}
    {ctMap_ : ctMap} {tenvS tenvS1 : tenv_store} {tids : Set type_ident} {tenv : type_env}
    (hinv : type_sound_invariant st env ctMap_ tenvS tids tenv)
    (hts : type_s ctMap_ st1.refs tenvS1) (hst : store_type_extension tenvS tenvS1)
    (hnt : st1.next_type_stamp = st.next_type_stamp)
    (hne : st1.next_exn_stamp = st.next_exn_stamp) :
    type_sound_invariant st1 env ctMap_ tenvS1 ∅ tenv :=
  ⟨hinv.1, hinv.2.1, ⟨fun _ hx => hx.1, fun cn id_ => by rw [hnt, hne]; exact hinv.2.2.1.2 cn id_⟩,
    type_all_env_weakening _ _ _ _ _ _
      ⟨weakCT_refl _, store_type_extension_weakS _ _ hst, hinv.2.2.2.1⟩, hts⟩

theorem list_rel_tenv_add_tvs {tvs : Nat} {c : ctMap} {s : tenv_store} :
    ∀ {l1 : List (varN × v)} {l2 : List (varN × sem_t)},
    LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
      p1.1 = p2.1 ∧ type_v tvs c s p1.2 p2.2) l1 l2 →
    LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
      p1.1 = p2.1 ∧ type_v p2.2.1 c s p1.2 p2.2.2) l1 (tenv_add_tvs tvs l2)
  | _, _, .nil => .nil
  | _, _, .cons _ _ _ _ h hl => .cons _ _ _ _ h (list_rel_tenv_add_tvs hl)

theorem good_ctMap_extend {c c' : ctMap} (hgood : good_ctMap c) (hok : ctMap_ok c')
    (hw : weakCT c' c)
    (hfresh : ∀ cn k, (k = bool_type_num ∨ k = list_type_num) →
      c' (.TypeStamp cn k) = c (.TypeStamp cn k)) :
    good_ctMap c' := by
  obtain ⟨_, ⟨b1, b2, b3⟩, ⟨e1, e2, e3, e4⟩, ⟨l1, l2, l3⟩⟩ := hgood
  refine ⟨hok, ⟨hw _ _ b1, hw _ _ b2, fun cn hcn => ?_⟩, ⟨hw _ _ e1, hw _ _ e2, hw _ _ e3, hw _ _ e4⟩,
    ⟨hw _ _ l1, hw _ _ l2, fun cn hcn => ?_⟩⟩
  · simp only [Finmap.FLOOKUP] at b3 ⊢
    rw [hfresh _ _ (Or.inl rfl)]; exact b3 cn hcn
  · simp only [Finmap.FLOOKUP] at l3 ⊢
    rw [hfresh _ _ (Or.inr rfl)]; exact l3 cn hcn

theorem decs_sound_nil (tenv : type_env) :
    decs_sound_motive tenv [] ∅ { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  simp only [evaluate_decs, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨ctMap_, tenvS, weakCT_refl _, range_diff_self _ _, store_type_extension_refl _, ?_, ?_⟩
  · exact ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩
  · rw [extend_dec_env_empty, extend_dec_tenv_empty]
    exact ⟨hinv.1, hinv.2.1, consistent_ctMap_empty hinv.2.2.1, hinv.2.2.2⟩

theorem decs_sound_cons (b : Bool) (tenv : type_env) (d : dec) (ds : List dec)
    (decls1 decls2 : Set type_ident) (tenv1 tenv2 : type_env)
    (hds : type_ds b (extend_dec_tenv tenv1 tenv) ds decls2 tenv2)
    (hdisj : Set.Disjoint decls1 decls2)
    (ih1 : decs_sound_motive tenv [d] decls1 tenv1)
    (ih2 : decs_sound_motive (extend_dec_tenv tenv1 tenv) ds decls2 tenv2) :
    decs_sound_motive tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1) := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  cases ds with
  | nil =>
    cases hds
    rw [set_union_empty, extend_dec_tenv_empty] at *
    exact ih1 st env st' r ctMap_ tenvS h hinv
  | cons d2 ds' =>
    rw [evaluate_decs] at h
    split at h
    · rename_i st1 env1 h1
      rw [fix_clock_evaluate2] at h1
      obtain ⟨ctMap1, tenvS1, hw1, hr1, hs1, hall1, hinv1⟩ :=
        ih1 st env st1 _ ctMap_ tenvS h1 (type_sound_invariant_union _ _ _ _ _ _ _ hinv)
      rcases h2 : evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with ⟨st2, r2⟩
      rw [h2] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ctMap2, tenvS2, hw2, hr2, hs2, hres⟩ :=
        ih2 st1 _ st2 r2 ctMap1 tenvS1 h2 (decs_seq_invariant hinv hdisj hr1 hinv1)
      obtain ⟨hw, hr, hs⟩ := decs_seq_frame hw1 hw2 hr1 hr2 hs1 hs2
      refine ⟨ctMap2, tenvS2, hw, hr, hs, ?_⟩
      rcases r2 with env2 | (err_v | (_ | _ | _))
      · rw [combine_dec_result_Rval]
        refine ⟨type_all_env_extend _ _ _ _ _ _ ⟨hres.1, type_all_env_weakening _ _ _ _ _ _
          ⟨hw2, store_type_extension_weakS _ _ hs2, hall1⟩⟩, ?_⟩
        rw [← extend_dec_env_assoc, ← extend_dec_tenv_assoc]
        exact hres.2
      · exact ⟨hres.1, inv_restore hres.2 hinv.1 hinv.2.2.2.1 hw hs⟩
      · exact hres
      · exact hres
      · exact hres
    · rename_i st1 e h1
      rw [fix_clock_evaluate2] at h1
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decs_sound_concl_err_mono (ih1 st env st1 _ ctMap_ tenvS h1
        (type_sound_invariant_union _ _ _ _ _ _ _ hinv)) (fun _ hx => Or.inl hx)

theorem decs_sound_dlet (b : Bool) (tenv : type_env) (locs : locs) (p : pat) (e : exp)
    (tvs : Nat) (t : sem_t) (bindings : List (varN × sem_t))
    (hdt : type_d b tenv (.Dlet locs p e) ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (hval : tvs ≠ 0 → is_value e)
    (hd : ALL_DISTINCT (pat_bindings p []))
    (hp : type_p tvs tenv p t bindings)
    (he : type_e tenv (bind_tvar tvs .Empty) e t) :
    decs_sound_motive tenv [.Dlet locs p e] ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  have hcon := (type_e_con_check ctMap_ env.c).1 _ _ _ _ he hinv.2.2.2.1.1
  simp only [evaluate_decs, hd, hcon, Bool.and_self, if_true] at h
  rcases h1 : evaluate st env [e] with ⟨st1, r1⟩
  rw [h1] at h
  obtain ⟨tenvS1, hts, hst, hnt, hne, hres⟩ :=
    (exp_type_sound ctMap_).1 st env [e] r1 st1 tenv .Empty [t] tvs tenvS
      ⟨h1, hinv.1, trivial, hinv.2.1, rfl, hinv.2.2.2.1, hinv.2.2.2.2,
        fun h => by simp [EVERY, hval h],
        (type_es_list_rel _ _ _ _).mpr (LIST_REL.cons _ _ _ _ he LIST_REL.nil)⟩
  have hinv1 := inv_after_exp hinv hts hst hnt hne
  rcases r1 with vs | (err_v | (_ | _ | _))
  · cases hres with
    | cons v1 _ vs' _ hv1 hrest =>
      cases hrest
      simp only [list_head!_cons] at h
      rcases (pat_type_sound).1 env.c st1.refs p v1 [] tenv ctMap_ [] t bindings tenvS1 tvs
          ⟨hinv.2.1.1, hinv.2.2.2.1.1, hv1, hp, hts, LIST_REL.nil⟩ with hm | ⟨bs, hm, hbs⟩
      · rw [hm] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ctMap_, tenvS1, weakCT_refl _, range_diff_self _ _, hst,
          (type_v_exn 0 ctMap_ tenvS1 hinv.2.1.2.2.1).2.2.1, hinv1⟩
      · rw [hm] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [List.append_nil] at hbs
        have hall : type_all_env ctMap_ tenvS1 (.mk (alist_to_ns bs) nsEmpty)
            { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } :=
          ⟨nsAll2_nsEmpty _, nsAll2_alist_to_ns _ _ _ (list_rel_tenv_add_tvs hbs)⟩
        exact ⟨ctMap_, tenvS1, weakCT_refl _, range_diff_self _ _, hst, hall,
          type_d_tenv_ok _ _ _ _ _ ⟨hdt, hinv.1⟩, hinv1.2.1, hinv1.2.2.1,
          type_all_env_extend _ _ _ _ _ _ ⟨hall, hinv1.2.2.2.1⟩, hts⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ctMap_, tenvS1, weakCT_refl _, range_diff_self _ _, hst, hres, hinv1⟩
  · exact hres.elim
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ctMap_, tenvS1, weakCT_refl _, range_diff_self _ _, hst, trivial⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ctMap_, tenvS1, weakCT_refl _, range_diff_self _ _, hst, trivial⟩

theorem decs_sound_dletrec (b : Bool) (tenv : type_env) (locs : locs) (funs : List (varN × varN × exp))
    (tvs : Nat) (bindings : List (varN × sem_t))
    (hd : type_d b tenv (.Dletrec locs funs) ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (hf : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs .Empty)) funs bindings) :
    decs_sound_motive tenv [.Dletrec locs funs] ∅
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  have hdist := type_funs_distinct _ _ _ _ hf
  have hcon := (type_e_con_check ctMap_ env.c).2.2 _ _ _ _ hf hinv.2.2.2.1.1
  simp only [EVERY] at hcon
  simp only [evaluate_decs, hdist, hcon, Bool.and_self, if_true, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine decs_concl_simple hinv (type_d_tenv_ok _ _ _ _ _ ⟨hd, hinv.1⟩) ⟨nsAll2_nsEmpty _, ?_⟩
  show nsAll2 _ (build_rec_env funs env nsEmpty) _
  rw [build_rec_env_merge, (nsAppend_nsEmpty _).1]
  have e1 : funs.map (fun ((f, _, _) : varN × varN × exp) => (f, v.Recclosure env funs f)) =
      funs.map (fun p => (p.1, v.Recclosure env funs p.1)) :=
    List.map_inj_left.2 (fun _ _ => rfl)
  have e2 : tenv_add_tvs tvs bindings = bindings.map (fun p => (p.1, tvs, p.2)) :=
    List.map_inj_left.2 (fun _ _ => rfl)
  have e3 : funs.map Prod.fst = funs.map (fun ((x, _, _) : varN × varN × exp) => x) :=
    List.map_inj_left.2 (fun _ _ => rfl)
  rw [e1, e2]
  apply nsAll2_alist_to_ns
  exact type_recfun_env funs ctMap_ tenvS tvs tenv .Empty env bindings
    ⟨hinv.1, hinv.2.2.2.1, trivial, rfl, hf, by rw [e3]; exact hdist⟩

theorem decs_sound_dtype (b : Bool) (tenv : type_env) (locs : locs) (tdefs : type_def)
    (type_identities : List type_ident) (tenvT : tenv_abbrev)
    (hd : type_d b tenv (.Dtype locs tdefs) (fun x => x ∈ type_identities)
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities,
        t := tenvT })
    (h1 : ALL_DISTINCT type_identities)
    (h2 : Set.Disjoint (fun x => x ∈ type_identities)
      (fun x => x ∈ (Tlist_num :: Tbool_num :: prim_type_nums)))
    (h3 : check_ctor_tenv (nsAppend tenvT tenv.t) tdefs)
    (h4 : type_identities.length = tdefs.length) :
    decs_sound_motive tenv [.Dtype locs tdefs] (fun x => x ∈ type_identities)
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities,
        t := tenvT } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  have hdup : EVERY check_dup_ctors tdefs = true := check_ctor_tenv_dups _ _ h3
  have hevery : EVERY (fun (p : List tvarN × typeN × List (conN × List ast_t)) =>
      ALL_DISTINCT (p.2.2.map Prod.fst)) tdefs = true := by
    simp only [EVERY, List.all_eq_true] at hdup ⊢
    rintro ⟨a, b, c⟩ hm
    have := hdup _ hm
    simp only [check_dup_ctors] at this
    rw [show c.map Prod.fst = c.map (fun (n, _) => n) from List.map_inj_left.2 (fun _ _ => rfl)]
    exact this
  simp only [EVERY] at hdup
  simp only [evaluate_decs, hdup, if_true, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hok, hgood, ⟨hdisj, hcons⟩, hall, hts⟩ := hinv
  have hokext := type_d_tenv_ok _ _ _ _ _ ⟨hd, hok⟩
  let L := type_def_to_ctMap (nsAppend tenvT tenv.t) st.next_type_stamp tdefs type_identities
  let c' : ctMap := Finmap.FUPDATE_LIST ctMap_ L.reverse
  have hlook : ∀ k, c' k = (ALOOKUP L k).or (ctMap_ k) := fun k =>
    FUPDATE_LIST_reverse_apply ctMap_ L k
  have hF1 : ∀ k x, ALOOKUP L k = some x →
      ∃ cn i, k = .TypeStamp cn i ∧ st.next_type_stamp ≤ i ∧
        i < st.next_type_stamp + tdefs.length := fun k x hk =>
    mem_type_def_to_ctMap _ _ _ _ _ _ ⟨ALOOKUP_mem hk, h4.symm⟩
  have hF2 : ∀ k x, ALOOKUP L k = some x → x.2.2 ∈ type_identities := fun k x hk =>
    type_def_to_ctMap_mem _ _ _ _ _ _ ⟨hk, h4.symm⟩
  have hF4 : ∀ k x, ctMap_ k = some x → ALOOKUP L k = none := by
    intro k x hk
    cases hL : ALOOKUP L k with
    | none => rfl
    | some y =>
      obtain ⟨cn, i, rfl, hle, _⟩ := hF1 _ _ hL
      have := (hcons cn i).1 (by show (ctMap_ _).isSome = true; rw [hk]; rfl)
      omega
  have hw : weakCT c' ctMap_ := by
    intro k x hk
    rw [hlook, hF4 k x hk, hk]; rfl
  have hrange : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ (fun x => x ∈ type_identities) := by
    rintro x ⟨⟨k, hk⟩, hnot⟩
    simp only [Finmap.o_f, hlook] at hk
    cases hL : ALOOKUP L k with
    | some y =>
      rw [hL] at hk
      simp only [Option.some_or, Option.map_some, Option.some.injEq] at hk
      subst hk
      exact hF2 _ _ hL
    | none =>
      rw [hL, Option.none_or] at hk
      exact absurd ⟨k, hk⟩ hnot
  have hunion : c' = Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY L.reverse) ctMap_ := by
    funext k
    show c' k = _
    rw [hlook]
    simp only [Finmap.FUNION]
    rw [FUPDATE_LIST_reverse_apply]
    cases ALOOKUP L k <;> rfl
  have hfresh_lt : ∀ cn i, i < st.next_type_stamp → ALOOKUP L (.TypeStamp cn i) = none := by
    intro cn i hi
    cases hL : ALOOKUP L (.TypeStamp cn i) with
    | none => rfl
    | some y =>
      obtain ⟨cn', i', he, hle, _⟩ := hF1 _ _ hL
      cases he
      omega
  have hbool : bool_type_num < st.next_type_stamp :=
    (hcons _ _).1 (by show (ctMap_ _).isSome = true; rw [show ctMap_ _ = _ from hgood.2.1.1]; rfl)
  have hlist : list_type_num < st.next_type_stamp :=
    (hcons _ _).1 (by show (ctMap_ _).isSome = true; rw [show ctMap_ _ = _ from hgood.2.2.2.1]; rfl)
  have hok' : ctMap_ok c' := by
    rw [hunion]
    refine ctMap_ok_merge_imp _ _ ⟨?_, ?_, hgood.1⟩
    · rintro x ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
      simp only [Finmap.o_f] at hk hk'
      rw [FUPDATE_LIST_reverse_apply] at hk
      cases hL : ALOOKUP L k with
      | none => rw [hL] at hk; cases hk
      | some y =>
        rw [hL] at hk
        simp only [Option.some_or, Option.map_some, Option.some.injEq] at hk
        subst hk
        cases hc : ctMap_ k' with
        | none => rw [hc] at hk'; cases hk'
        | some z =>
          rw [hc] at hk'
          simp only [Option.map_some, Option.some.injEq] at hk'
          exact hdisj _ ⟨hF2 _ _ hL, ⟨k', by simp only [Finmap.o_f, hc, Option.map_some, hk']⟩⟩
    · refine ctMap_ok_type_defs _ _ _ _ ⟨h1, fun x hx => h2 x ⟨hx.1, ?_⟩, h4.symm, h3, hokext.2.2⟩
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx.2)
  have hallnew : type_all_env c' tenvS (.mk nsEmpty (build_tdefs st.next_type_stamp tdefs))
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities,
        t := tenvT } :=
    ⟨build_tdefs_build_tenv _ _ _ _ _ ⟨hevery, h4.symm⟩, nsAll2_nsEmpty _⟩
  refine ⟨c', tenvS, hw, hrange, store_type_extension_refl _, hallnew, hokext,
    good_ctMap_extend hgood hok' hw (fun cn k hk => ?_),
    ⟨fun _ hx => hx.1, fun cn' id_ => ⟨fun hm => ?_, fun hm => ?_⟩⟩,
    type_all_env_extend _ _ _ _ _ _ ⟨hallnew, type_all_env_weakening _ _ _ _ _ _
      ⟨hw, weakS_refl _, hall⟩⟩,
    type_s_weakening _ _ _ _ ⟨hts, hw⟩⟩
  · rw [hlook, hfresh_lt _ _ (by rcases hk with rfl | rfl <;> assumption), Option.none_or]
  · show id_ < st.next_type_stamp + tdefs.length
    have hm' : (c' (.TypeStamp cn' id_)).isSome = true := hm
    rw [hlook] at hm'
    cases hL : ALOOKUP L (.TypeStamp cn' id_) with
    | some y =>
      obtain ⟨_, _, he, _, hlt⟩ := hF1 _ _ hL
      cases he; exact hlt
    | none =>
      rw [hL, Option.none_or] at hm'
      have := (hcons cn' id_).1 hm'
      omega
  · show id_ < st.next_exn_stamp
    have hm' : (c' (.ExnStamp id_)).isSome = true := hm
    rw [hlook] at hm'
    cases hL : ALOOKUP L (.ExnStamp id_) with
    | some y =>
      obtain ⟨_, _, he, _, _⟩ := hF1 _ _ hL
      cases he
    | none =>
      rw [hL, Option.none_or] at hm'
      exact (hcons cn' id_).2 hm'

theorem decs_sound_dtabbrev (b : Bool) (tenv : type_env) (locs : locs) (tvs : List tvarN)
    (tn : typeN) (t : ast_t)
    (hd : type_d b tenv (.Dtabbrev locs tvs tn t) ∅
      { v := nsEmpty, c := nsEmpty, t := nsSing tn (tvs, type_name_subst tenv.t t) }) :
    decs_sound_motive tenv [.Dtabbrev locs tvs tn t] ∅
      { v := nsEmpty, c := nsEmpty, t := nsSing tn (tvs, type_name_subst tenv.t t) } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  simp only [evaluate_decs, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact decs_concl_simple hinv (type_d_tenv_ok _ _ _ _ _ ⟨hd, hinv.1⟩)
    ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩

theorem decs_sound_dexn (b : Bool) (tenv : type_env) (locs : locs) (cn : conN) (ts : List ast_t)
    (hd : type_d b tenv (.Dexn locs cn ts) ∅
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty })
    (h1 : ∀ t', t' ∈ ts → check_freevars_ast [] t')
    (h2 : ∀ t', t' ∈ ts → check_type_names tenv.t t') :
    decs_sound_motive tenv [.Dexn locs cn ts] ∅
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  simp only [evaluate_decs, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hok, hgood, ⟨_, hcons⟩, hall, hts⟩ := hinv
  have hnone : ctMap_ (.ExnStamp st.next_exn_stamp) = none := by
    cases hc : ctMap_ (.ExnStamp st.next_exn_stamp) with
    | none => rfl
    | some _ =>
      have := (hcons cn st.next_exn_stamp).2
        (by show (ctMap_ _).isSome = true; rw [hc]; rfl)
      omega
  let c' : ctMap := Finmap.FUPDATE ctMap_
    (.ExnStamp st.next_exn_stamp, ([], ts.map (type_name_subst tenv.t), Texn_num))
  have hnew : c' (.ExnStamp st.next_exn_stamp) =
      some ([], ts.map (type_name_subst tenv.t), Texn_num) := by
    simp [c', Finmap.FUPDATE]
  have hold : ∀ k, k ≠ .ExnStamp st.next_exn_stamp → c' k = ctMap_ k := by
    intro k hk
    simp [c', Finmap.FUPDATE, hk]
  have hw : weakCT c' ctMap_ := by
    intro k x hk
    by_cases hk' : k = .ExnStamp st.next_exn_stamp
    · subst hk'; rw [hnone] at hk; cases hk
    · rw [hold k hk']; exact hk
  have hok' : ctMap_ok c' := by
    obtain ⟨⟨f1, f2, f3, f4⟩, _, _, _⟩ := hgood
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k x hk
      by_cases hk' : k = .ExnStamp st.next_exn_stamp
      · subst hk'; rw [hnew] at hk; cases hk
        show EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t)) = true
        simp only [EVERY, List.all_map, List.all_eq_true]
        intro t ht
        exact check_freevars_type_name_subst [] t 0 tenv.t ⟨hok.2.2, h2 t ht, h1 t ht⟩
      · rw [hold k hk'] at hk; exact f1 k x hk
    · intro ex tvs ts0 ti hk
      by_cases hk' : stamp.ExnStamp ex = .ExnStamp st.next_exn_stamp
      · simp only [Finmap.FLOOKUP] at hk
        rw [hk', hnew] at hk; cases hk; exact ⟨rfl, rfl⟩
      · simp only [Finmap.FLOOKUP] at hk ⊢
        rw [hold _ hk'] at hk; exact f2 _ _ _ _ hk
    · intro cn x tvs ts0 ti hk
      simp only [Finmap.FLOOKUP] at hk
      rw [hold _ (by intro h; cases h)] at hk; exact f3 _ _ _ _ _ hk
    · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨hk1, hk2⟩
      simp only [Finmap.FLOOKUP] at hk1 hk2
      have hprim : prim_type_nums.elem Texn_num = true := by decide
      by_cases e1 : s1 = .ExnStamp st.next_exn_stamp <;>
        by_cases e2 : s2 = .ExnStamp st.next_exn_stamp
      · subst e1; subst e2; rfl
      · subst e1; rw [hnew] at hk1; cases hk1
        rw [hold _ e2] at hk2
        cases s2 with
        | TypeStamp cn x => exact absurd hprim (f3 _ _ _ _ _ hk2)
        | ExnStamp _ => rfl
      · subst e2; rw [hnew] at hk2; cases hk2
        rw [hold _ e1] at hk1
        cases s1 with
        | TypeStamp cn x => exact absurd hprim (f3 _ _ _ _ _ hk1)
        | ExnStamp _ => rfl
      · rw [hold _ e1] at hk1; rw [hold _ e2] at hk2
        exact f4 _ _ _ _ _ _ _ ⟨hk1, hk2⟩
  have hrange : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ ∅ := by
    rintro x ⟨⟨k, hk⟩, hnot⟩
    by_cases hk' : k = .ExnStamp st.next_exn_stamp
    · subst hk'
      simp only [Finmap.o_f, hnew, Option.map_some, Option.some.injEq] at hk
      subst hk
      have hb : ctMap_ bind_stamp = some ([], [], Texn_num) := hgood.2.2.1.1
      exact hnot ⟨bind_stamp, by simp only [Finmap.o_f]; rw [hb]; rfl⟩
    · simp only [Finmap.o_f, hold k hk'] at hk
      exact hnot ⟨k, hk⟩
  have hallnew : type_all_env c' tenvS
      (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp)))
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } :=
    ⟨(nsAll2_nsSing _ _ _ _ _).2 ⟨rfl, hnew, by simp⟩, nsAll2_nsEmpty _⟩
  refine ⟨c', tenvS, hw, hrange, store_type_extension_refl _, hallnew,
    type_d_tenv_ok _ _ _ _ _ ⟨hd, hok⟩,
    good_ctMap_extend hgood hok' hw (fun cn k _ => hold _ (by intro h; cases h)),
    ⟨fun _ hx => hx.1, fun cn' id_ => ⟨fun hm => ?_, fun hm => ?_⟩⟩,
    type_all_env_extend _ _ _ _ _ _ ⟨hallnew, type_all_env_weakening _ _ _ _ _ _
      ⟨hw, weakS_refl _, hall⟩⟩,
    type_s_weakening _ _ _ _ ⟨hts, hw⟩⟩
  · have hm' : (ctMap_ (.TypeStamp cn' id_)).isSome = true := by
      rw [← hold _ (by intro h; cases h)]; exact hm
    exact (hcons cn' id_).1 hm'
  · show id_ < st.next_exn_stamp + 1
    by_cases hid : id_ = st.next_exn_stamp
    · omega
    · have hm' : (ctMap_ (.ExnStamp id_)).isSome = true := by
        rw [← hold _ (by intro h; cases h; exact hid rfl)]; exact hm
      have := (hcons cn' id_).2 hm'
      omega

theorem decs_sound_dmod (b : Bool) (tenv : type_env) (mn : modN) (ds : List dec)
    (decls : Set type_ident) (tenv' : type_env)
    (hd : type_d b tenv (.Dmod mn ds) decls (tenvLift mn tenv'))
    (ih : decs_sound_motive tenv ds decls tenv') :
    decs_sound_motive tenv [.Dmod mn ds] decls (tenvLift mn tenv') := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  rw [evaluate_decs] at h
  rcases h1 : evaluate_decs st env ds with ⟨st1, r1⟩
  rw [h1] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨ctMap1, tenvS1, hw1, hr1, hs1, hres⟩ := ih st env st1 r1 ctMap_ tenvS h1 hinv
  refine ⟨ctMap1, tenvS1, hw1, hr1, hs1, ?_⟩
  rcases r1 with env1 | (err_v | (_ | _ | _))
  · have hlift : type_all_env ctMap1 tenvS1
        (.mk (nsLift mn env1.v_) (nsLift mn env1.c)) (tenvLift mn tenv') :=
      ⟨(nsAll2_nsLift _ _ _ _).2 hres.1.1, (nsAll2_nsLift _ _ _ _).2 hres.1.2⟩
    refine ⟨hlift, type_d_tenv_ok _ _ _ _ _ ⟨hd, hinv.1⟩, hres.2.2.1, hres.2.2.2.1,
      type_all_env_extend _ _ _ _ _ _ ⟨hlift, ?_⟩, hres.2.2.2.2.2⟩
    exact type_all_env_weakening _ _ _ _ _ _ ⟨hw1, store_type_extension_weakS _ _ hs1, hinv.2.2.2.1⟩
  · exact hres
  · exact hres
  · exact hres
  · exact hres

theorem decs_sound_dlocal (b : Bool) (tenv : type_env) (lds ds : List dec)
    (decls1 decls2 : Set type_ident) (tenv1 tenv2 : type_env)
    (hds : type_ds b (extend_dec_tenv tenv1 tenv) ds decls2 tenv2)
    (hdisj : Set.Disjoint decls1 decls2)
    (ih1 : decs_sound_motive tenv lds decls1 tenv1)
    (ih2 : decs_sound_motive (extend_dec_tenv tenv1 tenv) ds decls2 tenv2) :
    decs_sound_motive tenv [.Dlocal lds ds] (decls1 ∪ decls2) tenv2 := by
  intro ffi st env st' r ctMap_ tenvS h hinv
  rw [evaluate_decs] at h
  split at h
  · rename_i st1 env1 h1
    rw [fix_clock_evaluate2] at h1
    obtain ⟨ctMap1, tenvS1, hw1, hr1, hs1, hall1, hinv1⟩ :=
      ih1 st env st1 _ ctMap_ tenvS h1 (type_sound_invariant_union _ _ _ _ _ _ _ hinv)
    obtain ⟨ctMap2, tenvS2, hw2, hr2, hs2, hres⟩ :=
      ih2 st1 _ st' r ctMap1 tenvS1 h (decs_seq_invariant hinv hdisj hr1 hinv1)
    obtain ⟨hw, hr, hs⟩ := decs_seq_frame hw1 hw2 hr1 hr2 hs1 hs2
    refine ⟨ctMap2, tenvS2, hw, hr, hs, ?_⟩
    rcases r with env2 | (err_v | (_ | _ | _))
    · refine ⟨hres.1, extend_dec_tenv_ok _ _ ⟨type_d_tenv_ok_helper.2 _ _ _ _ _ hds hinv1.1, hinv.1⟩,
        hres.2.2.1, hres.2.2.2.1, type_all_env_extend _ _ _ _ _ _ ⟨hres.1, ?_⟩, hres.2.2.2.2.2⟩
      exact type_all_env_weakening _ _ _ _ _ _ ⟨hw, store_type_extension_weakS _ _ hs, hinv.2.2.2.1⟩
    · exact ⟨hres.1, inv_restore hres.2 hinv.1 hinv.2.2.2.1 hw hs⟩
    · exact hres
    · exact hres
    · exact hres
  · rename_i st1 e h1
    rw [fix_clock_evaluate2] at h1
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact decs_sound_concl_err_mono (ih1 st env st1 _ ctMap_ tenvS h1
      (type_sound_invariant_union _ _ _ _ _ _ _ hinv)) (fun _ hx => Or.inl hx)

theorem decs_sound_all (b : Bool) (tenv : type_env) (ds : List dec) (tids : Set type_ident)
    (tenv' : type_env) (h : type_ds b tenv ds tids tenv') :
    decs_sound_motive tenv ds tids tenv' := by
  induction h using type_ds.rec
    (motive_1 := fun tenv d tids tenv' _ => decs_sound_motive tenv [d] tids tenv') with
  | dlet_poly tenv locs p e tvs t bindings hv hd hp he h5 =>
    exact decs_sound_dlet b tenv locs p e tvs t bindings (.dlet_poly b _ _ _ _ _ _ _ hv hd hp he h5)
      (fun _ => hv) hd hp he
  | dlet_mono tenv locs p e t bindings h1 hd hp he =>
    exact decs_sound_dlet b tenv locs p e 0 t bindings (.dlet_mono b _ _ _ _ _ _ h1 hd hp he)
      (fun h => absurd rfl h) hd hp he
  | dletrec tenv locs funs tvs bindings hf h2 =>
    exact decs_sound_dletrec b tenv locs funs tvs bindings (.dletrec b _ _ _ _ _ hf h2) hf
  | dtype tenv locs tdefs tids tenvT h1 h2 h3 h4 h5 =>
    subst h5
    exact decs_sound_dtype b tenv locs tdefs tids _ (.dtype b _ _ _ _ _ h1 h2 h3 h4 rfl) h1 h2 h3 h4
  | dtabbrev tenv locs tvs tn t h1 h2 h3 =>
    exact decs_sound_dtabbrev b tenv locs tvs tn t (.dtabbrev b _ _ _ _ _ h1 h2 h3)
  | dexn tenv locs cn ts h1 h2 =>
    exact decs_sound_dexn b tenv locs cn ts (.dexn b _ _ _ _ h1 h2) h1 h2
  | dmod tenv mn ds decls tenv' hds ih =>
    exact decs_sound_dmod b tenv mn ds decls tenv' (.dmod b _ _ _ _ _ hds) ih
  | dlocal tenv lds ds decls1 tenv1 decls2 tenv2 _ h2 h3 ih1 ih2 =>
    exact decs_sound_dlocal b tenv lds ds decls1 decls2 tenv1 tenv2 h2 h3 ih1 ih2
  | nil tenv => exact decs_sound_nil tenv
  | cons tenv d ds decls1 tenv1 decls2 tenv2 _ h2 h3 ih1 ih2 =>
    exact decs_sound_cons b tenv d ds decls1 decls2 tenv1 tenv2 h2 h3 ih1 ih2

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
        | .Rerr (.Rabort (.Rffi_error _)) => True := by
  intro ffi st env ds st' r ctMap_ tenvS tenv tids tenv' ⟨h1, h2, h3⟩
  exact decs_sound_all false tenv ds tids tenv' h2 st env st' r ctMap_ tenvS h1 h3
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
        | .Rerr (.Rabort .Rtimeout_error) => True := by
  intro ffi st env ds extra_checks st' r ctMap_ tenvS tenv tids tenv' ⟨h1, h2, h3⟩
  obtain ⟨c, s, hw, hr, hs, hres⟩ :=
    decs_sound_all extra_checks tenv ds tids tenv' h2 st env st' r ctMap_ tenvS h1 h3
  exact ⟨c, s, hw, hr, hs, by rcases r with _ | (_ | (_ | _ | _)) <;> exact hres⟩
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
      r ≠ .Fail := by
  intro ffi st env tops r checks ctMap_ tenvS tenv new_tenv tids ⟨hsem, hty, hinv⟩ hr
  subst hr
  obtain ⟨k, hk⟩ := hsem
  simp only [evaluate_prog_with_clock] at hk
  rcases he : evaluate_decs { st with clock := k } env tops with ⟨st', r⟩
  rw [he] at hk
  simp only at hk
  subst hk
  obtain ⟨_, _, _, _, _, hres⟩ :=
    decs_sound_all checks tenv tops tids new_tenv hty { st with clock := k } env st' _ ctMap_
      tenvS he hinv
  exact hres

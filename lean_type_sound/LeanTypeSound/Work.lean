import LeanTypeSound.TypeSysProps
open HOL4

theorem FUPDATE_LIST_reverse_eq_alist {α β : Type} [BEq α] (l : List (α × β)) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse = Finmap.alist_to_fmap l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [Finmap.FUPDATE_LIST, List.reverse_cons, List.foldl_append, List.foldl] at ih ⊢
    rw [ih]
    funext k
    simp only [Finmap.FUPDATE, Finmap.alist_to_fmap, List.find?]
    split <;> simp_all

theorem ALOOKUP_map_snd_some {α β : Type} [BEq α] (f : β → β) :
    ∀ (l : List (α × β)) (k : α) (v : β), ALOOKUP l k = some v →
      ALOOKUP (l.map (fun (x, t) => (x, f t))) k = some (f v)
  | [], _, _, h => by simp [ALOOKUP] at h
  | (a, b) :: l, k, v, h => by
    simp only [ALOOKUP] at h
    simp only [List.map, ALOOKUP]
    split at h
    · rename_i he; simp only [he]; simp at h; rw [h]; rfl
    · rename_i hne; simp only [hne]; exact ALOOKUP_map_snd_some f l k v h

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (n : Nat)
    (h : n < l.length) : (l.map f)[n]! = f l[n]! := EL_map' f l n h

theorem type_subst_thm2 :
    ∀ (targs : List sem_t) (tvs' : Nat),
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs ctMap_ tenvS v_ t →
      tvs = targs.length ∧
      ctMap_ok ctMap_ ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars targs.length [] t →
      type_v tvs' ctMap_ tenvS v_ (deBruijn_subst 0 targs t) := by
  intro targs tvs'' tvs ctMap_ tenvS v_ t h
  have hfvσ : EVERY (check_freevars tvs'' []) targs → ∀ t, check_freevars targs.length [] t →
      check_freevars tvs'' [] (deBruijn_subst 0 targs t) := by
    intro hev t ht
    have := check_freevars_subst _ _ t ht 0 targs tvs'' ⟨by simp, by simpa using hev⟩
    simpa using this
  have hbt : ∀ a E, tenv_val_exp_ok E → tenv_val_exp_ok (bind_tvar a E) := by
    intro a E hE; unfold bind_tvar; split
    · exact hE
    · exact hE
  induction h with
  | litv_int => intro _; simpa [Tint, deBruijn_subst] using type_v.litv_int _ _ _ _
  | litv_char => intro _; simpa [Tchar, deBruijn_subst] using type_v.litv_char _ _ _ _
  | litv_str => intro _; simpa [Tstring, deBruijn_subst] using type_v.litv_str _ _ _ _
  | litv_word8 => intro _; simpa [Tword8, deBruijn_subst] using type_v.litv_word8 _ _ _ _
  | litv_word64 => intro _; simpa [Tword64, deBruijn_subst] using type_v.litv_word64 _ _ _ _
  | litv_float64 => intro _; simpa [Tdouble, deBruijn_subst] using type_v.litv_float64 _ _ _ _
  | conv_some tvs ctMap_ tenvS ts' tvs' vs ts ti stmp hts hlen hvl hall hlk ih =>
    intro ⟨hL, hok, hev, hc⟩
    subst hL
    rw [FUPDATE_LIST_reverse_eq_alist] at hvl hall ih
    have hcl : EVERY (check_freevars 0 tvs') ts := hok.1 stmp _ hlk
    have heq := type_subst_deBruijn_subst_list (.Tvar_db 0) tvs' tvs' ts' targs ts 0 ⟨hlen, hcl⟩
    simp only [ZIP] at heq
    simp only [deBruijn_subst]
    refine .conv_some _ _ _ (ts'.map (deBruijn_subst 0 targs)) tvs' vs ts ti stmp ?_ (by simpa using hlen) ?_ ?_ hlk
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact hfvσ hev t0 (hts t0 ht0)
    · rw [FUPDATE_LIST_reverse_eq_alist]; simpa using hvl
    · intro i hi
      rw [FUPDATE_LIST_reverse_eq_alist, ← heq]
      have hi' : i < (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))).length := by
        rw [← hvl]; exact hi
      rw [getElem!_map' _ _ _ hi']
      refine ih i hi ⟨rfl, hok, hev, ?_⟩
      have hi2 : i < ts.length := by simpa using hi'
      rw [getElem!_map' _ _ _ hi2]
      have hmem : ts[i]! ∈ ts := EL_mem' ts i hi2
      have := check_freevars_subst_single targs.length tvs' ts[i]! [] ts'
        ⟨hlen, check_freevars_add _ _ _ (by simp only [EVERY, List.all_eq_true] at hcl; exact hcl _ hmem) _ (Nat.zero_le _),
         by simpa [EVERY] using hts⟩
      simpa [ZIP] using this
  | conv_none tvs ctMap_ tenvS vs ts hl hall ih =>
    intro ⟨hL, hok, hev, hc⟩
    simp only [Ttup, deBruijn_subst]
    refine .conv_none _ _ _ _ _ (by simpa using hl) ?_
    intro i hi
    have hi2 : i < ts.length := by omega
    rw [getElem!_map' _ _ _ hi2]
    refine ih i hi ⟨hL, hok, hev, ?_⟩
    simp only [Ttup, check_freevars_Tapp, List.all_eq_true] at hc
    exact hc _ (EL_mem' ts i hi2)
  | closure tvs ctMap_ tenvS tenv tenvE env n e t1 t2 hok hE h0 hc' hdom hp1 hp2 htyp ht1 he _ =>
    intro ⟨hL, hok', hev, hc⟩
    subst hL
    simp only [Tfn, deBruijn_subst, List.map]
    have he' := type_e_subst_lem n t1 tenv tenvE e t2 targs tvs'' targs
      ⟨he, h0, hok.2.2, hok.2.1, hok.1, hbt _ _ hE, hev, ht1⟩
    exact .closure _ _ _ tenv tenvE env n e _ _ hok hE h0 hc' hdom hp1 hp2 htyp (hfvσ hev t1 ht1) he'
  | recclosure tvs ctMap_ tenvS tenv tenvE env n funs bindings t hok hE h0 hc' hdom hp1 hp2 htyp hf hl hd hm _ =>
    intro ⟨hL, hok', hev, hc⟩
    subst hL
    refine .recclosure _ _ _ tenv tenvE env n funs
      (bindings.map (fun (x, t) => (x, deBruijn_subst 0 targs t))) _ hok hE h0 hc' hdom hp1 hp2 htyp
      ?_ (ALOOKUP_map_snd_some _ _ _ _ hl) hd hm
    have hokb := tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v _ ⟨hf, hbt targs.length _ hE⟩
    have := (type_e_subst tenvE).2.2 tenv _ funs bindings hf (bind_var_list 0 bindings .Empty) targs tvs''
      (targs.map (deBruijn_inc 0 0))
      ⟨h0, hok.2.2, hok.2.1, hok.1, hokb, hev, by rw [db_merge_bvl]; rfl, by simp [num_tvs_bind_var_list, num_tvs]⟩
    rw [deBruijn_subst_E_bvl, db_merge_bvl] at this
    simpa [num_tvs_bind_var_list, num_tvs, deBruijn_subst_tenvE, db_merge, deBruijn_inc0.2] using this
  | loc_ref tvs ctMap_ tenvS t n hc0 hlk =>
    intro _
    simp only [Tref, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    exact .loc_ref _ _ _ _ _ hc0 hlk
  | loc_w8array tvs ctMap_ tenvS n hlk =>
    intro _
    simpa [Tword8array, deBruijn_subst] using type_v.loc_w8array tvs'' _ _ _ hlk
  | loc_varray tvs ctMap_ tenvS t n hc0 hlk =>
    intro _
    simp only [Tarray, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    exact .loc_varray _ _ _ _ _ hc0 hlk
  | vectorv tvs ctMap_ tenvS t vs hc0 hall ih =>
    intro ⟨hL, hok, hev, hc⟩
    simp only [Tvector, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    refine .vectorv _ _ _ t vs hc0 ?_
    intro w hw
    have := ih w hw ⟨hL, hok, hev, check_freevars_add 0 [] t hc0 _ (Nat.zero_le _)⟩
    rwa [nil_deBruijn_subst 0 targs t hc0] at this

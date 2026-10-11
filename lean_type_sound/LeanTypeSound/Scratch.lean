import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.Tactics
open HOL4

set_option maxHeartbeats 4000000 in
theorem do_app_cases_bwd {ffi : Type} :
    ∀ (s : List (store_v v)) (t : ffi_state ffi) (op_ : op) (vs : List v)
      (st' : List (store_v v) × ffi_state ffi) (r : result v v),
    
    ( -- ListAppend
      (∃ x1 x2 xs ys, op_ = .ListAppend ∧ vs = [x1, x2] ∧
        v_to_list x1 = some xs ∧ v_to_list x2 = some ys ∧
        st' = (s, t) ∧ r = .Rval (list_to_v (xs ++ ys))) ∨
      -- Shift W8
      (∃ sh n w, op_ = .Shift .W8 sh n ∧ vs = [.Litv (.Word8 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (shift8_lookup sh w n)))) ∨
      -- Shift W64
      (∃ sh n w, op_ = .Shift .W64 sh n ∧ vs = [.Litv (.Word64 w)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word64 (shift64_lookup sh w n)))) ∨
      -- Equality
      (∃ v1 v2 b, op_ = .Equality ∧ vs = [v1, v2] ∧
        do_eq v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b)) ∨
      -- Opassign
      (∃ b lnum val_ s', op_ = .Opassign ∧ vs = [.Loc b lnum, val_] ∧
        store_assign lnum (.Refv val_) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Opref
      (∃ val_ s' n, op_ = .Opref ∧ vs = [val_] ∧
        store_alloc (.Refv val_) s = (s', n) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true n)) ∨
      -- Opderef
      (∃ b n val_, op_ = .Opderef ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Refv val_) ∧
        st' = (s, t) ∧ r = .Rval val_) ∨
      -- Aw8alloc
      (∃ n w, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n w s' lnum, op_ = .Aw8alloc ∧ vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
        ¬ n < 0 ∧
        store_alloc (.W8array (REPLICATE n.natAbs w)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Aw8sub
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i ws, op_ = .Aw8sub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8sub_unsafe
      (∃ b lnum i ws, op_ = .Aw8sub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Word8 (EL i.natAbs ws)))) ∨
      -- Aw8length
      (∃ b n ws, op_ = .Aw8length ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.W8array ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aw8update
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws, op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ i.natAbs ≥ ws.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i w ws s', op_ = .Aw8update ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aw8update_unsafe
      (∃ b lnum i w ws s', op_ = .Aw8update_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ ws.length ∧
        store_assign lnum (.W8array (LUPDATE w i.natAbs ws)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyStrStr
      (∃ strng off len, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len cs, op_ = .CopyStrStr ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        copy_array (explode strng, off) len none = some cs ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk cs))))) ∨
      -- CopyStrAw8
      (∃ strng off len b dst dstoff ws, op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng off len b dst dstoff ws cs s', op_ = .CopyStrAw8 ∧
        vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b dst, .Litv (.IntLit dstoff)] ∧
        store_lookup dst s = some (.W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = some cs ∧
        store_assign dst (.W8array (chars_to_ws cs)) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- CopyAw8Str
      (∃ b src off len ws, op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len ws ws', op_ = .CopyAw8Str ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
        store_lookup src s = some (.W8array ws) ∧
        copy_array (ws, off) len none = some ws' ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk (ws_to_chars ws')))))) ∨
      -- CopyAw8Aw8
      (∃ b src off len b' dst dstoff ws ds, op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = none ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b src off len b' dst dstoff ws ds ws' s', op_ = .CopyAw8Aw8 ∧
        vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len),
              .Loc b' dst, .Litv (.IntLit dstoff)] ∧
        store_lookup src s = some (.W8array ws) ∧
        store_lookup dst s = some (.W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
        store_assign dst (.W8array ws') s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- XorAw8Str_unsafe
      (∃ b dst str_arg bs new_bs s', op_ = .XorAw8Str_unsafe ∧
        vs = [.Loc b dst, .Litv (.StrLit str_arg)] ∧
        store_lookup dst s = some (.W8array bs) ∧
        xor_bytes ((explode str_arg).map (fun c => n2w_8 (ORD c))) bs = some new_bs ∧
        store_assign dst (.W8array new_bs) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Implode
      (∃ val_ ls, op_ = .Implode ∧ vs = [val_] ∧
        v_to_char_list val_ = some ls ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit (implode (String.mk ls))))) ∨
      -- Explode
      (∃ strng, op_ = .Explode ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧
        r = .Rval (list_to_v ((explode strng).map (fun c => .Litv (.Char c))))) ∨
      -- Strsub
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ strng i, op_ = .Strsub ∧ vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ strlen strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.Char (EL i.natAbs (explode strng))))) ∨
      -- Strlen
      (∃ strng, op_ = .Strlen ∧ vs = [.Litv (.StrLit strng)] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat (strlen strng))))) ∨
      -- Strcat
      (∃ val_ vs' strng, op_ = .Strcat ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        vs_to_string vs' = some strng ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.StrLit strng))) ∨
      -- VfromList
      (∃ val_ vs', op_ = .VfromList ∧ vs = [val_] ∧
        v_to_list val_ = some vs' ∧
        st' = (s, t) ∧ r = .Rval (.Vectorv vs')) ∨
      -- Vsub_unsafe
      (∃ vs' i, op_ = .Vsub_unsafe ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        (0 ≤ i ∧ i.natAbs < vs'.length) ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vsub
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ vs' i, op_ = .Vsub ∧ vs = [.Vectorv vs', .Litv (.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Vlength
      (∃ vs', op_ = .Vlength ∧ vs = [.Vectorv vs'] ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat vs'.length)))) ∨
      -- Aalloc
      (∃ n val_, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        n < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ n val_ s' lnum, op_ = .Aalloc ∧ vs = [.Litv (.IntLit n), val_] ∧
        ¬ n < 0 ∧
        store_alloc (.Varray (REPLICATE n.natAbs val_)) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocEmpty
      (∃ s' lnum, op_ = .AallocEmpty ∧ vs = [.Conv none []] ∧
        store_alloc (.Varray []) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- AallocFixed (any argument list)
      (∃ s' lnum, op_ = .AallocFixed ∧
        store_alloc (.Varray vs) s = (s', lnum) ∧
        st' = (s', t) ∧ r = .Rval (.Loc true lnum)) ∨
      -- Asub
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i vs', op_ = .Asub ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Asub_unsafe
      (∃ b lnum i vs', op_ = .Asub_unsafe ∧ vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rval (EL i.natAbs vs')) ∨
      -- Alength
      (∃ b n ws, op_ = .Alength ∧ vs = [.Loc b n] ∧
        store_lookup n s = some (.Varray ws) ∧
        st' = (s, t) ∧ r = .Rval (.Litv (.IntLit (Int.ofNat ws.length)))) ∨
      -- Aupdate
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        i < 0 ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ i.natAbs ≥ vs'.length ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise sub_exn_v)) ∨
      (∃ b lnum i val_ vs' s', op_ = .Aupdate ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- Aupdate_unsafe
      (∃ b lnum i val_ vs' s', op_ = .Aupdate_unsafe ∧
        vs = [.Loc b lnum, .Litv (.IntLit i), val_] ∧
        store_lookup lnum s = some (.Varray vs') ∧
        ¬ i < 0 ∧ ¬ i.natAbs ≥ vs'.length ∧
        store_assign lnum (.Varray (LUPDATE val_ i.natAbs vs')) s = some s' ∧
        st' = (s', t) ∧ r = .Rval (.Conv none [])) ∨
      -- ConfigGC
      (∃ i j, op_ = .ConfigGC ∧ vs = [.Litv (.IntLit i), .Litv (.IntLit j)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [])) ∨
      -- FFI
      (∃ n conf b lnum ws t' ws' s', op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_return t' ws' ∧
        store_assign lnum (.W8array ws') s = some s' ∧
        st' = (s', t') ∧ r = .Rval (.Conv none [])) ∨
      (∃ n conf b lnum ws outcome, op_ = .FFI n ∧
        vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
        store_lookup lnum s = some (.W8array ws) ∧
        call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w_8 (ORD c))) ws =
          .FFI_final outcome ∧
        st' = (s, t) ∧ r = .Rerr (.Rabort (.Rffi_error outcome))) ∨
      -- Env_id
      (∃ env gen id_, op_ = .Env_id ∧ vs = [.Env env (gen, id_)] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [nat_to_v gen, nat_to_v id_])) ∨
      (∃ gen id_, op_ = .Env_id ∧ vs = [.Conv none [gen, id_]] ∧
        st' = (s, t) ∧ r = .Rval (.Conv none [gen, id_])) ∨
      -- ThunkOp (any argument list; thunk_op_fun stays folded)
      (∃ th_op, op_ = .ThunkOp th_op ∧
        thunk_op_fun (s, t) th_op vs = some (st', r)) ∨
      -- Arith (any argument list)
      (∃ a ty res, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ a ty exn, op_ = .Arith a ty ∧
        EVERY (check_type ty) vs = true ∧
        do_arith a ty vs = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- FromTo
      (∃ ty1 ty2 val_ res, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inr res) ∧
        st' = (s, t) ∧ r = .Rval res) ∨
      (∃ ty1 ty2 val_ exn, op_ = .FromTo ty1 ty2 ∧ vs = [val_] ∧
        check_type ty1 val_ = true ∧
        do_conversion val_ ty1 ty2 = some (.inl exn) ∧
        st' = (s, t) ∧ r = .Rerr (.Rraise exn)) ∨
      -- Test
      (∃ test_ test_ty v1 v2 b, op_ = .Test test_ test_ty ∧ vs = [v1, v2] ∧
        do_test test_ test_ty v1 v2 = .Eq_val b ∧
        st' = (s, t) ∧ r = .Rval (Boolv b))) →
    do_app (s, t) op_ vs = some (st', r) := by
  intro s t op_ vs st' r
  simp only [or_imp, forall_exists_index, and_imp]
  repeat' apply And.intro
  all_goals intros
  all_goals subst_vars
  all_goals (try simp_all [do_app])
  all_goals rw [if_neg (by omega), if_neg (by omega)]

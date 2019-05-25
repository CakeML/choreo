open preamble payloadSemanticsTheory payloadLangTheory;

val _ = new_theory "payloadProps";

(* todo: move? *)
val EXISTS_REPLICATE = Q.store_thm("EXISTS_REPLICATE",
  `!f n d. EXISTS f (REPLICATE n d) = (n > 0 /\ f d)`,
  Induct_on `n` >> rw[EQ_IMP_THM]);

val unpad_pad = Q.store_thm("unpad_pad",
  `!conf d. unpad(pad conf d) = TAKE conf.payload_size d`,
  rw[pad_def,unpad_def,SPLITP_APPEND,EXISTS_REPLICATE,SPLITP]
  >> TRY(first_x_assum(assume_tac o GSYM)
         >> rw[TAKE_LENGTH_ID] >> NO_TAC)
  >> imp_res_tac LESS_IMP_LESS_OR_EQ
  >> rw[TAKE_LENGTH_TOO_LONG]);

val pad_LENGTH = Q.store_thm("pad_LENGTH",
  `!conf d. LENGTH(pad conf d) = conf.payload_size + 1`,
  rw[pad_def]);

val unpad_pad_LENGTH = Q.store_thm("unpad_pad_LENGTH",
  `!conf d. LENGTH(unpad(pad conf d)) <= conf.payload_size`,
  rw[unpad_pad,LENGTH_TAKE_EQ]);

val final_pad_LENGTH = Q.store_thm("final_pad_LENGTH",
  `!conf d. final(pad conf d) <=> LENGTH d <= conf.payload_size`,
  rw[pad_def,final_def])

val final_pad_TAKE = Q.store_thm("final_pad_TAKE",
  `!conf d. final(pad conf d) ==> TAKE conf.payload_size d = d`,
  metis_tac[final_pad_LENGTH,TAKE_LENGTH_TOO_LONG])
                                  
val intermediate_pad_LENGTH = Q.store_thm("intermediate_pad_LENGTH",
  `!conf d. intermediate(pad conf d) <=> conf.payload_size < LENGTH d`,
  rw[pad_def,intermediate_def])

val pad_not_final = Q.store_thm("pad_not_final",
  `!conf d. ¬final (pad conf d) <=> intermediate(pad conf d)`,
  rw[final_def,pad_def,intermediate_def]);

val pad_not_intermediate = Q.store_thm("pad_not_intermediate",
  `!conf d. ¬intermediate (pad conf d) <=> final(pad conf d)`,
  metis_tac[pad_not_final]);

val endpoints_def = Define `
   (endpoints NNil = [])
/\ (endpoints (NEndpoint p1 s e1) = [(p1,s,e1)])
/\ (endpoints (NPar n1 n2) = endpoints n1 ++ endpoints n2)`

val (qcong_rules, qcong_ind, qcong_cases) = Hol_reln `
  (* Reflexive *)
  (∀n. qcong n n)

  (* Symmetric *)
∧ (∀n1 n2.
    qcong n1 n2
    ⇒ qcong n2 n1)
  (* Transitive *)
∧ (∀n1 n2 n3.
     qcong n1 n2
     ∧ qcong n2 n3
     ⇒ qcong n1 n3)

  (* Queue-Reorder *)
∧ (∀p s e p1 d1 p2 d2 q1 q2.
    s.queue = q1 ++ [(p1,d1);(p2,d2)] ++ q2
    ∧ p1 ≠ p2
    ⇒ qcong (NEndpoint p s e) (NEndpoint p (s with queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2) e))

  (* Par *)
∧ (∀n1 n2 n3 n4.
     qcong n1 n2
     ∧ qcong n3 n4
     ⇒ qcong (NPar n1 n3) (NPar n2 n4))`

val [qcong_refl,qcong_sym,qcong_trans,qcong_queue_reorder,qcong_par]
    = zip ["qcong_refl","qcong_sym","qcong_trans","qcong_queue_reorder","qcong_par"]
          (CONJUNCTS qcong_rules) |> map save_thm;

val qcong_strongind = fetch "-" "qcong_strongind"

val (qrel_rules, qrel_ind, qrel_cases) = Hol_reln `
  (* Reflexive *)
  (∀q. qrel q q)

  (* Symmetric *)
∧ (∀q1 q2.
    qrel q1 q2
    ⇒ qrel q2 q1)
  (* Transitive *)
∧ (∀q1 q2 q3.
     qrel q1 q2
     ∧ qrel q2 q3
     ⇒ qrel q1 q3)

  (* Queue-Reorder *)
∧ (∀p1 d1 p2 d2 q1 q2.
    p1 ≠ p2
    ⇒ qrel (q1 ++ [(p1,d1);(p2,d2)] ++ q2) (q1 ++ [(p2,d2);(p1,d1)] ++ q2))`

val qrel_strongind = fetch "-" "qrel_strongind"  

val [qrel_refl,qrel_sym,qrel_trans,qrel_queue_reorder]
    = zip ["qrel_refl","qrel_sym","qrel_trans","qrel_queue_reorder"]
          (CONJUNCTS qrel_rules) |> map save_thm;
                           
val qcong_queue_reorder' = Q.store_thm("qcong_queue_reorder'",
  `∀p s e p1 d1 p2 d2 q1 q2.
     p1 ≠ p2
     ⇒ qcong (NEndpoint p (s with queue:=q1 ++ [(p1,d1);(p2,d2)] ++ q2) e)
              (NEndpoint p (s with queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `qcong (NEndpoint _ (_ with queue := a1) _) (NEndpoint _ (_ with queue := a2) _)`
  >> `s with queue := a2 = (s with queue := a1) with queue := a2` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac qcong_queue_reorder
  >> simp[]);

val qrel_IMP_qcong = Q.store_thm("qrel_IMP_qcong",
  `!q1 q2 p s e.
    qrel q1 q2
    ==> qcong (NEndpoint p (s with queue := q1) e) (NEndpoint p (s with queue := q2) e)`,
  simp[GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind
  >> metis_tac[qcong_rules,qcong_queue_reorder'])

val qrel_cons = Q.store_thm("qrel_cons",
  `!q1 q2 qe. qrel q1 q2 ==> qrel (qe::q1) (qe::q2)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >> `!a b. qe::(a ++ b) = qe::a ++ b` by simp[]
  >> ASM_SIMP_TAC pure_ss [] >> pop_assum kall_tac
  >> metis_tac[qrel_rules]);

val qrel_snoc = Q.store_thm("qrel_snoc",
  `!q1 q2 qe. qrel q1 q2 ==> qrel (SNOC qe q1) (SNOC qe q2)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >> simp[SNOC_APPEND]
  >> metis_tac[qrel_rules,APPEND_ASSOC]);

val qrel_append_l = Q.store_thm("qrel_append_l",
  `!q1 q2 q3. qrel q2 q3 ==> qrel (q1++q2) (q1++q3)`,
  Induct >> simp[] >> metis_tac[qrel_cons]);

val qrel_append_r = Q.store_thm("qrel_append_r",
  `!q3 q1 q2. qrel q1 q2 ==> qrel (q1++q3) (q2++q3)`,
  ho_match_mp_tac SNOC_INDUCT >> rpt strip_tac >> simp[APPEND_SNOC] >> metis_tac[qrel_snoc]);

val qrel_append = Q.store_thm("qrel_append",
  `!q1 q2 q3 q4. qrel q1 q2 /\ qrel q3 q4 ==> qrel (q1++q3) (q2++q4)`,
  metis_tac[qrel_rules,qrel_append_l,qrel_append_r]);

val qrel_LENGTH = Q.store_thm("qrel_LENGTH",
  `!q1 q2. qrel q1 q2 ==> LENGTH q1 = LENGTH q2`,
  ho_match_mp_tac qrel_ind >> rw[]);

val qrel_PERM = Q.store_thm("qrel_PERM",
  `!q1 q2. qrel q1 q2 ==> PERM q1 q2`,
  ho_match_mp_tac qrel_strongind
  >> rpt strip_tac
  >> fs[PERM_SYM]
  >- metis_tac[PERM_TRANS]
  >- CONV_TAC permLib.PERM_ELIM_DUPLICATES_CONV);

val qrel_cons_IMP_lemma = Q.prove(
  `!q1l q1r q2 qe. qrel (q1l ++ [qe] ++ q1r) q2 /\ EVERY (λ(p,_). p ≠ FST qe) q1l ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l ++ q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l`,
  `!q1 q2. qrel q1 q2 ==> ((!q1l q1r qe. q1 = q1l ++ [qe] ++ q1r /\ EVERY (λ(p,_). p ≠ FST qe) q1l ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l)
                           /\ (!q2l q2r qe. q2 = q2l ++ [qe] ++ q2r /\ EVERY (λ(p,_). p ≠ FST qe) q2l ==> ?q1l q1r. q1 = q1l ++ [qe] ++ q1r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q1l))`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac >> rveq
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_sym]
  >- metis_tac[qrel_sym]
  >- (last_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l'`,`q2r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (first_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l'`,`q1r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q1l` >> rw[]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p2,d2)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p2,d2); (p1,d1)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC]))
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q2l` >> rw[]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p1,d1)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p1,d1); (p2,d2)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])));

val qrel_snoc_IMP_lemma = Q.prove(
  `!q1l q1r q2 qe. qrel (q1l ++ [qe] ++ q1r) q2 /\ EVERY (λ(p,_). p ≠ FST qe) q1r ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l ++ q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r`,
  `!q1 q2. qrel q1 q2 ==> ((!q1l q1r qe. q1 = q1l ++ [qe] ++ q1r /\ EVERY (λ(p,_). p ≠ FST qe) q1r ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r)
                           /\ (!q2l q2r qe. q2 = q2l ++ [qe] ++ q2r /\ EVERY (λ(p,_). p ≠ FST qe) q2r ==> ?q1l q1r. q1 = q1l ++ [qe] ++ q1r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q1r))`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac >> rveq
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_sym]
  >- metis_tac[qrel_sym]
  >- (last_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l'`,`q2r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (first_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l'`,`q1r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q1l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC,EVERY_APPEND])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p2,d2)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p2,d2); (p1,d1)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC]))
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q2l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC,EVERY_APPEND])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p1,d1)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p1,d1); (p2,d2)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])));

val qrel_cons_IMP = Q.prove(
  `!q1 q2 qe. qrel (qe::q1) q2 ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel q1 (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l`,
  rpt gen_tac
  >> `qe::q1 = [] ++ [qe] ++ q1` by rw[]
  >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> rpt strip_tac
  >> dxrule qrel_cons_IMP_lemma >> rw[]);

val qrel_snoc_IMP = Q.prove(
  `!q1 q2 qe. qrel (SNOC qe q1) q2 ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel q1 (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r`,
  rpt gen_tac
  >> `SNOC qe q1 = q1 ++ [qe] ++ []` by rw[SNOC_APPEND]
  >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> rpt strip_tac
  >> dxrule qrel_snoc_IMP_lemma >> rw[]);

val qrel_consE = Q.store_thm("qrel_consE",
  `!q1 q2 qe. qrel (qe::q1) (qe::q2) ==> qrel q1 q2`,  
  `!qq1 qq2. qrel qq1 qq2 ==> (!q1 q2 qe. qq1 = (qe::q1) /\ qq2 = (qe::q2) ==> qrel q1 q2)`
    suffices_by metis_tac[qrel_refl]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >> fs[] >> rveq
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- (imp_res_tac qrel_LENGTH
      >> qpat_x_assum `qrel _ (_::_)` (assume_tac o MATCH_MP qrel_sym)
      >> imp_res_tac qrel_cons_IMP
      >> rveq >> fs[]
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> match_mp_tac qrel_sym
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >> rpt(pairarg_tac >> fs[])
      >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rw[qrel_refl])
  >- (Cases_on `q1` >> fs[] >> rveq
      >> match_mp_tac qrel_queue_reorder >> rw[]));

val qrel_snocE = Q.store_thm("qrel_snocE",
  `!q1 q2 qe. qrel (SNOC qe q1) (SNOC qe q2) ==> qrel q1 q2`,  
  `!qq1 qq2. qrel qq1 qq2 ==> (!q1 q2 qe. qq1 = (SNOC qe q1) /\ qq2 = (SNOC qe q2) ==> qrel q1 q2)`
    suffices_by metis_tac[qrel_refl]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >> fs[] >> rveq
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- (imp_res_tac qrel_LENGTH
      >> qpat_x_assum `qrel _ (_ ++ _)` (assume_tac o MATCH_MP qrel_sym)
      >> imp_res_tac (qrel_snoc_IMP |> REWRITE_RULE [SNOC_APPEND])
      >> rveq >> fs[]
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> match_mp_tac qrel_sym
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >> rpt(pairarg_tac >> fs[])
      >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rw[qrel_refl])
  >- (Q.ISPEC_THEN `q2` assume_tac SNOC_CASES >> fs[] >> rveq
      >> fs[] >> rveq
      >> match_mp_tac qrel_queue_reorder >> rw[]));

val qrel_append_r_E = Q.store_thm("qrel_append_r_E",
  `!q3 q1 q2. qrel (q1++q3) (q2++q3) ==> qrel q1 q2`,
  ho_match_mp_tac SNOC_INDUCT >> rpt strip_tac >> fs[APPEND_SNOC] >> metis_tac[qrel_snocE]);

val qrel_append_l_E = Q.store_thm("qrel_append_l_E",
  `!q1 q2 q3. qrel (q1++q2) (q1++q3) ==> qrel q2 q3`,
  Induct >> rpt strip_tac >> fs[] >> metis_tac[qrel_consE]);

val qcong_nil_rel_nil = Q.store_thm("qcong_nil_rel_nil",
  `!n2.
    qcong NNil n2
    ==> n2 = NNil`,
  `!n1 n2.
    qcong n1 n2
    ==> (n1 = NNil ==> n2 = NNil)
        /\ (n2 = NNil ==> n1 = NNil)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[]);

val qcong_endpoint_rel_endpoint = Q.store_thm("qcong_endpoint_rel_endpoint",
  `!p1 s1 e1 n2.
    qcong (NEndpoint p1 s1 e1) n2
    ==> ?s2. n2 = (NEndpoint p1 s2 e1)`,
  `!n1 n2.
    qcong n1 n2
    ==> (!p1 s1 e1. n1 = NEndpoint p1 s1 e1 ==> ?s2. n2 = NEndpoint p1 s2 e1)
        /\ (!p2 s2 e2. n2 = NEndpoint p2 s2 e2 ==> ?s1. n1 = NEndpoint p2 s1 e2)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[])

val qcong_par_rel_par = Q.store_thm("qcong_par_rel_par",
  `!n1 n2 n3.
    qcong (NPar n1 n2) n3
    ==> ?n4 n5. n3 = (NPar n4 n5) /\ qcong n1 n4 /\ qcong n2 n5`,
  `!n1 n2.
    qcong n1 n2
    ==> (!n3 n4. n1 = NPar n3 n4 ==> ?n5 n6. n2 = NPar n5 n6 /\ qcong n3 n5 /\ qcong n4 n6)
        /\ (!n3 n4. n2 = NPar n3 n4 ==> ?n5 n6. n1 = NPar n5 n6 /\ qcong n5 n3 /\ qcong n6 n4)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[qcong_refl,qcong_sym]
  >> rpt(first_x_assum drule >> strip_tac) >> metis_tac[qcong_rules]);

val qcong_par_rel_par_sym = Q.store_thm("qcong_par_rel_par_sym",
  `!n1 n2 n3.
    qcong n1 (NPar n2 n3)
    ==> ?n4 n5. n1 = (NPar n4 n5) /\ qcong n4 n2 /\ qcong n5 n3`,
  metis_tac[qcong_par_rel_par,qcong_sym]);

val qcong_IMP_qrel = Q.store_thm("qcong_IMP_qrel",
  `!p1 s1 e1 p2 s2 e2.
    qcong (NEndpoint p1 s1 e1) (NEndpoint p2 s2 e2)
    ==> qrel s1.queue s2.queue`,
  `!n1 n2.
    qcong n1 n2 ==>
    !p1 s1 e1 p2 s2 e2.
    n1 = NEndpoint p1 s1 e1 /\ n2 = NEndpoint p2 s2 e2
    ==> qrel s1.queue s2.queue` suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[] >> rveq >> simp[]
  >> metis_tac[qrel_rules,qcong_endpoint_rel_endpoint]);

val qcong_queue_reorder'' = Q.store_thm("qcong_queue_reorder''",
  `∀p e p1 d1 p2 d2 b q1 q2.
     p1 ≠ p2
     ⇒ qcong (NEndpoint p (<|bindings := b; queue:=q1 ++ [(p1,d1);(p2,d2)] ++ q2|>) e)
              (NEndpoint p (<|bindings := b; queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2|>) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `qcong (NEndpoint _ a1 _) (NEndpoint _ (<|bindings := _; queue := a2|>) _)`
  >> `<|bindings := b; queue := a2|> = a1 with queue := a2` by(unabbrev_all_tac >> fs[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac qcong_queue_reorder
  >> simp[]);

val qcong_endpoints = Q.store_thm("qcong_endpoints",
  `!n1 n2. qcong n1 n2 ==> MAP FST (endpoints n2) = MAP FST (endpoints n1)`,
  ho_match_mp_tac qcong_strongind >> rw[endpoints_def])

val trans_enqueue' = Q.store_thm("trans_enqueue'",
  `∀conf s d p1 p2 e q.
     p1 ≠ p2
     ⇒ trans conf (NEndpoint p2 (s with queue := q) e) (LReceive p1 d p2)
       (NEndpoint p2 (s with queue := SNOC (p1,d) q) e)`,
  rpt strip_tac
  >> `s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue
  >> simp[]);

val trans_dequeue_last_payload' = Q.store_thm("trans_dequeue_last_payload'",
  `∀conf s v p1 p2 e q1 q2 d ds.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ∧ final d ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,d)] ⧺ q2) (Receive p1 v ds e)) LTau
       (NEndpoint p2
          <|bindings := s.bindings |+ (v,FLAT (SNOC (unpad d) ds));
            queue := q1 ⧺ q2|> e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s.bindings = (s with queue := a1).bindings` by simp[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac (trans_dequeue_last_payload |> SIMP_RULE (srw_ss()) [])
  >> simp[]);

val trans_dequeue_intermediate_payload' = Q.store_thm("trans_dequeue_intermediate_payload'",
  `∀conf s v p1 p2 e q1 q2 d ds.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ∧ intermediate d ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,d)] ⧺ q2) (Receive p1 v ds e)) LTau
       (NEndpoint p2 (s with queue := q1 ⧺ q2)
          (Receive p1 v (SNOC (unpad d) ds) e))`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_dequeue_intermediate_payload)
  >> simp[]);

val trans_let' = Q.store_thm("trans_let'",
  `∀conf s v p f vl e q.
         EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl) ⇒
         trans conf (NEndpoint p (s with queue:= q) (Let v f vl e)) LTau
           (NEndpoint p
              (<|bindings := s.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s.bindings) vl));
                 queue:= q
                 |>) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `trans _ (NEndpoint _ s1 _) _ (NEndpoint _ s2 _)`
  >> `s2 = s1 with bindings := s1.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s1.bindings) vl))`
     by(unabbrev_all_tac >> simp[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])  
  >> unabbrev_all_tac
  >> match_mp_tac trans_let
  >> simp[]);

val qcong_sym_eq = Q.store_thm("qcong_sym_eq",
`∀p q. qcong p q = qcong q p`,metis_tac[qcong_sym]);

val trans_IMP_weak_trans = Q.store_thm("trans_IMP_weak_trans",
  `∀conf p alpha q. trans conf p alpha q ==> weak_trans conf p alpha q`,
  rw[weak_trans_def,weak_tau_trans_def]
  >> metis_tac[RTC_REFL,RTC_SINGLE,reduction_def]);

val qcong_trans_eq = Q.store_thm("qcong_trans_eq",
  `∀p1 q1 .
     qcong p1 q1
     ⇒ ∀ conf alpha p2 q2.
            ((trans conf p1 alpha p2 ⇒ (∃q2. trans conf q1 alpha q2 ∧ qcong p2 q2))
         ∧ (trans conf q1 alpha q2 ⇒ (∃p2. trans conf p1 alpha p2 ∧ qcong p2 q2)))`,
  ho_match_mp_tac qcong_strongind
  >> rpt strip_tac
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- (* qcong_queue_reorder *)
     (qpat_x_assum `trans _ _ _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS payloadSemanticsTheory.trans_rules)
                 >> fs[])
             >- metis_tac[qcong_rules])
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with queue := SNOC a3 _) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC a3 (q1 ++ [(p2,d2);(p1,d1)] ++ q2)) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac [trans_enqueue']
                 >> simp[])
             >- (simp[SNOC_APPEND] >> metis_tac[qcong_queue_reorder',APPEND_ASSOC]))
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with bindings := a3) a4)`
              >> qexists_tac `NEndpoint a1 ((a2 with queue := (q1 ++ [(p2,d2);(p1,d1)] ++ q2))
                                                with bindings := a3) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> `s.bindings = (s with queue := q1 ++ [(p2,d2); (p1,d1)] ++ q2).bindings`
                       by simp[]
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
                 >> match_mp_tac trans_let
                 >> simp[])
             >- (`(a2 with bindings := a3).queue = a2.queue` by fs[]
                 >> PURE_ONCE_REWRITE_TAC [GSYM endpointLangTheory.state_fupdcanon]
                 >> metis_tac [qcong_queue_reorder]))
      >> TRY(fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a5;a6] ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a6;a5] ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder''])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4;a5] ++ a6 ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a5;a4] ++ a6 ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'',APPEND_ASSOC])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a5;a6] ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a6;a5] ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4;a5] ++ a6 ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a5;a4] ++ a6 ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder',APPEND_ASSOC])))
  >- (* qcong_queue_reorder, symmetric case *)
     (qmatch_asmsub_abbrev_tac `NEndpoint _ s' _`
      >> `s'.queue = q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2` by(unabbrev_all_tac >> simp[])
      >> `s = s' with queue := q1 ⧺ [(p1,d1); (p2,d2)] ⧺ q2`
            by(unabbrev_all_tac >> simp[endpointLangTheory.state_component_equality])
      >> pop_assum (fn thm => fs[thm])
      >> qpat_x_assum `Abbrev _` kall_tac
      >> rename1 `s with queue := _ ++ [(p3,d3); (p4,d4)] ++ _`
      >> rename1 `_ with queue := _ ++ [(p2,d2); (p1,d1)] ++ _`
      >> PURE_ONCE_REWRITE_TAC [qcong_sym_eq]      
      >> qpat_x_assum `trans _ _ _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS payloadSemanticsTheory.trans_rules)
                 >> fs[])
             >- metis_tac[qcong_rules])
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with queue := SNOC a3 _) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC a3 (q1 ++ [(p2,d2);(p1,d1)] ++ q2)) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac [trans_enqueue']
                 >> simp[])
             >- (simp[SNOC_APPEND] >> metis_tac[qcong_queue_reorder',APPEND_ASSOC]))
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with bindings := a3) a4)`
              >> qexists_tac `NEndpoint a1 ((a2 with queue := (q1 ++ [(p2,d2);(p1,d1)] ++ q2))
                                                with bindings := a3) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> `s.bindings = (s with queue := q1 ++ [(p2,d2); (p1,d1)] ++ q2).bindings`
                       by simp[]
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
                 >> match_mp_tac trans_let
                 >> simp[])
             >- (`(a2 with bindings := a3).queue = a2.queue` by fs[]
                 >> PURE_ONCE_REWRITE_TAC [GSYM endpointLangTheory.state_fupdcanon]
                 >> metis_tac [qcong_queue_reorder]))
      >> TRY(fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a5;a6] ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a6;a5] ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder''])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4;a5] ++ a6 ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a5;a4] ++ a6 ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'',APPEND_ASSOC])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a5;a6] ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a6;a5] ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4;a5] ++ a6 ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a5;a4] ++ a6 ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder',APPEND_ASSOC])))
  >- (qpat_x_assum `trans _ (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[qcong_rules])
  >- (qpat_x_assum `trans _ (NPar _ _) _ _` (assume_tac
                                             o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[qcong_rules]));
  
val qcong_trans_pres = Q.store_thm("qcong_trans_pres",
  `∀p1 q1 conf alpha p2.
     qcong p1 q1 ∧ trans conf p1 alpha p2
     ⇒ ∃q2. trans conf q1 alpha q2 ∧ qcong p2 q2`,
  metis_tac[qcong_trans_eq])

val reduction_par_l = Q.store_thm("reduction_par_l",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar p r) (NPar q r)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_l]);

val reduction_par_r = Q.store_thm("reduction_par_r",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar r p) (NPar r q)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_r]);

val trans_nil_false = Q.store_thm("trans_nil_false",
  `∀conf alpha n. trans conf NNil alpha n = F`,
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[trans_cases]
  >> fs[]);

val reduction_nil = Q.store_thm("reduction_nil",
  `∀conf n. (reduction conf)^* NNil n ==> n = NNil`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = NNil`
  >> pop_assum (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> simp[]
  >> rpt(last_x_assum mp_tac)
  >> PURE_ONCE_REWRITE_TAC [AND_IMP_INTRO]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n`,`a1`]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[payloadSemanticsTheory.reduction_def,trans_nil_false]);

val reduction_par_l = Q.store_thm("reduction_par_l",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar p r) (NPar q r)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_l]);

val reduction_par_r = Q.store_thm("reduction_par_r",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar r p) (NPar r q)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_r]);

val trans_nil_false = Q.store_thm("trans_nil_false",
  `∀conf alpha n. trans conf NNil alpha n = F`,
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[trans_cases]
  >> fs[]);

val reduction_nil = Q.store_thm("reduction_nil",
  `∀conf n. (reduction conf)^* NNil n ==> n = NNil`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = NNil`
  >> pop_assum (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> simp[]
  >> rpt(last_x_assum mp_tac)
  >> PURE_ONCE_REWRITE_TAC [AND_IMP_INTRO]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n`,`a1`]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[payloadSemanticsTheory.reduction_def,trans_nil_false]);

val list_trans_def = Define `
    (list_trans conf p [] q = (p = q))
 /\ (list_trans conf p (alpha::l) q = ?p'. trans conf p alpha p' /\ list_trans conf p' l q)`

val list_trans_append = Q.store_thm("list_trans_append",
  `!l1 n1 l2 n2 conf. list_trans conf n1 (l1 ++ l2) n2 =
  ?n3. list_trans conf n1 l1 n3 /\ list_trans conf n3 l2 n2`,
  Induct_on `l1` >> rpt strip_tac >> fs[list_trans_def]
  >> rw[EQ_IMP_THM] >> fs[] >> metis_tac[]);

val list_trans_par_l = Q.store_thm("list_trans_par_l",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar p r) alpha (NPar q r)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemanticsTheory.trans_par_l]);

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemanticsTheory.trans_par_r]);

val endpoint_names_trans = Q.store_thm("endpoint_names_trans",
  `!conf n1 alpha n2. trans conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  ho_match_mp_tac trans_strongind >> rpt strip_tac >> fs[endpoints_def]);

val endpoint_names_list_trans = Q.store_thm("endpoint_names_list_trans",
  `!conf n1 alpha n2. list_trans conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  Induct_on `alpha` >> rw[list_trans_def] >>
  metis_tac[endpoint_names_trans]);

val sender_is_endpoint = Q.store_thm("sender_is_endpoint",
 `∀p1 p2 q1 d q2 conf.
  trans conf p1 (LSend q1 d q2) p2 ==> MEM q1 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val receiver_is_endpoint = Q.store_thm("receiver_is_endpoint",
 `∀p1 p2 q1 d q2 conf.
  trans conf p1 (LReceive q1 d q2) p2 ==> MEM q2 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val add_queue_def = Define `
  (add_queue p1 qe p2 payloadLang$NNil = NNil)
  ∧ (add_queue p1 qe p2 (NEndpoint p s e) =
      if p1 = p then NEndpoint p (s with queue := SNOC (p2,qe) s.queue) e
      else NEndpoint p s e
     )
  ∧ (add_queue p1 qe p2 (NPar n1 n2) = NPar (add_queue p1 qe p2 n1) (add_queue p1 qe p2 n2))
`

Theorem trans_same_sender_determ:
  trans conf p1 (LSend q2 d1 q1) p2
  /\ trans conf p1 (LSend q2 d2 q3) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q1 = q3 /\ d1 = d2 /\ p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`q2`,`d2`,`q1`,`d1`,`p3`,`q3`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint]
QED

Theorem trans_same_receiver_determ:
  trans conf p1 (LReceive s d r) p2
  /\ trans conf p1 (LReceive s d r) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`p3`,`s`,`d`,`r`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[receiver_is_endpoint]
QED

Theorem trans_no_selfloop:
  !conf p1 alpha p2.
  trans conf p1 alpha p2 /\ conf.payload_size > 0
  ==> p1 <> p2
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_ind >> rw[] >> fs[endpointLangTheory.state_component_equality] >>
  TRY(disj2_tac) >> spose_not_then strip_assume_tac >>
  qmatch_asmsub_abbrev_tac `a1 = a2` >>
  `endpoint_size a1 = endpoint_size a2` by simp[] >>
  pop_assum mp_tac >> unabbrev_all_tac >> rpt(pop_assum kall_tac) >>
  simp[endpoint_size_def]
QED

Theorem trans_different_sender:
  trans conf p1 (LSend s1 d1 r1) p2
  /\ trans conf p1 (LSend s2 d2 r2) p3
  /\ conf.payload_size > 0
  /\ s1 <> s2
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

(* TODO: remove? strictly weaker than trans_distinct_residual *)
Theorem trans_send_receive_distinct:
  trans conf p1 (LSend s1 d1 r1) p2
  /\ trans conf p1 (LReceive s2 d2 r2) p3
  /\ conf.payload_size > 0 (* not strictly needed *)
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> fs[endpointLangTheory.state_component_equality]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

Theorem trans_distinct_residual:
  !conf p1 alpha p2 beta p3.
  trans conf p1 alpha p2
  /\ trans conf p1 beta p3
  /\ alpha <> beta
  /\ conf.payload_size > 0
  ==> p2 <> p3
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_strongind >> rpt strip_tac >>
  fs[] >> rveq
  >- (* Send-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality])
  >- (* Send-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality])
  >- (* Enqueue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpointLangTheory.state_component_equality])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_no_selfloop])
QED

Theorem intermediate_final_IMP:
  !d. intermediate d /\ final d ==> F
Proof
  Cases >> rpt strip_tac >> fs[intermediate_def,final_def] >> rveq >> fs[]
QED

Theorem qcong_list_trans_pres:
  !conf p l q p'. list_trans conf p l q /\ qcong p p'
  ==> ?q'. list_trans conf p' l q' /\ qcong q q'
Proof
  Induct_on `l` >>
  rw[list_trans_def] >> simp[] >>
  dxrule_all_then strip_assume_tac qcong_trans_pres >>
  metis_tac[]
QED

val _ = export_theory ();

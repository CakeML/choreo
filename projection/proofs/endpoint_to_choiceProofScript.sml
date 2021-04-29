(* Semantics preservation and semantics reflection for the compilation step that
   implements internal/external choice using send/receive.

   For semantics reflection, the proof idea is as follows: the relation choice_rel
   relates endpointLang networks to compiled endpointLang networks, and also relates
   all intermediate states that the compiled network can reach to the closest
   preceding source network. In order to show (weak) semantics reflection it suffices to
   show:

   1) That choice_rel is closed under all reductions originating from a compiled network.
        (choice_rel_reduction_pres)
   2) That for any network on the RHS of choice_rel, there is a reduction sequence that
      takes us to the compilation of some reachable source network (up-to differences in
      unused local state).
        (choice_rel_exit)

   In order to obtain a tractable induction hypothesis for 2), we define the function
   closing_distance, which counts the number of reductions necessary to escape from
   choice_rel. We prove that for any networks related by choice_rel, there are reductions
   from the source and target that decrease the closing distance by one (closing_distance_SUC_IMP);
   unless the closing distance is zero, in which case we have already reached the compilation
   of a network (closing_distance_zero_IMP).

   The main proof for 2) is by induction on the closing distance. This proof structure greatly
   simplifies inductive arguments about semantics reflection, by allowing us to concentrate on
   only one reduction at a time.
 *)
open preamble choreoUtilsTheory endpointLangTheory endpointSemTheory
     endpointPropsTheory endpoint_to_choiceTheory

val _ = new_theory "endpoint_to_choiceProof";

val compile_network_preservation_send = Q.store_thm("compile_network_preservation_send",
  `∀p1 p2 q1 d q2 fv.
    trans p1 (LSend q1 d q2) p2
    ==> trans (compile_network_fv fv p1) (LSend q1 d q2) (compile_network_fv fv p2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def]
  >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[]);

val compile_network_preservation_receive = Q.store_thm("compile_network_preservation_receive",
  `∀p1 p2 q1 d q2 fv.
    trans p1 (LReceive q1 d q2) p2
    ==> trans (compile_network_fv fv p1) (LReceive q1 d q2) (compile_network_fv fv p2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def]
  >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[]);

val add_state_def = Define `
  (add_state p v d endpointLang$NNil = NNil)
  ∧ (add_state p v d (NEndpoint q s e) =
      if p = q then NEndpoint q (s with bindings := s.bindings |+ (v,d)) e
      else NEndpoint q s e
     )
  ∧ (add_state p v d (NPar n1 n2) = NPar (add_state p v d n1) (add_state p v d n2))
`

val junkcong_add_state_free_vars = Q.store_thm("junkcong_add_state_free_vars",
  `!n v fv p d. ~MEM v (free_var_names_network n) ∧
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  Induct
  >> rpt strip_tac
  >- rw[add_state_def,junkcong_refl]
  >- (fs[free_var_names_network_def]
      >> rpt (first_x_assum drule >> strip_tac)
      >> fs[add_state_def]
      >> match_mp_tac junkcong_par >> simp[])
  >- (rw[add_state_def,junkcong_refl]
      >> match_mp_tac junkcong_add_junk
      >> fs[free_var_names_network_def]));

val add_queue_def = Define `
  (add_queue p1 qe p2 endpointLang$NNil = NNil)
  ∧ (add_queue p1 qe p2 (NEndpoint p s e) =
      if p1 = p then NEndpoint p (s with queue := SNOC (p2,qe) s.queue) e
      else NEndpoint p s e
     )
  ∧ (add_queue p1 qe p2 (NPar n1 n2) = NPar (add_queue p1 qe p2 n1) (add_queue p1 qe p2 n2))
`

val junkcong_add_queue = Q.store_thm("junkcong_add_queue",
  `!fvs n1 n2 p1 qe p2. junkcong fvs n1 n2
                        ==> junkcong fvs (add_queue p1 qe p2 n1) (add_queue p1 qe p2 n2)`,
  simp[RIGHT_FORALL_IMP_THM]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac
  >- MATCH_ACCEPT_TAC junkcong_refl
  >- simp[junkcong_sym]
  >- metis_tac[junkcong_trans]
  >- (rw[add_queue_def]
      >> MAP_FIRST match_mp_tac [SIMP_RULE (srw_ss()) [] junkcong_add_junk''',
                                 junkcong_add_junk]
      >> rw[])
  >- rw[add_queue_def,junkcong_par]);

val junkcong_add_state_free_vars = Q.store_thm("junkcong_add_state_free_vars",
  `!n v fv p d. ~MEM v (free_var_names_network n) ∧
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  Induct
  >> rpt strip_tac
  >- rw[add_state_def,junkcong_refl]
  >- (fs[free_var_names_network_def]
      >> rpt (first_x_assum drule >> strip_tac)
      >> fs[add_state_def]
      >> match_mp_tac junkcong_par >> simp[])
  >- (rw[add_state_def,junkcong_refl]
      >> match_mp_tac junkcong_add_junk
      >> fs[free_var_names_network_def]));

val junkcong_add_state = Q.store_thm("junkcong_add_state",
  `!n v fv p d. ~MEM v (var_names_network n) ∧
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  metis_tac[junkcong_add_state_free_vars,free_names_are_names]);

val compile_network_endpoints = Q.store_thm("compile_network_endpoints",
  `!fv n. MAP FST (endpoints(compile_network_fv fv n)) = MAP FST (endpoints n)`,
  Induct_on `n` >> rw[endpoints_def,compile_network_fv_def]);

val compile_network_endpoints = Q.store_thm("compile_network_endpoints",
  `!fv n. MAP FST (endpoints(compile_network_fv fv n)) = MAP FST (endpoints n)`,
  Induct_on `n` >> rw[endpoints_def,compile_network_fv_def]);

val not_MEM_add_state = Q.store_thm("not_MEM_add_state",
  `!n q fv d. ¬MEM q (MAP FST (endpoints n)) ==> add_state q fv d n = n`,
  Induct >> rw[endpoints_def,add_state_def]);

val compile_network_preservation_int_choice_T = Q.store_thm(
  "compile_network_preservation_int_choice_T",
  `∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    trans n1 (LIntChoice q1 T q2) n2
    ==> list_trans (compile_network_fv fv n1)
                   [LTau;LSend q1 [1w] q2]
                   (add_state q1 fv [1w] (compile_network_fv fv n2))
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (qmatch_goalsub_abbrev_tac `Let _ _ _ a1`
      >> qexists_tac `NEndpoint p1
                        (s with bindings := s.bindings
                                              |+ (fv,
                                                  (K1)(MAP (THE o FLOOKUP s.bindings) [])))
                        a1`
      >> conj_tac
      >- (match_mp_tac trans_let >> simp[])
      >> simp[]
      >> unabbrev_all_tac
      >> simp[K1_def]
      >> PURE_ONCE_REWRITE_TAC [DROP_0 |> GEN_ALL |> ISPEC ``[1w:8 word]`` |> GSYM]
      >> match_mp_tac trans_send >> fs[FLOOKUP_UPDATE])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum drule >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_l])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum(qspec_then `q1` (drule o PURE_REWRITE_RULE[NOT_CLAUSES] o CONTRAPOS))
      >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_r]));

val compile_network_preservation_int_choice_F = Q.store_thm(
  "compile_network_preservation_int_choice_F",
  `∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    trans n1 (LIntChoice q1 F q2) n2
    ==> list_trans (compile_network_fv fv n1)
                   [LTau;LSend q1 [0w] q2]
                   (add_state q1 fv [0w] (compile_network_fv fv n2))
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (qmatch_goalsub_abbrev_tac `Let _ _ _ a1`
      >> qexists_tac `NEndpoint p1
                        (s with bindings := s.bindings
                                              |+ (fv,
                                                  (K0)(MAP (THE o FLOOKUP s.bindings) [])))
                        a1`
      >> conj_tac
      >- (match_mp_tac trans_let >> simp[])
      >> simp[]
      >> unabbrev_all_tac
      >> simp[K0_def]
      >> PURE_ONCE_REWRITE_TAC [DROP_0 |> GEN_ALL |> ISPEC ``[0w:8 word]`` |> GSYM]
      >> match_mp_tac trans_send >> fs[FLOOKUP_UPDATE])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum drule >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_l])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum(qspec_then `q1` (drule o PURE_REWRITE_RULE[NOT_CLAUSES] o CONTRAPOS))
      >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_r]));

val compile_network_preservation_ext_choice_T = Q.store_thm("compile_network_preservation_ext_choice_T",
  `∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    trans n1 (LExtChoice q1 T q2) n2
    ==> trans (compile_network_fv fv n1)
                   (LReceive q1 [1w] q2)
                   (compile_network_fv fv n2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (match_mp_tac trans_enqueue >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_l >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_r >> first_x_assum ACCEPT_TAC));

val compile_network_preservation_ext_choice_F = Q.store_thm("compile_network_preservation_ext_choice_T",
  `∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    trans n1 (LExtChoice q1 F q2) n2
    ==> trans (compile_network_fv fv n1)
                   (LReceive q1 [0w] q2)
                   (compile_network_fv fv n2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (match_mp_tac trans_enqueue >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_l >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_r >> first_x_assum ACCEPT_TAC));

val MEM_free_vars_compile_endpoint = Q.store_thm("MEM_free_vars_compile_endpoint",
  `!p fv. ~MEM fv (var_names_endpoint p) ==>
          MEM fv (free_var_names_endpoint (compile_endpoint fv p)) = MEM fv (free_var_names_endpoint p)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_endpoint_def,compile_endpoint_def,MEM_FILTER]
  >> fs[var_names_endpoint_def] >> metis_tac[free_names_are_names_endpoint]);

val MEM_free_vars_compile_network = Q.store_thm("MEM_free_vars_compile_network",
  `!n fv. ~MEM fv (var_names_network n) ==>
          MEM fv (free_var_names_network (compile_network_fv fv n)) = MEM fv (free_var_names_network n)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_network_def,compile_network_fv_def,MEM_FILTER]
  >> fs[var_names_network_def,MEM_free_vars_compile_endpoint]);

val MEM_free_vars_compile_endpoint' = Q.store_thm("MEM_free_vars_compile_endpoint'",
  `!p fv. ~MEM fv (var_names_endpoint p) ==>
          MEM fv (free_var_names_endpoint (compile_endpoint fv' p)) = MEM fv (free_var_names_endpoint p)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_endpoint_def,endpoint_to_choiceTheory.compile_endpoint_def,MEM_FILTER]
  >> fs[var_names_endpoint_def] >> metis_tac[free_names_are_names_endpoint]);

val MEM_free_vars_compile_network' = Q.store_thm("MEM_free_vars_compile_network'",
  `!n fv fv'. ~MEM fv (var_names_network n) ==>
          MEM fv (free_var_names_network (compile_network_fv fv' n)) = MEM fv (free_var_names_network n)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_network_def,compile_network_fv_def,MEM_FILTER]
  >> fs[var_names_network_def,MEM_free_vars_compile_endpoint']);

val compile_endpoint_support = Q.store_thm("compile_endpoint_support",
  `!e fv. MEM fv (free_var_names_endpoint (compile_endpoint fv e))
   ==> MEM fv (free_var_names_endpoint e)
  `,
  Induct >> rpt strip_tac
  >> fs[compile_endpoint_def,free_var_names_endpoint_def,MEM_FILTER]
  >> every_case_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]);

val compile_network_support = Q.store_thm("compile_network_support",
  `!n fv. MEM fv (free_var_names_network (compile_network_fv fv n))
   ==> MEM fv (free_var_names_network n)
  `,
  Induct >> rpt strip_tac
  >> fs[compile_network_fv_def,free_var_names_network_def,
        compile_endpoint_support]);

Theorem compile_network_fv_dsubst:
  compile_endpoint fv (dsubst e dn e') =
  dsubst (compile_endpoint fv e) dn (compile_endpoint fv e')
Proof
  Induct_on ‘e’ >>
  rw[compile_endpoint_def,dsubst_def]
QED

Theorem compile_network_preservation_trans:
  ∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    ¬MEM fv (var_names_network n1) ∧
    trans n1 LTau n2
    ==> ?n3. reduction^+ (compile_network_fv fv n1) n3 ∧
             junkcong {fv} (compile_network_fv fv n2) n3
Proof
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> qpat_x_assum `¬MEM _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* com-l *)
     (imp_res_tac compile_network_preservation_send
      >> imp_res_tac compile_network_preservation_receive
      >> rpt(first_x_assum(qspec_then `fv` assume_tac))
      >> imp_res_tac trans_com_l
      >> fs[GSYM reduction_def,compile_network_fv_def]
      >> metis_tac[cj 1 TC_RULES,junkcong_refl])
  >- (* com-r *)
     (imp_res_tac compile_network_preservation_send
      >> imp_res_tac compile_network_preservation_receive
      >> rpt(first_x_assum(qspec_then `fv` assume_tac))
      >> imp_res_tac trans_com_r
      >> fs[GSYM reduction_def,compile_network_fv_def]
      >> metis_tac[cj 1 TC_RULES,junkcong_refl])
  >- (* com-choice-l *)
     (Cases_on `b`
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def,K0_def,K1_def]
          >> imp_res_tac compile_network_preservation_int_choice_T
          >> imp_res_tac compile_network_preservation_ext_choice_T
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_l
          >> qpat_x_assum `trans (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_l >> disch_then(qspec_then `compile_network_fv fv n1'` assume_tac)
          >> fs[GSYM reduction_def]
          >> irule_at (Pos hd) (cj 2 TC_RULES)
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> simp[]
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
          >- MATCH_ACCEPT_TAC junkcong_refl)
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def,K0_def,K1_def]
          >> imp_res_tac compile_network_preservation_int_choice_F
          >> imp_res_tac compile_network_preservation_ext_choice_F
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_l
          >> qpat_x_assum `trans (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_l >> disch_then(qspec_then `compile_network_fv fv n1'` assume_tac)
          >> fs[GSYM reduction_def]
          >> irule_at (Pos hd) (cj 2 TC_RULES)
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
          >- MATCH_ACCEPT_TAC junkcong_refl))
  >- (* com-choice-l *)
     (Cases_on `d` (* TODO: why not b? *)
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def,K0_def,K1_def]
          >> imp_res_tac compile_network_preservation_int_choice_T
          >> imp_res_tac compile_network_preservation_ext_choice_T
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_r
          >> qpat_x_assum `trans (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_r >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
          >> fs[GSYM reduction_def]
          >> irule_at (Pos hd) (cj 2 TC_RULES)
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- MATCH_ACCEPT_TAC junkcong_refl
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def,K0_def,K1_def]
          >> imp_res_tac compile_network_preservation_int_choice_F
          >> imp_res_tac compile_network_preservation_ext_choice_F
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_r
          >> qpat_x_assum `trans (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_r >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
          >> fs[GSYM reduction_def]
          >> irule_at (Pos hd) (cj 2 TC_RULES)
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> irule_at (Pos hd) (cj 1 TC_RULES)
          >> goal_assum drule
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- MATCH_ACCEPT_TAC junkcong_refl
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
         )
     )
  >- (* dequeue *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac (cj 1 TC_RULES) >> imp_res_tac trans_dequeue
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* extchoice-l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint a1 a2 a3) _`
      >> qexists_tac `NEndpoint a1 (a2 with bindings:= s.bindings |+ (fv,[1w])) a3` >> unabbrev_all_tac
      >> conj_tac
      >- (Q.ISPEC_THEN `reduction` (match_mp_tac o CONJUNCT2) TC_RULES
          >> imp_res_tac trans_dequeue
          >> pop_assum(qspec_then `fv` assume_tac)
          >> qmatch_goalsub_abbrev_tac `Receive _ _ a1`
          >> qmatch_goalsub_abbrev_tac `NEndpoint _ a2 (compile_endpoint _ _)`
          >> qexists_tac `NEndpoint p2 a2 a1` >> unabbrev_all_tac
          >> conj_tac >- (match_mp_tac (cj 1 TC_RULES) >> fs[reduction_def])
          >> match_mp_tac (cj 1 TC_RULES)
          >> fs[reduction_def] >> match_mp_tac trans_if_true
          >> fs[FLOOKUP_UPDATE])
      >- (match_mp_tac junkcong_add_junk'''
          >> fs[free_var_names_endpoint_def,var_names_network_def,var_names_endpoint_def]
          >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))
  >- (* extchoice-r *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint a1 a2 a3) _`
      >> qexists_tac `NEndpoint a1 (a2 with bindings:= s.bindings |+ (fv,d)) a3` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac (cj 2 TC_RULES) >>
          irule_at (Pos hd) (cj 1 TC_RULES) >>
          simp[reduction_def] >>
          irule_at (Pos hd) trans_dequeue >>
          rpt(goal_assum drule) >>
          match_mp_tac (cj 1 TC_RULES) >>
          fs[reduction_def] >> match_mp_tac trans_if_false
          >> fs[FLOOKUP_UPDATE])
      >- (match_mp_tac junkcong_add_junk'''
          >> fs[free_var_names_endpoint_def,var_names_network_def,var_names_endpoint_def]
          >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))
  >- (* trans_if_true *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac (cj 1 TC_RULES) >> imp_res_tac trans_if_true
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_if_false *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac (cj 1 TC_RULES) >> imp_res_tac trans_if_false
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_let *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac (cj 1 TC_RULES) >> imp_res_tac trans_let
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_par_l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def,var_names_network_def]
      >> first_x_assum drule
      >> (impl_tac >> fs[ALL_DISTINCT_APPEND,endpoints_def])
      >> strip_tac
      >> drule reduction_par_l_TC >> disch_then(qspec_then `compile_network_fv fv n2'` assume_tac)
      >> asm_exists_tac >> simp[] >> match_mp_tac junkcong_par
      >> fs[junkcong_refl])
  >- (* trans_par_l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def,var_names_network_def]
      >> first_x_assum drule
      >> (impl_tac >> fs[ALL_DISTINCT_APPEND,endpoints_def])
      >> strip_tac
      >> drule reduction_par_r_TC >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
      >> asm_exists_tac >> simp[] >> match_mp_tac junkcong_par
      >> fs[junkcong_refl])
  >- (* trans_fix *)
     (fs[compile_network_fv_def,compile_network_fv_dsubst,compile_endpoint_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> simp[junkcong_refl]
      >> match_mp_tac (cj 1 TC_RULES)
      >> metis_tac[reduction_def,trans_fix])
QED

Theorem compile_network_preservation:
  ∀n1 n2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    ¬MEM fv (var_names_network n1) ∧
    reduction^* n1 n2
    ==> ?n3. reduction^* (compile_network_fv fv n1) n3 ∧
             junkcong {fv} (compile_network_fv fv n2) n3
Proof
    `∀n1 n2.
        reduction^* n1 n2
        ==> ∀fv.
             ALL_DISTINCT (MAP FST (endpoints n1)) ∧
             ¬MEM fv (var_names_network n1)
             ==> ?n3. reduction^* (compile_network_fv fv n1) n3 ∧
                      junkcong {fv} (compile_network_fv fv n2) n3`
    suffices_by metis_tac []
    \\ ho_match_mp_tac RTC_ind
    \\ rw [reduction_def]
    >- (qexists_tac ‘compile_network_fv fv n1’ \\ fs [junkcong_rules])
    \\ drule compile_network_preservation_trans
    \\ rpt (disch_then drule) \\ strip_tac \\ fs []
    \\ ‘~MEM fv (var_names_network n1')’
       by (CCONTR_TAC \\ fs []
           \\ drule_then drule trans_var_names_mono \\ fs [])
    \\ drule_then (assume_tac o GSYM) endpoint_names_trans \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ dxrule_then strip_assume_tac TC_RTC
    \\ qmatch_asmsub_abbrev_tac ‘reduction^* cn1  n3’
    \\ qmatch_asmsub_abbrev_tac ‘reduction^* cn1' n3'’
    \\ qspecl_then [‘{fv}’,‘cn1'’,‘n3’] assume_tac junkcong_reduction_eq
    \\ rfs [] \\ first_x_assum (qspecl_then [‘n3'’,‘q2’] assume_tac) \\ fs []
    \\ rfs [] \\ qexists_tac ‘q2'’
    \\ conj_tac
    >- (irule RTC_SPLIT \\ asm_exists_tac \\ fs [])
    \\ irule junkcong_trans \\ asm_exists_tac \\ fs []
QED

Theorem compile_network_preservation_TC:
  ∀n1 n2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    ¬MEM fv (var_names_network n1) ∧
    reduction^+ n1 n2
    ==> ?n3. reduction^+ (compile_network_fv fv n1) n3 ∧
             junkcong {fv} (compile_network_fv fv n2) n3
Proof
    `∀n1 n2.
        reduction^+ n1 n2
        ==> ∀fv.
             ALL_DISTINCT (MAP FST (endpoints n1)) ∧
             ¬MEM fv (var_names_network n1)
             ==> ?n3. reduction^+ (compile_network_fv fv n1) n3 ∧
                      junkcong {fv} (compile_network_fv fv n2) n3`
      suffices_by metis_tac []
    \\ ho_match_mp_tac TC_INDUCT_LEFT1
    \\ rw [reduction_def]
    >- (metis_tac[compile_network_preservation_trans])
    \\ drule_all compile_network_preservation_trans
    \\ rw[]
    \\ ‘~MEM fv (var_names_network n1')’
       by (CCONTR_TAC \\ fs []
           \\ drule_then drule trans_var_names_mono \\ fs [])
    \\ drule_then (assume_tac o GSYM) endpoint_names_trans \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ irule_at (Pos hd) (cj 2 TC_RULES)
    \\ goal_assum drule
    \\ qmatch_asmsub_abbrev_tac ‘reduction^+ cn1  n3’
    \\ qmatch_asmsub_abbrev_tac ‘reduction^+ cn1' n3'’
    \\ qspecl_then [‘{fv}’,‘cn1'’,‘n3’] assume_tac junkcong_reduction_eq_TC
    \\ first_x_assum drule
    \\ rw[FORALL_AND_THM]
    \\ first_x_assum drule
    \\ strip_tac
    \\ goal_assum drule
    \\ metis_tac[junkcong_rules]
QED

val (choice_rel_rules,choice_rel_ind,choice_rel_cases) = Hol_reln `
  (* choice_rel_eq_junk *)
  (∀fv n1 n2.
     ¬MEM fv (var_names_network n1)
     ∧ junkcong {fv} (compile_network_fv fv n1) n2
     ==> choice_rel fv n1 n2)
  (* choice_rel_par *)
∧ (∀fv n1 n2 n3 n4.
     choice_rel fv n1 n2
     ∧ choice_rel fv n3 n4
     ==> choice_rel fv (NPar n1 n3) (NPar n2 n4))
  (* choice_rel_int_choice_true *)
∧ (∀fv e p1 s p2.
     ¬MEM fv (var_names_endpoint e) ∧ p1 ≠ p2
     ==> choice_rel fv
                    (NEndpoint p1 s (IntChoice T p2 e))
                    (NEndpoint p1 (s with bindings := s.bindings |+ (fv,[1w]))
                                  (Send p2 fv (compile_endpoint fv e))))
  (* choice_rel_int_choice_false *)
∧ (∀fv e p1 s p2.
     ¬MEM fv (var_names_endpoint e) ∧ p1 ≠ p2
     ==> choice_rel fv
                    (NEndpoint p1 s (IntChoice F p2 e))
                    (NEndpoint p1 (s with bindings := s.bindings |+ (fv,[0w]))
                                  (Send p2 fv (compile_endpoint fv e))))
  (* choice_rel_ext_choice *)
∧ (∀fv e1 e2 p1 s p2 q1 q2 d.
     ¬MEM fv (var_names_endpoint e1) ∧ ¬MEM fv (var_names_endpoint e2)
     ∧ s.queue = q1 ++ [(p1,d)] ++ q2
     ∧ EVERY (λ(p,_). p ≠ p1) q1 ∧ p1 ≠ p2
     ==> choice_rel fv
                    (NEndpoint p2 s (ExtChoice p1 e1 e2))
                    (NEndpoint p2 (s with <|bindings := s.bindings |+ (fv,d);
                                            queue := q1 ++ q2|>)
                                  (IfThen fv (compile_endpoint fv e1) (compile_endpoint fv e2))))
  `;

val [choice_rel_eq_junk,
     choice_rel_par,
     choice_rel_int_choice_true,
     choice_rel_int_choice_false,
     choice_rel_ext_choice] =
    zip ["choice_rel_eq_junk", "choice_rel_par",
         "choice_rel_int_choice_true","choice_rel_int_choice_false",
         "choice_rel_ext_choice"]
        (CONJUNCTS choice_rel_rules) |> map save_thm;

val choice_rel_endpoint_eq_junk = Q.store_thm("choice_rel_endpoint_eq_junk",
  `!fv e l s n. ¬MEM fv (var_names_endpoint e) ∧
     junkcong {fv} (NEndpoint l s (compile_endpoint fv e)) n ⇒
     choice_rel fv (NEndpoint l s e) n`,
  rpt strip_tac
  >> match_mp_tac choice_rel_eq_junk
  >> rw[var_names_network_def,compile_network_fv_def]);

val choice_rel_endpoint_eq_junk_send = Q.store_thm("choice_rel_endpoint_eq_junk_send",
  `!fv e l s n a b. ¬MEM fv (var_names_endpoint e) ∧ fv ≠ b ∧
     junkcong {fv} (NEndpoint l s (Send a b (compile_endpoint fv e))) n ⇒
     choice_rel fv (NEndpoint l s (Send a b e)) n`,
  rpt strip_tac
  >> match_mp_tac choice_rel_endpoint_eq_junk
  >> rw[var_names_endpoint_def,compile_endpoint_def]);

val choice_rel_endpoint_eq_junk_receive = Q.store_thm("choice_rel_endpoint_eq_junk_receive",
  `!fv e l s n a b d. ¬MEM fv (var_names_endpoint e) ∧ fv ≠ b ∧
     junkcong {fv} (NEndpoint l s (Receive a b (compile_endpoint fv e))) n ⇒
     choice_rel fv (NEndpoint l s (Receive a b e)) n`,
  rpt strip_tac
  >> match_mp_tac choice_rel_endpoint_eq_junk
  >> rw[var_names_endpoint_def,compile_endpoint_def]);

val bool2w_def = Define `bool2w T = 1w /\ bool2w F = 0w`

val closing_distance_def = Define `
  (closing_distance fv (NPar n1 n2) (NPar n3 n4)
   = closing_distance fv n1 n3 + closing_distance fv n2 n4) ∧
  (closing_distance fv NNil NNil = (0:num)) ∧
  (closing_distance fv (NEndpoint p1 s1 e1) (NEndpoint p2 s2 e2) =
   if junkcong {fv} (NEndpoint p1 s1 (compile_endpoint fv e1)) (NEndpoint p2 s2 e2) then
     0
   else if ?b p e. e1 = IntChoice b p e /\ e2 = Send p fv (compile_endpoint fv e)
                   ∧ s2 = s1 with bindings := s1.bindings |+ (fv,[bool2w b]) then
     1
   else if ?p e3 e4 q1 d q2. e1 = ExtChoice p e3 e4 ∧ e2 = IfThen fv (compile_endpoint fv e3)
                                                                (compile_endpoint fv e4)
                   ∧ s1.queue = q1 ++ [(p,d)] ++ q2
                   ∧ EVERY (λ(p',_). p' ≠ p) q1
                   ∧ s2 = s1 with <|bindings := s1.bindings |+ (fv,d); queue := q1 ++ q2|>
                   then
     1 else 0) ∧ closing_distance _ _ _ = 0`

val closing_distance_zero_IMP = Q.store_thm("closing_distance_zero_IMP",
  `!fv n1 n2. choice_rel fv n1 n2 /\ closing_distance fv n1 n2 = 0
   ==> junkcong {fv} (compile_network_fv fv n1) n2`,
  PURE_ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac choice_rel_ind
  >> rpt strip_tac
  >- (* choice_rel_eq_junk *)
     first_x_assum ACCEPT_TAC
  >- (* choice_rel_eq_par *)
     fs[closing_distance_def,ADD_EQ_0,compile_network_fv_def,junkcong_par]
  >- (* choice_rel_int_choice_true *)
    (fs[closing_distance_def,compile_network_fv_def]
     >> rpt(pop_assum mp_tac) >> IF_CASES_TAC >> rpt strip_tac
     >> fs[bool2w_def])
  >- (* choice_rel_int_choice_false *)
    (fs[closing_distance_def,compile_network_fv_def]
     >> rpt(pop_assum mp_tac) >> IF_CASES_TAC >> rpt strip_tac
     >> fs[bool2w_def])
  >- (* choice_rel_ext_choice *)
   (fs[closing_distance_def,compile_network_fv_def]
    >> every_case_tac >> fs[] >> rfs[]
    >> rpt(first_x_assum (qspecl_then [`q1`,`d`,`q2`] assume_tac))
    >> fs[EXISTS_MEM,EVERY_MEM] >> first_x_assum drule >> strip_tac));

val closing_distance_compile_network = Q.store_thm("closing_distance_compile_network",
  `!fv n3. closing_distance fv n3 (compile_network_fv fv n3) = 0`,
  Induct_on `n3` >> rpt strip_tac
  >> fs[compile_network_fv_def,closing_distance_def,junkcong_refl])

val junkcong_closing_distance_eq = Q.store_thm("junkcong_closing_distance_eq",
  `!fv n1 n2 n3. junkcong {fv} n1 n2
    ==> closing_distance fv n3 n1 = closing_distance fv n3 n2`,
  `!fvs n1 n2. junkcong fvs n1 n2
               ==> !n3 fv. fvs = {fv} ==> closing_distance fv n3 n1 = closing_distance fv n3 n2`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[closing_distance_def]
  >> Cases_on `n3` >> fs[closing_distance_def]
  >> qmatch_goalsub_abbrev_tac `(if a1 then _ else _) = (if a2 then _ else _)`
  >> `a1 = a2`
  by(unabbrev_all_tac >> rw[EQ_IMP_THM] >> imp_res_tac junkcong_endpoint_rel_endpoint
     >> fs[] >> rveq >> match_mp_tac junkcong_trans >> asm_exists_tac >> simp[]
     >> FIRST [match_mp_tac junkcong_add_junk >> fs[],
               match_mp_tac junkcong_sym >> match_mp_tac junkcong_add_junk >> fs[]])
  >> IF_CASES_TAC >> fs[]
  >> rpt(qpat_x_assum `Abbrev _` kall_tac)
  >> qmatch_goalsub_abbrev_tac `(if a3 then _ else _) = (if a4 then _ else _)`
  >> `a3 = a4`
  by(unabbrev_all_tac >> rw[EQ_IMP_THM] >> fs[free_var_names_endpoint_def])
  >> IF_CASES_TAC >> fs[]
  >> rpt(qpat_x_assum `Abbrev _` kall_tac)
  >> qmatch_goalsub_abbrev_tac `(if a5 then _ else _) = (if a6 then _ else _)`
  >> `a5 = a6`
  by(unabbrev_all_tac >> rw[EQ_IMP_THM] >> fs[free_var_names_endpoint_def])
  >> IF_CASES_TAC >> fs[]
  >> rpt(qpat_x_assum `Abbrev _` kall_tac)
  >> qmatch_goalsub_abbrev_tac `(if a7 then _ else _) = (if a8 then _ else _)`
  >> `a7 = a8`
  by(unabbrev_all_tac >> rw[EQ_IMP_THM] >> fs[free_var_names_endpoint_def])
  >> fs[]);

val sends_fv_def = Define `
  sends_fv fv e = (?p e'. e = Send p fv e')`

val endpoint_sends_fv_def = Define `
  endpoint_sends_fv p fv n =
  (?e. (OPTION_MAP (SND o SND) (FIND ($= p o FST) (endpoints n)) = SOME e)
         ∧ sends_fv fv e)`

val decompile_label_def = Define `
  (decompile_label fv n (LSend p1 l p2) =
    if (l = [1w]) ∧ endpoint_sends_fv p1 fv n then
      LIntChoice p1 T p2
    else if (l = [0w]) ∧ endpoint_sends_fv p1 fv n then
      LIntChoice p1 F p2
    else LSend p1 l p2)
  ∧ decompile_label fv n alpha = alpha`

val choice_rel_endpoints = Q.store_thm("choice_rel_endpoints",
  `!fv n1 n2. choice_rel fv n1 n2 ==> MAP FST (endpoints n1) = MAP FST (endpoints n2)`,
  ho_match_mp_tac choice_rel_ind
  >> rpt strip_tac >> imp_res_tac junkcong_endpoints >> fs[endpoints_def,compile_network_endpoints]);

val sends_fv_compile_endpoint = Q.prove(
  `¬MEM fv (var_names_endpoint e) ==> (sends_fv fv (compile_endpoint fv e) = F)`,
  Induct_on `e` >> fs[var_names_endpoint_def,sends_fv_def,compile_endpoint_def]
  >> rw[]);

val choice_rel_int_choice_true' = Q.store_thm("choice_rel_int_choice_true'",
`!fv net p1 s q p2 e. ¬MEM fv (var_names_endpoint e) ∧ p1 ≠ p2 ==>
choice_rel fv
  (NEndpoint p1 (s with queue := q) (IntChoice T p2 e))
  (NEndpoint p1
     <|bindings := s.bindings |+ (fv,[1w]);
       queue := q|>
     (Send p2 fv (compile_endpoint fv e)))`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `<|bindings := a1; queue := _|>`
  >> qmatch_goalsub_abbrev_tac `choice_rel _ (NEndpoint _ a2 _)`
  >> `<|bindings := a1; queue := q|> = a2 with bindings := a1` by(unabbrev_all_tac >> simp[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[Once thm])
  >> qunabbrev_tac `a1`
  >> `s.bindings = a2.bindings` by(unabbrev_all_tac >> simp[])
  >> simp[] >> match_mp_tac choice_rel_int_choice_true >> simp[]);

val choice_rel_int_choice_false' = Q.store_thm("choice_rel_int_choice_false'",
`!fv p1 s q p2 e. ¬MEM fv (var_names_endpoint e) ∧ p1 ≠ p2 ==>
choice_rel fv
  (NEndpoint p1 (s with queue := q) (IntChoice F p2 e))
  (NEndpoint p1
     <|bindings := s.bindings |+ (fv,[0w]);
       queue := q|>
     (Send p2 fv (compile_endpoint fv e)))`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `<|bindings := a1; queue := _|>`
  >> qmatch_goalsub_abbrev_tac `choice_rel _ (NEndpoint _ a2 _)`
  >> `<|bindings := a1; queue := q|> = a2 with bindings := a1` by(unabbrev_all_tac >> simp[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[Once thm])
  >> qunabbrev_tac `a1`
  >> `s.bindings = a2.bindings` by(unabbrev_all_tac >> simp[])
  >> simp[] >> match_mp_tac choice_rel_int_choice_false >> simp[]);

val choice_rel_ext_choice_SNOC = Q.store_thm("choice_rel_ext_choice_SNOC",
  `∀fv e1 e2 p1 s p2 q1 qe q2 d.
     ¬MEM fv (var_names_endpoint e1) ∧ ¬MEM fv (var_names_endpoint e2) ∧
     EVERY (λ(p,_). p ≠ p1) q1 ∧
     p1 ≠ p2 ⇒
     choice_rel fv (NEndpoint p2 (s with queue := SNOC qe (q1 ⧺ [(p1,d)] ⧺ q2))
                              (ExtChoice p1 e1 e2))
       (NEndpoint p2
          (<|bindings := s.bindings |+ (fv,d); queue := SNOC qe (q1 ++ q2) |>)
          (IfThen fv (compile_endpoint fv e1) (compile_endpoint fv e2)))`,
  rpt strip_tac >> simp[SNOC_APPEND]
  >> `q1 ++ [(p1,d)] ++ q2 ++ [qe] = q1 ++ [(p1,d)] ++ (q2 ++ [qe])`
     by simp[]
  >> `q1 ++ q2 ++ [qe] = q1 ++ (q2 ++ [qe])`
     by simp[]
  >> `s.bindings = (s with queue := q1 ⧺ [(p1,d)] ⧺ (q2 ⧺ [qe])).bindings`
     by simp[]
  >> ntac 3 (pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm]))
  >> match_mp_tac (choice_rel_ext_choice |> SIMP_RULE (srw_ss()) [])
  >> rw[]);

val send_or_tau_def = Define `
  send_or_tau LTau = T
  /\ send_or_tau (LSend _ _ _) = T
  /\ send_or_tau _ = F`

val compile_network_add_queue = Q.store_thm("compile_network_add_queue",
  `!n1 p1 qe p2 fv.
     add_queue p1 qe p2(compile_network_fv fv n1)
     = compile_network_fv fv (add_queue p1 qe p2 n1)`,
  Induct >> rw[add_queue_def,compile_network_fv_def]);

val var_names_add_queue = Q.store_thm("var_names_add_queue",
  `!n1 p1 qe p2 fv.
     var_names_network(add_queue p1 qe p2 n1)
     = var_names_network n1`,
  Induct >> rw[add_queue_def,var_names_network_def]);

val choice_rel_add_queue = Q.store_thm("choice_rel_add_queue",
  `!fv n1 n2 p1 qe p2. choice_rel fv n1 n2
                        ==> choice_rel fv (add_queue p1 qe p2 n1) (add_queue p1 qe p2 n2)`,
  simp[RIGHT_FORALL_IMP_THM]
  >> ho_match_mp_tac (fetch "-" "choice_rel_strongind")
  >> rpt strip_tac
  >- (imp_res_tac junkcong_add_queue
      >> match_mp_tac choice_rel_eq_junk
      >> fs[compile_network_add_queue,var_names_add_queue])
  >- rw[add_queue_def,choice_rel_par]
  >- (rw[add_queue_def]
      >> MAP_FIRST match_mp_tac [SIMP_RULE (srw_ss()) [] choice_rel_int_choice_true',
                                 choice_rel_int_choice_true]
      >> rw[])
  >- (rw[add_queue_def]
      >> MAP_FIRST match_mp_tac [SIMP_RULE (srw_ss()) [] choice_rel_int_choice_false',
                                 choice_rel_int_choice_false]
      >> rw[])
  >- (rw[add_queue_def]
      >> MAP_FIRST (match_mp_tac o SIMP_RULE (srw_ss()) [])
                    [choice_rel_ext_choice_SNOC,
                     choice_rel_ext_choice]
  >> rw[]));

val add_queue_fresh = Q.store_thm("add_queue_fresh",
  `!p1 qe p2 n.
     ¬MEM p1 (MAP FST (endpoints n))
     ==> add_queue p1 qe p2 n = n`,
  Induct_on `n` >> rw[add_queue_def,endpoints_def]);

val receive_add_queue = Q.store_thm("receive_add_queue",
  `!n1 p1 d p2.
     MEM p2 (MAP FST (endpoints n1)) /\ ALL_DISTINCT (MAP FST (endpoints n1))
     /\ p1 ≠ p2
     ==> trans n1 (LReceive p1 d p2) (add_queue p2 d p1 n1)`,
  Induct_on `n1` >> rpt strip_tac
  >> fs[endpoints_def,ALL_DISTINCT_APPEND,add_queue_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> rpt(first_x_assum (drule o PURE_REWRITE_RULE [NOT_CLAUSES] o CONTRAPOS o SPEC_ALL)) >> rpt strip_tac
  >> fs[add_queue_fresh]
  >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
  >> rveq >> fs[]);

val sender_receiver_distinct = Q.store_thm("sender_receiver_distinct",
  `!n1 p1 d p2 n2.
     trans n1 (LSend p1 d p2) n2 ==> p1 ≠ p2`,
  rpt strip_tac >> pop_assum mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`d`,`p2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[]);

val com_add_queue = Q.store_thm("com_add_queue",
  `!n1 p1 d p2 n2.
    trans n1 (LSend p1 d p2) n2 /\ MEM p2 (MAP FST (endpoints n1))
    /\ ALL_DISTINCT (MAP FST (endpoints n1))
    ==> trans n1 LTau (add_queue p2 d p1 n2)
  `,
  rpt strip_tac
  >> ntac 2 (pop_assum mp_tac)
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`d`,`p2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[add_queue_def,endpoints_def,ALL_DISTINCT_APPEND] >> rveq
  >> rpt(first_x_assum drule >> strip_tac)
  >> rpt(first_x_assum (drule o PURE_REWRITE_RULE [NOT_CLAUSES] o CONTRAPOS o SPEC_ALL)) >> rpt strip_tac
  >> fs[add_queue_fresh,trans_par_r,trans_par_l]
  >> imp_res_tac (GSYM endpoint_names_trans)
  >> fs[add_queue_fresh]
  >> imp_res_tac sender_receiver_distinct
  >> imp_res_tac receive_add_queue
  >> metis_tac[trans_com_l,trans_com_r]);

val com_choice_add_queue = Q.store_thm("com_choice_add_queue",
  `!n1 p1 b p2 n2.
    trans n1 (LIntChoice p1 b p2) n2 /\ MEM p2 (MAP FST (endpoints n1))
    /\ ALL_DISTINCT (MAP FST (endpoints n1))
    ==> trans n1 LTau (add_queue p2 [bool2w b] p1 n2)
  `,
  rpt strip_tac
  >> ntac 2 (pop_assum mp_tac)
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`b`,`p2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[add_queue_def,endpoints_def,ALL_DISTINCT_APPEND] >> rveq
  >> rpt(first_x_assum drule >> strip_tac)
  >> rpt(first_x_assum (drule o PURE_REWRITE_RULE [NOT_CLAUSES] o CONTRAPOS o SPEC_ALL)) >> rpt strip_tac
  >> fs[add_queue_fresh,trans_par_r,trans_par_l]
  >> imp_res_tac (GSYM endpoint_names_trans)
  >> fs[add_queue_fresh]
  >> imp_res_tac sender_receiver_distinct_choice
  >> (Cases_on `b`
      >> fs[bool2w_def]
      >- (imp_res_tac receive_add_queue >> rpt(first_x_assum(qspec_then `[1w]` assume_tac))
          >> fs[trans_ext_choice_T_receive] >> metis_tac[trans_com_choice_l,trans_com_choice_r])
      >- (imp_res_tac receive_add_queue >> rpt(first_x_assum(qspec_then `[0w]` assume_tac))
          >> fs[trans_ext_choice_F_receive] >> metis_tac[trans_com_choice_l,trans_com_choice_r])));

val closing_distance_SUC_IMP = Q.store_thm("closing_distance_SUC_IMP",
`!fv n1 n2 n. choice_rel fv n1 n2 /\ closing_distance fv n1 n2 = SUC n
              /\ ALL_DISTINCT (MAP FST (endpoints n1))
  ==> ?n3 n4 alpha. choice_rel fv n3 n4 /\ closing_distance fv n3 n4 = n
               /\ trans n1 (decompile_label fv n2 alpha) n3 /\ trans n2 alpha n4
               /\ send_or_tau alpha
  `,
  `!fv n1 n2. choice_rel fv n1 n2 ==> !n. closing_distance fv n1 n2 = SUC n
                     /\ ALL_DISTINCT (MAP FST (endpoints n1))
  ==> ?n3 n4 alpha. choice_rel fv n3 n4 /\ closing_distance fv n3 n4 = n
               /\ trans n1 (decompile_label fv n2 alpha) n3 /\ trans n2 alpha n4
               /\ send_or_tau alpha
  ` suffices_by metis_tac[]
  >> ho_match_mp_tac (fetch "-" "choice_rel_strongind")
  >> rpt strip_tac
  >- (* choice_rel_eq_junk *)
     (imp_res_tac junkcong_closing_distance_eq >> pop_assum(qspec_then `n1` assume_tac)
      >> fs[closing_distance_compile_network])
  >- (* choice_rel_eq_par *)
     (fs[closing_distance_def,endpoints_def,ALL_DISTINCT_APPEND]
      >> Cases_on `closing_distance fv n1 n2`
      >- (fs[]
          >> MAP_EVERY qexists_tac [`NPar n1 n3`, `NPar n2 n4`, `alpha`]
          >> fs[closing_distance_def] >> fs[choice_rel_par,trans_par_r]
          >> imp_res_tac choice_rel_endpoints >> imp_res_tac(GSYM endpoint_names_trans) >> fs[]
          >> Cases_on `alpha` >> fs[decompile_label_def]
          >> TRY(match_mp_tac trans_par_r >> first_x_assum ACCEPT_TAC)
          >> imp_res_tac sender_is_endpoint
          >> first_x_assum(qspec_then `s` assume_tac)
          >> rfs[] >> fs[endpoint_sends_fv_def,endpoints_def,FIND_APPEND]
          >> fs[GSYM FIND_o_NOT_MEM] >> match_mp_tac trans_par_r
          >> first_x_assum ACCEPT_TAC)
      >- (fs[]
          >> MAP_EVERY qexists_tac [`NPar n3 n1'`, `NPar n4 n2'`, `alpha`]
          >> fs[closing_distance_def] >> fs[choice_rel_par,trans_par_l]
          >> Cases_on `alpha` >> fs[decompile_label_def]
          >> imp_res_tac choice_rel_endpoints >> imp_res_tac(GSYM endpoint_names_trans) >> fs[]
          >> TRY(match_mp_tac trans_par_l >> first_x_assum ACCEPT_TAC)
          >> imp_res_tac sender_is_endpoint
          >> first_x_assum(qspec_then `s` assume_tac)
          >> rfs[] >> fs[endpoint_sends_fv_def,endpoints_def,FIND_APPEND]
          >> fs[GSYM FIND_o_MEM, GSYM FIND_o_NOT_MEM]
          >> Q.ISPEC_THEN `SOME` (fn thm => fs[thm]) ETA_THM
          >> match_mp_tac trans_par_l
          >> first_x_assum ACCEPT_TAC))
  >- (* choice_rel_int_choice_true *)
    (fs[closing_distance_def,compile_network_fv_def,bool2w_def]
     >> every_case_tac >> fs[endpoints_def,ALL_DISTINCT_APPEND]
     >> MAP_EVERY qexists_tac [`NEndpoint p1 s e`,
                               `NEndpoint p1 (s with bindings := s.bindings |+ (fv,[1w]))
                                             (compile_endpoint fv e)`,
                               `LSend p1 [1w] p2`]
     >> conj_tac
     >- (match_mp_tac choice_rel_eq_junk
         >> fs[var_names_network_def,compile_network_fv_def] >> match_mp_tac junkcong_add_junk
         >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[closing_distance_def]
         >> qmatch_goalsub_abbrev_tac `junkcong _ a1 a2`
         >> `junkcong {fv} a1 a2` suffices_by fs[]
         >> unabbrev_all_tac >> match_mp_tac junkcong_add_junk >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[decompile_label_def,endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,
            sends_fv_def,trans_int_choice])
     >> conj_tac
     >- (match_mp_tac trans_send >> fs[FLOOKUP_UPDATE])
     >> simp[send_or_tau_def])
  >- (* choice_rel_int_choice_false *)
    (fs[closing_distance_def,compile_network_fv_def,bool2w_def]
     >> every_case_tac >> fs[endpoints_def,ALL_DISTINCT_APPEND]
     >> MAP_EVERY qexists_tac [`NEndpoint p1 s e`,
                               `NEndpoint p1 (s with bindings := s.bindings |+ (fv,[0w]))
                                             (compile_endpoint fv e)`,
                               `LSend p1 [0w] p2`]
     >> conj_tac
     >- (match_mp_tac choice_rel_eq_junk
         >> fs[var_names_network_def,compile_network_fv_def] >> match_mp_tac junkcong_add_junk
         >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[closing_distance_def]
         >> qmatch_goalsub_abbrev_tac `junkcong _ a1 a2`
         >> `junkcong {fv} a1 a2` suffices_by fs[]
         >> unabbrev_all_tac >> match_mp_tac junkcong_add_junk >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[decompile_label_def,endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,
            sends_fv_def,trans_int_choice])
     >> conj_tac
     >- (match_mp_tac trans_send >> fs[FLOOKUP_UPDATE])
     >> simp[send_or_tau_def])
  >- (* choice_rel_ext_choice *)
    (fs[closing_distance_def,compile_network_fv_def,bool2w_def]
     >> rpt(pop_assum mp_tac) >> IF_CASES_TAC >> rpt strip_tac
     >- (imp_res_tac junkcong_endpoint_rel_endpoint >> fs[])
     >> rpt(pop_assum mp_tac) >> reverse IF_CASES_TAC >> rpt strip_tac
     >- (fs[] >> first_x_assum(qspecl_then [`q1`,`d`,`q2`] assume_tac) >> fs[EXISTS_MEM,EVERY_MEM]
         >> rfs[])
     >> qpat_x_assum `?x. _` kall_tac >> fs[]
     >> MAP_EVERY qexists_tac [`NEndpoint p2 (s with queue := q1 ⧺ q2) (if d = [1w] then e1 else e2)`,
                               `NEndpoint p2 <|bindings := s.bindings |+ (fv,d);
                                               queue := q1 ⧺ q2|>
                                             (compile_endpoint fv (if d = [1w] then e1 else e2))`,
                               `LTau`]
     >> IF_CASES_TAC
     >> (fs[send_or_tau_def]
     >> conj_tac
     >- (`!b q. <|bindings := b; queue := q|> = (s with queue := q) with bindings := b`
           by simp[endpointLangTheory.state_component_equality]
         >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
         >> match_mp_tac choice_rel_eq_junk
         >> fs[var_names_network_def,compile_network_fv_def]
         >> `!b q. <|bindings := b; queue := q|> = (s with queue := q) with bindings := b`
           by simp[endpointLangTheory.state_component_equality]
         >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
         >> match_mp_tac junkcong_add_junk''' >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[closing_distance_def]
         >> qmatch_goalsub_abbrev_tac `junkcong _ a1 a2`
         >> `junkcong {fv} a1 a2` suffices_by fs[]
         >> unabbrev_all_tac
         >> `!b q. <|bindings := b; queue := q|> = (s with queue := q) with bindings := b`
           by simp[endpointLangTheory.state_component_equality]
         >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
         >> match_mp_tac junkcong_add_junk''' >> fs[]
         >> metis_tac[compile_endpoint_support,free_names_are_names_endpoint])
     >> conj_tac
     >- (fs[decompile_label_def,trans_ext_choice_l,trans_ext_choice_r])
     >> TRY(match_mp_tac trans_if_true >> fs[FLOOKUP_UPDATE] >> NO_TAC)
     >> match_mp_tac trans_if_false >> fs[FLOOKUP_UPDATE])));

val partners_compile_endpoint = Q.store_thm("partners_compile_endpoint",
  `!fv e. partners_endpoint(compile_endpoint fv e) = partners_endpoint e`,
  Induct_on `e` >> rpt strip_tac >> rw[compile_endpoint_def,partners_endpoint_def]);

val partners_compile_network = Q.store_thm("partners_compile_network",
  `!fv n. partners_network(compile_network_fv fv n) = partners_network n`,
  Induct_on `n` >> rpt strip_tac >> rw[compile_network_fv_def,partners_network_def,
                                       partners_compile_endpoint]);

val closed_under_compile_network = Q.store_thm("closed_under_compile_network",
  `!fv n1 e. closed_under e(compile_network_fv fv n1) = closed_under e n1`,
  rw[closed_under_def,partners_compile_network]);

val closed_under_choice_rel = Q.store_thm("closed_under_choice_rel",
  `!fv n1 n2 e. choice_rel fv n1 n2 /\ set (MAP FST (endpoints n1)) ⊆ e /\ closed_under e n1 ==> closed_under e n2`,
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  >> ho_match_mp_tac (fetch "-" "choice_rel_strongind")
  >> rpt strip_tac
  >- (drule closed_under_junkcong >> simp[compile_network_endpoints,closed_under_compile_network]
      >> metis_tac[])
  >> fs[closed_under_def,partners_network_def,endpoints_def,partners_endpoint_def,
        partners_compile_endpoint]);

val junkcong_compile_rel_compile = Q.store_thm("junkcong_compile_rel_compile",
  `!fv n1 n2. junkcong {fv} (compile_network_fv fv n1) n2 ==>
   ?n2'. n2 = compile_network_fv fv n2'`,
  Induct_on `n1` >> rpt strip_tac >> fs[compile_network_fv_def]
  >> imp_res_tac junkcong_nil_rel_nil
  >> imp_res_tac junkcong_endpoint_rel_endpoint
  >> imp_res_tac junkcong_par_rel_par
  >- (qexists_tac `NNil` >> simp[compile_network_fv_def])
  >- (Q.REFINE_EXISTS_TAC `NPar _ _`
      >> fs[compile_network_fv_def]
      >> metis_tac[])
  >- (Q.REFINE_EXISTS_TAC `NEndpoint _ _ _`
      >> fs[compile_network_fv_def]
      >> metis_tac[]));

val closed_network_choice_rel = Q.store_thm("closed_network_choice_rel",
  `!fv n1 n2. choice_rel fv n1 n2 /\ closed_network n1 ==> closed_network n2`,
  simp[closed_network_def] >> rpt strip_tac
  >> drule closed_under_choice_rel
  >> disch_then(qspec_then `set (MAP FST (endpoints n1))` mp_tac)
  >> rw[] >> imp_res_tac (GSYM choice_rel_endpoints) >> rw[]);

val junkcong_compile_closing_distance = Q.store_thm("junkcong_compile_closing_distance",
  `!fv n1 n2. junkcong {fv} (compile_network_fv fv n1) n2 ==> closing_distance fv n1 n2 = 0`,
  Induct_on `n1`
  >> rpt strip_tac >> fs[compile_network_fv_def]
  >- (imp_res_tac junkcong_nil_rel_nil >> fs[closing_distance_def])
  >- (imp_res_tac junkcong_par_rel_par >> fs[closing_distance_def])
  >- (imp_res_tac junkcong_endpoint_rel_endpoint >> fs[closing_distance_def]));

val closing_distance_add_queue = Q.store_thm("closing_distance_add_queue",
  `!fv n1 n2 p1 d p2. choice_rel fv n1 n2 ==>
    closing_distance fv (add_queue p1 d p2 n1) (add_queue p1 d p2 n2) = closing_distance fv n1 n2`,
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  >> ho_match_mp_tac (fetch "-" "choice_rel_strongind")
  >> rpt strip_tac
  >- (drule junkcong_add_queue >> disch_then(qspecl_then [`p1`,`d`,`p2`] assume_tac)
      >> fs[compile_network_add_queue,closing_distance_compile_network]
      >> imp_res_tac junkcong_compile_closing_distance
      >> fs[])
  >- (fs[closing_distance_def,add_queue_def])
  >- (fs[closing_distance_def,add_queue_def]
      >> every_case_tac >> fs[closing_distance_def,compile_endpoint_def,bool2w_def]
      >> IF_CASES_TAC >> fs[]
      >> imp_res_tac junkcong_endpoint_rel_endpoint >> fs[])
  >- (fs[closing_distance_def,add_queue_def]
      >> every_case_tac >> fs[closing_distance_def,compile_endpoint_def,bool2w_def]
      >> IF_CASES_TAC >> fs[]
      >> imp_res_tac junkcong_endpoint_rel_endpoint >> fs[])
  >- (fs[closing_distance_def,add_queue_def]
      >> every_case_tac >> fs[closing_distance_def,compile_endpoint_def,bool2w_def]
      >> IF_CASES_TAC >> fs[]
      >> imp_res_tac junkcong_endpoint_rel_endpoint >> fs[]
      >> IF_CASES_TAC >> fs[] >> rfs[]
      >> fs[FUPD11_SAME_KEY_AND_BASE] >> rveq >> fs[]
      >> first_x_assum (fn thm =>
                          qspecl_then [`q1`,`q2`] assume_tac thm
                          >> qspecl_then [`q1`,`q2 ++ [(p2',d')]`] assume_tac thm
                       )
      >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >> rveq >> fs[]
      >> fs[EXISTS_MEM,EVERY_MEM] >> rfs[]));

val closing_distance_SUC_IMP_tau = Q.store_thm("closing_distance_SUC_IMP_tau",
`!fv n1 n2 n. choice_rel fv n1 n2 /\ closing_distance fv n1 n2 = SUC n
              /\ ALL_DISTINCT (MAP FST (endpoints n1))
              /\ closed_network n1
  ==> ?n3 n4. choice_rel fv n3 n4 /\ closing_distance fv n3 n4 = n
               /\ trans n1 LTau n3 /\ trans n2 LTau n4
  `,
  rpt strip_tac
  >> drule closing_distance_SUC_IMP
  >> rpt(disch_then drule) >> strip_tac
  >> Cases_on `alpha` >> fs[send_or_tau_def, decompile_label_def]
  >> every_case_tac >> fs[] >> rveq >> fs[]
  >> ntac 2 (TRY(drule com_add_queue >> qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac))
  >> ntac 2 (TRY(drule com_choice_add_queue >> qpat_x_assum `trans _ (LIntChoice _ _ _) _` mp_tac))
  >> rpt strip_tac
  >> imp_res_tac choice_rel_endpoints
  >> fs[] >> rfs[]
  >> imp_res_tac closed_network_choice_rel
  >> imp_res_tac closed_network_receiver_mem
  >> fs[bool2w_def]
  >> qpat_x_assum `trans n1 _ _` assume_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ a1`
  >> qexists_tac `a1`
  >> qpat_x_assum `trans n2 _ _` assume_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ a2`
  >> qexists_tac `a2`
  >> unabbrev_all_tac
  >> fs[closing_distance_add_queue,choice_rel_add_queue]
  >> fs[trans_ext_choice_F_receive]);

val decompile_label_id = Q.store_thm("decompile_label_id",
  `!fv n alpha. ¬MEM fv (free_var_names_network n)
   ==> decompile_label fv n alpha = alpha`,
  Cases_on `alpha` >> rpt strip_tac
  >> fs[decompile_label_def,sends_fv_def,endpoint_sends_fv_def]
  >> every_case_tac >> fs[]
  >> imp_res_tac FIND_MEM
  >> `MEM fv (free_var_names_endpoint e)` by(rfs[free_var_names_endpoint_def])
  >> rveq >> rfs[]
  >> imp_res_tac free_var_names_endpoint_in_network);

val decompile_label_id2 = Q.store_thm("decompile_label_id2",
  `!fv n alpha. ¬MEM fv (var_names_network n)
   ==> decompile_label fv n alpha = alpha`,
  metis_tac[decompile_label_id,free_names_are_names]);

val decompile_label_par_l = Q.store_thm("decompile_label_par_l",
  `!n1 n2 n3 n4 fv alpha. weak_trans n1 (decompile_label fv n2 alpha) n3
   /\ MAP FST (endpoints n1) = MAP FST (endpoints n2)
   /\ (∀e. MEM e (MAP FST (endpoints n4)) ⇒ ¬MEM e (MAP FST (endpoints n2)))
   ==> decompile_label fv (NPar n2 n4) alpha = decompile_label fv n2 alpha`,
  rpt strip_tac >> Cases_on `alpha` >> fs[decompile_label_def]
  >> rpt(IF_CASES_TAC) >> fs[] >> rveq >> fs[]
  >> fs[weak_trans_def,weak_tau_trans_def]
  >> imp_res_tac sender_is_endpoint
  >> imp_res_tac choice_sender_is_endpoint
  >> fs[endpoint_sends_fv_def,endpoints_def,FIND_APPEND]
  >> first_x_assum(qspec_then `e` assume_tac)
  >> rveq >> fs[sends_fv_def]
  >> TRY(first_x_assum(qspec_then `z` assume_tac))
  >> imp_res_tac endpoint_names_reduction
  >> every_case_tac >> fs[] >> rveq >> fs[FIND_o_NOT_MEM]
  >> rfs[]);

val decompile_label_par_l_trans = Q.store_thm("decompile_label_par_l_trans",
  `!n1 n2 n3 n4 fv alpha. weak_trans n1 (decompile_label fv n2 alpha) n3
   /\ MAP FST (endpoints n1) = MAP FST (endpoints n2)
   /\ (∀e. MEM e (MAP FST (endpoints n4)) ⇒ ¬MEM e (MAP FST (endpoints n2)))
      ==> weak_trans n1 (decompile_label fv (NPar n2 n4) alpha) n3`,
  metis_tac [decompile_label_par_l]);

val decompile_label_par_r = Q.store_thm("decompile_label_par_r",
  `!n1 n2 n3 n4 fv alpha. weak_trans n1 (decompile_label fv n2 alpha) n3
   /\ MAP FST (endpoints n1) = MAP FST (endpoints n2)
   /\ (∀e. MEM e (MAP FST (endpoints n4)) ⇒ ¬MEM e (MAP FST (endpoints n2)))
   ==> decompile_label fv (NPar n4 n2) alpha = decompile_label fv n2 alpha`,
  rpt strip_tac >> Cases_on `alpha` >> fs[decompile_label_def]
  >> rpt(IF_CASES_TAC) >> fs[] >> rveq >> fs[]
  >> fs[weak_trans_def,weak_tau_trans_def]
  >> imp_res_tac sender_is_endpoint
  >> imp_res_tac choice_sender_is_endpoint
  >> fs[endpoint_sends_fv_def,endpoints_def,FIND_APPEND]
  >> first_x_assum(qspec_then `e` assume_tac)
  >> rveq >> fs[sends_fv_def]
  >> TRY(first_x_assum(qspec_then `z` assume_tac))
  >> imp_res_tac endpoint_names_reduction
  >> every_case_tac >> fs[] >> rveq >> fs[FIND_o_NOT_MEM]
  >> rfs[]
  >> `MEM s (MAP FST (endpoints n4))` by(fs[GSYM FIND_o_MEM])
  >> metis_tac[]);

val decompile_label_par_r_trans = Q.store_thm("decompile_label_par_r_trans",
  `!n1 n2 n3 n4 fv alpha. weak_trans n1 (decompile_label fv n2 alpha) n3
   /\ MAP FST (endpoints n1) = MAP FST (endpoints n2)
   /\ (∀e. MEM e (MAP FST (endpoints n4)) ⇒ ¬MEM e (MAP FST (endpoints n2)))
      ==> weak_trans n1 (decompile_label fv (NPar n4 n2) alpha) n3`,
  metis_tac [decompile_label_par_r]);

val reduction_par = Q.store_thm("reduction_par",
  `!p1 p2 q1 q2. reduction^* p1 p2 /\ reduction^* q1 q2
                 ==> reduction^* (NPar p1 q1) (NPar p2 q2)`,
 metis_tac[reduction_par_l, reduction_par_r, RTC_RTC]);

val choice_rel_trans_pres = Q.prove(
  `!fv n1 n2.
    choice_rel fv n1 n2 ==>
    !n4 alpha. (trans n2 alpha n4 /\ EVERY endpoint_ok (endpoints n1)
                                  /\ ALL_DISTINCT (MAP FST (endpoints n1))
    ==> ?n3. weak_trans n1 (decompile_label fv n2 alpha) n3 ∧ choice_rel fv n3 n4)`,
  ho_match_mp_tac (fetch "-" "choice_rel_strongind") >> conj_tac
  >- (Induct_on `n1`
      >- ((* NNil *)
          rpt strip_tac >> drule junkcong_sym
          >> strip_tac >> drule junkcong_trans_pres >> disch_then drule
          >> fs[trans_nil_false,compile_network_fv_def])
      >- ((* NPar *)
          rpt strip_tac
          >> fs[var_names_network_def,compile_network_fv_def,endpoints_def,EVERY_APPEND,
                ALL_DISTINCT_APPEND]
          >> imp_res_tac junkcong_par_rel_par
          >> rveq >> fs[]
          >> rpt(first_x_assum drule) >> rpt(disch_then drule >> strip_tac)
          >> qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
          >> fs[] >> rveq
          >> rpt(first_x_assum drule) >> rpt(disch_then drule >> strip_tac)
          >> imp_res_tac junkcong_free_var_names
          >> imp_res_tac MEM_free_vars_compile_network
          >> rfs[] >> imp_res_tac (free_names_are_names |> SPEC_ALL |> CONTRAPOS)
          >> rpt(qpat_x_assum `MEM _ _ = MEM _ _` (mp_tac o GSYM)) >> rpt strip_tac
          >> fs[]
          >> qmatch_goalsub_abbrev_tac `decompile_label _ (NPar a1 a2) _`
          >> `¬MEM fv (free_var_names_network (NPar a1 a2))` by(fs[free_var_names_network_def])
          >> fs[decompile_label_id,weak_trans_def,weak_tau_trans_def]
          >> rfs[decompile_label_id]
          >> imp_res_tac choice_rel_eq_junk
          >> qmatch_goalsub_abbrev_tac `choice_rel _ _ (NPar a3 a4)`
          >> qpat_x_assum `choice_rel _ _ a3` mp_tac
          >> qpat_x_assum `choice_rel _ _ a4` mp_tac
          >> rpt strip_tac
          >> drule choice_rel_par >> pop_assum(fn thm => disch_then drule >> assume_tac thm)
          >> strip_tac >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
          >> asm_exists_tac >> simp[]
          >> TRY(match_mp_tac RTC_SANDWICH
                 >> metis_tac[trans_com_l,trans_com_r,reduction_par,reduction_def,
                              trans_com_choice_l,trans_com_choice_r])
          >> rw[]
          >> TRY(MAP_FIRST match_mp_tac [reduction_par_l,reduction_par_r]
                 >> first_x_assum ACCEPT_TAC)
          >> fs[]
          >> metis_tac[trans_par_l,reduction_par_l,trans_par_r,reduction_par_r])
      >- ((* NEndpoint *)
          rpt strip_tac
          >> first_x_assum (assume_tac o MATCH_MP junkcong_sym)
          >> drule junkcong_trans_pres >> disch_then drule
          >> rpt strip_tac
          >> qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
          >> fs[] >> rveq >> fs[compile_network_fv_def,compile_endpoint_def,var_names_network_def,
                                var_names_endpoint_def]
          >- ((* trans_send *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def]
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac junkcong_endpoint_rel_endpoint
              >> rveq
              >> every_case_tac
              >> fs[endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,sends_fv_def]
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_enqueue *)
              rveq
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> fs[decompile_label_def]
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_int_choice *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> every_case_tac >> fs[])
          >- ((* trans_enqueue_choice_l *)
              rveq
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> fs[decompile_label_def]
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_enqueue_choice_r *)
              rveq
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> fs[decompile_label_def]
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_dequeue *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def]
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac junkcong_endpoint_rel_endpoint
              >> rveq
              >> every_case_tac
              >> fs[endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,sends_fv_def]
              >> TRY(imp_res_tac choice_rel_endpoint_eq_junk
                    >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
                    >> asm_exists_tac
                    >> simp[]
                    >> match_mp_tac trans_IMP_weak_trans
                    >> MAP_FIRST match_mp_tac (trans_rules |> SIMP_RULE (srw_ss()) [] |> CONJUNCTS)
                    >> fs[])
              >> qmatch_goalsub_abbrev_tac `weak_trans a1`
              >> qexists_tac `a1`
              >> unabbrev_all_tac
              >> simp[weak_trans_def]
              >> imp_res_tac junkcong_has_fv_eq
              >> fs[free_var_names_endpoint_def, MEM_FILTER]
              >> rveq
              >> match_mp_tac (SIMP_RULE (srw_ss()) [] choice_rel_ext_choice)
              >> fs[])
          >- ((* trans_ext_choice_l *)
              Cases_on `e` >> fs[compile_endpoint_def] >> every_case_tac >> fs[])
          >- ((* trans_ext_choice_r *)
              Cases_on `e` >> fs[compile_endpoint_def] >> every_case_tac >> fs[])
          >- ((* trans_if_true *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def]
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac junkcong_endpoint_rel_endpoint
              >> rveq
              >> every_case_tac
              >> fs[endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,sends_fv_def]
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_if_false *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def]
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac junkcong_endpoint_rel_endpoint
              >> rveq
              >> every_case_tac
              >> fs[endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,sends_fv_def]
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> asm_exists_tac
              >> simp[]
              >> match_mp_tac trans_IMP_weak_trans
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_let *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def,endpoint_ok_def,endpoints_def,EVERY_APPEND,
                    partners_endpoint_def]
              >> rveq >> fs[]
              >> rpt(first_x_assum (mp_tac o MATCH_MP junkcong_sym))
              >> rpt strip_tac
              >> imp_res_tac junkcong_endpoint_rel_endpoint
              >> rveq
              >> every_case_tac
              >> fs[endpoint_sends_fv_def,endpoints_def,FIND_def,INDEX_FIND_def,sends_fv_def]
              >> rveq >> fs[]
              >> imp_res_tac junkcong_has_fv_eq >> fs[free_var_names_endpoint_def,MEM_FILTER]
              >> rveq >> fs[]
              >> imp_res_tac choice_rel_int_choice_true
              >> imp_res_tac choice_rel_int_choice_false
              >> rename1 ‘NEndpoint _ (st with bindings := _)’
              >> rpt(first_x_assum (qspec_then `st` assume_tac))
              >> imp_res_tac choice_rel_endpoint_eq_junk
              >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
              >> simp[K0_def,K1_def]
              >> asm_exists_tac
              >> simp[weak_trans_refl]
              >> match_mp_tac trans_IMP_weak_trans
              >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
              >> fs[])
          >- ((* trans_fix *)
              Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[var_names_endpoint_def]
              >> fs[decompile_label_def,endpoint_ok_def,endpoints_def,EVERY_APPEND,
                    partners_endpoint_def,CaseEq "bool"]
              >> rename1 ‘NEndpoint p s (Fix dn e)’
              >> qexists_tac ‘NEndpoint p s (dsubst e dn (Fix dn e))’
              >> conj_tac
              >- (match_mp_tac trans_IMP_weak_trans >> metis_tac[trans_fix])
              >> match_mp_tac choice_rel_endpoint_eq_junk
              >> simp[compile_network_fv_dsubst]
              >> reverse conj_tac >- metis_tac[junkcong_sym,compile_endpoint_def]
              >> spose_not_then strip_assume_tac
              >> imp_res_tac MEM_var_names_endpoint_dsubst
              >> fs[var_names_endpoint_def])))
  >> rpt strip_tac
  >- ((* choice_rel_par *)
      fs[endpoint_ok_def,endpoints_def,EVERY_APPEND,ALL_DISTINCT_APPEND]
      >> qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
      >> fs[] >> rveq
      >> rpt(first_x_assum drule >> strip_tac)
      >> qmatch_goalsub_abbrev_tac `choice_rel _ _ (NPar a1 a2)`
      >> qpat_x_assum `choice_rel _ _ a1` assume_tac
      >> drule choice_rel_par
      >> qpat_x_assum `choice_rel _ _ a2` assume_tac
      >> disch_then drule >> strip_tac
      >> unabbrev_all_tac
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> asm_exists_tac
      >> simp[]
      >> TRY(match_mp_tac weak_trans_par_r
             >> match_mp_tac decompile_label_par_r_trans
             >> metis_tac[choice_rel_endpoints])
      >> TRY(match_mp_tac weak_trans_par_l
             >> match_mp_tac decompile_label_par_l_trans
             >> metis_tac[choice_rel_endpoints])
      >> fs[weak_trans_def,weak_tau_trans_def,decompile_label_def]
      >> every_case_tac >> fs[] >> rveq >> fs[]
      >> match_mp_tac RTC_SANDWICH
      >> qmatch_goalsub_abbrev_tac `_^* (NPar a1 a2) _ ∧ _ ∧ _^* _ (NPar a3 a4)`
      >> qpat_x_assum `reduction^* a1 _` assume_tac
      >> drule reduction_par
      >> qpat_x_assum `reduction^* a2 _` assume_tac
      >> disch_then drule >> strip_tac
      >> asm_exists_tac >> simp[]
      >> qpat_x_assum `reduction^* _ a3` assume_tac
      >> drule reduction_par
      >> qpat_x_assum `reduction^* _ a4` assume_tac
      >> disch_then drule >> strip_tac
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> asm_exists_tac >> simp[]
      >> unabbrev_all_tac
      >> simp[reduction_def]
      >> imp_res_tac trans_ext_choice_T_receive
      >> imp_res_tac trans_ext_choice_F_receive
      >> metis_tac[trans_com_choice_l,trans_com_choice_r,trans_com_l,trans_com_r])
  >- ((* choice_rel_int_choice_true *)
      qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
      >> fs[FLOOKUP_UPDATE] >> rveq
      >> fs[decompile_label_def,endpoint_sends_fv_def,sends_fv_def,
            FIND_def,INDEX_FIND_def,endpoints_def,ALL_DISTINCT_APPEND,endpoints_def,endpoint_ok_def,
            partners_endpoint_def]
      >- (qexists_tac `NEndpoint p1 s e` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_int_choice]
          >- (match_mp_tac choice_rel_eq_junk
              >> simp[var_names_network_def,compile_network_fv_def]
              >> match_mp_tac junkcong_add_junk >> simp[]
              >> imp_res_tac MEM_free_vars_compile_endpoint
              >> fs[] >> metis_tac[free_names_are_names_endpoint]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LReceive a4 a5 _)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,a5) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_true'
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[1w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_l]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_true'
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[0w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_r]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_true'
              >> simp[])))
  >- ((* choice_rel_int_choice_false *)
      qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
      >> fs[FLOOKUP_UPDATE] >> rveq
      >> fs[decompile_label_def,endpoint_sends_fv_def,sends_fv_def,
            FIND_def,INDEX_FIND_def,endpoints_def,ALL_DISTINCT_APPEND,endpoints_def,endpoint_ok_def,
            partners_endpoint_def]
      >- (qexists_tac `NEndpoint p1 s e` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_int_choice]
          >- (match_mp_tac choice_rel_eq_junk
              >> simp[var_names_network_def,compile_network_fv_def]
              >> match_mp_tac junkcong_add_junk >> simp[]
              >> imp_res_tac MEM_free_vars_compile_endpoint
              >> fs[] >> metis_tac[free_names_are_names_endpoint]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LReceive a4 a5 _)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,a5) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_false'
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[1w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_l]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_false'
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[0w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_r]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_int_choice_false'
              >> simp[])))
  >- ((* choice_rel_ext_choice *)
      qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[Once trans_cases])
      >> fs[FLOOKUP_UPDATE] >> rveq
      >> fs[decompile_label_def,endpoint_sends_fv_def,sends_fv_def,
            FIND_def,INDEX_FIND_def,endpoints_def,endpoint_ok_def,partners_endpoint_def]
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LReceive a4 a5 _)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,a5) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue]
          >- (unabbrev_all_tac
              >> match_mp_tac choice_rel_ext_choice_SNOC
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[1w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_l]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_ext_choice_SNOC
              >> simp[]))
      >- (qmatch_goalsub_abbrev_tac `weak_trans (NEndpoint a1 a2 a3) (LExtChoice a4 _ a5)`
          >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC (a4,[0w]) a2.queue) a3` >> rw[]
          >- metis_tac[trans_IMP_weak_trans,trans_enqueue_choice_r]
          >- (unabbrev_all_tac >> match_mp_tac choice_rel_ext_choice_SNOC
              >> simp[]))
      >- (qexists_tac `NEndpoint p2 (s with queue := q1 ++ q2) e1`
          >> conj_tac
          >- metis_tac[trans_IMP_weak_trans, trans_ext_choice_l]
          >- (match_mp_tac choice_rel_endpoint_eq_junk >> simp[]
              >> match_mp_tac (junkcong_add_junk''' |> SIMP_RULE (srw_ss()) [])
              >> simp[]
              >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))
      >- (qexists_tac `NEndpoint p2 (s with queue := q1 ++ q2) e2`
          >> conj_tac
          >- metis_tac[trans_IMP_weak_trans, trans_ext_choice_r]
          >- (match_mp_tac choice_rel_endpoint_eq_junk >> simp[]
              >> match_mp_tac (junkcong_add_junk''' |> SIMP_RULE (srw_ss()) [])
              >> simp[]
              >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))));

val choice_rel_tau_trans_pres = Q.prove(
  `!n4 fv n1 n2.
    choice_rel fv n1 n2 ∧ trans n2 LTau n4 ∧ EVERY endpoint_ok (endpoints n1)
    ∧ ALL_DISTINCT (MAP FST (endpoints n1))
    ==> ?n3. reduction^* n1 n3 ∧ choice_rel fv n3 n4`,
  rpt strip_tac >> imp_res_tac choice_rel_trans_pres
  >> fs[decompile_label_def,weak_trans_def] >> asm_exists_tac >> simp[]);

val choice_rel_reduction_pres = Q.store_thm("choice_rel_reduction_pres",
  `!fv n1 n2 n4.
    choice_rel fv n1 n2 ∧ reduction^* n2 n4
    ∧ EVERY endpoint_ok (endpoints n1)
    ∧ ALL_DISTINCT (MAP FST (endpoints n1))
    ==> ?n3. reduction^* n1 n3 ∧ choice_rel fv n3 n4`,
  ntac 4 strip_tac
  >> `∀n2 n4.
      (∃n3. reduction^* n1 n3 ∧ choice_rel fv n3 n2
             ∧ EVERY endpoint_ok (endpoints n1)
             ∧ ALL_DISTINCT (MAP FST (endpoints n1)))
      ∧ reduction^* n2 n4 ⇒
      ∃n3. reduction^* n1 n3 ∧ choice_rel fv n3 n4
            ∧ EVERY endpoint_ok (endpoints n1)
            ∧ ALL_DISTINCT (MAP FST (endpoints n1))`
      suffices_by metis_tac[RTC_REFL]
  >> ho_match_mp_tac (GEN_ALL RTC_lifts_invariants)
  >> rw[reduction_def]
  >> imp_res_tac reduction_endpoints_ok
  >> imp_res_tac choice_rel_endpoints
  >> imp_res_tac endpoint_names_reduction
  >> fs[]
  >> drule choice_rel_tau_trans_pres
  >> rpt(disch_then drule)
  >> fs[]
  >> rpt strip_tac
  >> fs[GSYM reduction_def]
  >> imp_res_tac RTC_RTC
  >> asm_exists_tac >> rw[]);

val choice_rel_exit = Q.store_thm("choice_rel_exit",
  `!fv n1 n2.
   choice_rel fv n1 n2 /\ closed_network n1 /\ ALL_DISTINCT (MAP FST (endpoints n1))
   ==> ?n3 n4. (reduction^* n1 n3 /\ reduction^* n2 n4 /\
                junkcong {fv} (compile_network_fv fv n3) n4)
`,
  `!fv n1 n2 n.
   choice_rel fv n1 n2 /\ closed_network n1 /\ closing_distance fv n1 n2 = n
   /\ ALL_DISTINCT (MAP FST (endpoints n1))
   ==> ?n3 n4. (reduction^* n1 n3 /\ reduction^* n2 n4 /\
                junkcong {fv} (compile_network_fv fv n3) n4)
  ` suffices_by metis_tac[]
  >> Induct_on `n`
  >> rpt strip_tac
  >- (imp_res_tac closing_distance_zero_IMP
      >> MAP_EVERY qexists_tac [`n1`,`n2`]
      >> simp[])
  >- (drule closing_distance_SUC_IMP_tau
      >> rpt(disch_then drule) >> strip_tac
      >> first_x_assum drule
      >> impl_tac
      >- (imp_res_tac closed_network_trans >> imp_res_tac endpoint_names_trans >> simp[])
      >> strip_tac
      >> fs[GSYM reduction_def]
      >> Q.ISPEC_THEN `reduction` (imp_res_tac o CONJUNCT2) RTC_RULES
      >> metis_tac[]));

val compile_network_reflection = Q.store_thm("compile_network_reflection",
  `∀n1 n2 q1 d q2 fv.
    ALL_DISTINCT (MAP FST (endpoints n1)) ∧
    ¬MEM fv (var_names_network n1) ∧
    closed_network n1 ∧
    EVERY endpoint_ok (endpoints n1) ∧
    reduction^* (compile_network_fv fv n1) n2
    ==> ?n3 n4. reduction^* n2 n3 ∧
                reduction^* n1 n4 ∧
             junkcong {fv} (compile_network_fv fv n4) n3
  `,
  rpt strip_tac
  >> `choice_rel fv n1 (compile_network_fv fv n1)`
      by(match_mp_tac choice_rel_eq_junk >> simp[junkcong_refl])
  >> drule choice_rel_reduction_pres
  >> rpt(disch_then drule) >> strip_tac
  >> drule closed_network_reduction >> simp[] >> strip_tac
  >> drule choice_rel_exit >> disch_then drule
  >> impl_tac
  >- (imp_res_tac endpoint_names_reduction >> fs[])
  >> strip_tac
  >> asm_exists_tac >> simp[]
  >> metis_tac[RTC_RTC]);

val _ = export_theory ()

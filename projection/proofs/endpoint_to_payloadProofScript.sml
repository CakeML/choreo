open preamble endpointLangTheory payloadLangTheory endpoint_to_payloadTheory
              endpointPropsTheory              
              payloadSemanticsTheory endpointSemanticsTheory payloadPropsTheory
              payloadConfluenceTheory;

val _ = new_theory "endpoint_to_payloadProof";

val compile_queue_append = Q.store_thm("compile_queue_append",
  `∀q1 q2 conf. compile_queue conf (q1 ++ q2) = compile_queue conf q1 ++ compile_queue conf q2`,
  Induct
  >- fs[compile_queue_def]
  >> Cases >> fs[compile_queue_def]);

val compile_queue_lift_ineq = Q.store_thm("compile_queue_lift_ineq",
  `∀conf q1 p1. EVERY (λ(p,_). p ≠ p1) q1 ==> EVERY (λ(p,_). p ≠ p1) (compile_queue conf q1)`,
  recInduct compile_queue_ind
  >> rpt strip_tac
  >> fs[compile_queue_def]
  >> simp[EVERY_MAP]);

val compile_queue_unlift_ineq = Q.store_thm("compile_queue_unlift_ineq",
  `∀conf q1 p1. EVERY (λ(p,_). p ≠ p1) (compile_queue conf q1)
                 /\ conf.payload_size > 0
                 ==> EVERY (λ(p,_). p ≠ p1) q1`,
  recInduct compile_queue_ind
  >> rpt strip_tac
  >> fs[compile_queue_def]
  >> simp[EVERY_MAP]
  >> fs[Once compile_message_def]
  >> every_case_tac >> fs[]);

val list_trans_par_l = Q.store_thm("list_trans_par_l",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar p r) alpha (NPar q r)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemanticsTheory.trans_par_l])

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemanticsTheory.trans_par_r])

val compile_message_preservation_send = Q.store_thm("compile_message_preservation_send",
`∀conf n d v p1 p2 e s.
    FLOOKUP s.bindings v = SOME d
    ∧ conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
        (NEndpoint p1 s
         (Send p2 v n e))
        (MAP (λm. LSend p1 m p2) (compile_message conf (DROP n d)))
        (NEndpoint p1 s e)
  `,
  ntac 3 GEN_TAC
  >> qpat_abbrev_tac `a1 = DROP n d`
  >> pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`d`,`n`,`a1`,`conf`]
  >> recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [compile_message_def]
  >> rveq >> fs[]
  >> IF_CASES_TAC
  >- (simp[list_trans_def] >> match_mp_tac trans_send_last_payload >> fs[final_pad_LENGTH])
  >- (fs[list_trans_def,NOT_LESS_EQUAL,intermediate_pad_LENGTH,pad_not_final]
      >> drule(trans_send_intermediate_payload|>REWRITE_RULE[GREATER_DEF])
      >> disch_then(qspecl_then [`conf`,`n`] mp_tac)
      >> simp[]
      >> disch_then drule
      >> disch_then(qspecl_then [`e`] assume_tac)
      >> asm_exists_tac
      >> fs[DROP_DROP]));

val compile_message_preservation_send0 = Q.store_thm("compile_message_preservation_send0",
`∀conf d v p1 p2 e s.
    FLOOKUP s.bindings v = SOME d
    ∧ conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
        (NEndpoint p1 s
         (Send p2 v 0 e))
        (MAP (λm. LSend p1 m p2) (compile_message conf d))
        (NEndpoint p1 s e)
  `,
  rpt strip_tac >> imp_res_tac compile_message_preservation_send
  >> first_x_assum(qspec_then `0` mp_tac) >> fs[]);

val compile_network_preservation_send = Q.store_thm("compile_network_preservation_send",
  `∀p1 p2 q1 d q2 conf.
    conf.payload_size > 0
    ∧ trans p1 (LSend q1 d q2) p2
    ==> list_trans conf (compile_network conf p1)
                        (MAP (λm. LSend q1 m q2) (compile_message conf d))
                        (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `conf.payload_size > 0` mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`conf`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- ((* trans_send *)
      simp[compile_network_def,compile_endpoint_def,list_trans_def]
      >> match_mp_tac compile_message_preservation_send0 >> simp[])
  >- ((* trans_par_l *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_l)
  >- ((* trans_par_r *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_r));

val compile_message_preservation_enqueue = Q.store_thm("compile_message_preservation_enqueue",
  `∀conf d q p1 p2 e s.
    conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
  (NEndpoint p2 (s with queue := q) e)
  (MAP (λm. LReceive p1 m p2) (compile_message conf d))
  (NEndpoint p2
     (s with queue := q ⧺ MAP (λd. (p1,d)) (compile_message conf d)) e)
  `,
  recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [compile_message_def]
  >> simp[]
  >> IF_CASES_TAC
  >- (simp[list_trans_def] >> drule payloadSemanticsTheory.trans_enqueue >> simp[SNOC_APPEND]
      >> disch_then(qspecl_then [`conf`,`s with queue := q`] mp_tac)
      >> simp[])
  >- (fs[list_trans_def,NOT_LESS_EQUAL,pad_not_final]
      >> drule payloadPropsTheory.trans_enqueue'
      >> disch_then (qspecl_then [`conf`,`s`,`pad conf d`,`e`,`q`] assume_tac)
      >> asm_exists_tac >> simp[]
      >> first_x_assum drule
      >> disch_then (qspec_then `q ++ [(p1,pad conf d)]` assume_tac)
      >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND]));

val compile_network_preservation_receive = Q.store_thm("compile_network_preservation_receive",
  `∀p1 p2 q1 d q2 conf.
    conf.payload_size > 0
    ∧ trans p1 (LReceive q1 d q2) p2
    ==> list_trans conf (compile_network conf p1)
                        (MAP (λm. LReceive q1 m q2) (compile_message conf d))
                        (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `conf.payload_size > 0` mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`conf`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- ((* trans_enqueue *)
      simp[compile_network_def,compile_endpoint_def,SNOC_APPEND,compile_queue_append,
           compile_queue_def,compile_message_preservation_enqueue])
  >- ((* trans_par_l *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_l)
  >- ((* trans_par_r *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_r));

val compile_network_preservation_com_l = Q.store_thm("compile_network_preservation_com_l",
  `∀conf d p1 p2 r1 r2 q1 q2.
    conf.payload_size > 0
    ∧ q1 ≠ q2
    ∧ list_trans conf p1
                        (MAP (λm. LSend q1 m q2) d)
                        p2
    ∧ list_trans conf r1
                        (MAP (λm. LReceive q1 m q2) d)
                        r2
    ==> (reduction conf)^* (NPar p1 r1) (NPar p2 r2)
  `,
  Induct_on `d` >> rpt strip_tac
  >> fs[list_trans_def]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> imp_res_tac payloadSemanticsTheory.trans_com_l
  >> simp [payloadSemanticsTheory.reduction_def]
  >> asm_exists_tac
  >> simp[] >> metis_tac[])

val compile_network_preservation_com_r = Q.store_thm("compile_network_preservation_com_r",
  `∀conf d p1 p2 r1 r2 q1 q2.
    conf.payload_size > 0
    ∧ q1 ≠ q2
    ∧ list_trans conf p1
                        (MAP (λm. LReceive q1 m q2) d)
                        p2
    ∧ list_trans conf r1
                        (MAP (λm. LSend q1 m q2) d)
                        r2
    ==> (reduction conf)^* (NPar p1 r1) (NPar p2 r2)
  `,
  Induct_on `d` >> rpt strip_tac
  >> fs[list_trans_def]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> imp_res_tac payloadSemanticsTheory.trans_com_r
  >> simp [payloadSemanticsTheory.reduction_def]
  >> asm_exists_tac
  >> simp[] >> metis_tac[])

val compile_message_preservation_dequeue = Q.store_thm("compile_message_preservation_dequeue",
  `!conf d ds p1 p2 q1 q2 e s v.
   p1 ≠ p2 /\ conf.payload_size > 0 /\ EVERY (λ(p,_). p ≠ p1) q1
   ==>                                                                                       
   (reduction conf)^*
    (NEndpoint p2
               (s with queue := q1 ⧺ MAP (λd. (p1,d)) (compile_message conf d) ⧺ q2)
               (Receive p1 v ds e))
    (NEndpoint p2
               <|bindings := s.bindings |+ (v,FLAT(ds) ++ d);
                 queue := q1 ⧺ q2|>
               e)`,
  recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[compile_message_def]
  >> simp[]
  >> IF_CASES_TAC
  >- (match_mp_tac RTC_SINGLE
      >> simp[payloadSemanticsTheory.reduction_def]
      >> drule trans_dequeue_last_payload'
      >> rpt(disch_then drule) >> simp[SNOC_APPEND,unpad_pad,final_pad_TAKE])
  >- (match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
      >> fs[pad_not_final] >> first_x_assum drule >> disch_then drule
      >> disch_then(qspecl_then [`ds ++ [TAKE conf.payload_size d]`,
                    `q2`,`e`,`s`,`v`] assume_tac)
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> fs[] >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,TAKE_DROP]
      >> asm_exists_tac >> simp[]
      >> simp[payloadSemanticsTheory.reduction_def]
      >> drule trans_dequeue_intermediate_payload'
      >> rpt(disch_then drule) >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND,
                                                        unpad_pad]));

val compile_network_preservation_trans = Q.store_thm("compile_network_preservation_trans",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ choice_free_network p1
    ∧ reduction p1 p2
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `conf.payload_size > 0` mp_tac
  >> qpat_x_assum `choice_free_network _` mp_tac      
  >> fs[endpointSemanticsTheory.reduction_def,payloadSemanticsTheory.reduction_def]
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> (W(curry Q.SPEC_TAC)) `conf`
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac endpointSemanticsTheory.trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- ((* trans_com_l *)
      MAP_EVERY imp_res_tac [compile_network_preservation_send,
                             compile_network_preservation_receive,
                             compile_network_preservation_com_l]
      >> simp[compile_network_def])
  >- ((* trans_com_r *)
      MAP_EVERY imp_res_tac [compile_network_preservation_send,
                             compile_network_preservation_receive,
                             compile_network_preservation_com_r]
      >> simp[compile_network_def])
  >- ((*trans_com_choice_l*)
      fs[choice_free_network_def] >> metis_tac[choice_free_network_no_choice])
  >- ((*trans_com_choice_r*)
      fs[choice_free_network_def] >> metis_tac[choice_free_network_no_choice])
  >- ((* trans_dequeue *)
       simp[compile_network_def,compile_endpoint_def,compile_queue_def,compile_queue_append]
       >> drule compile_message_preservation_dequeue
       >> drule compile_queue_lift_ineq >> disch_then(qspec_then `conf` assume_tac)
       >> disch_then drule >> disch_then drule
       >> disch_then(qspecl_then [`d`,`[]`] mp_tac)
       >> simp[])
  >- ((* trans_ext_choice_l *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_ext_choice_r *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_if_true *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_if_true
      >> simp[])
  >- ((* trans_if_false *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_if_false
      >> simp[])
  >- ((* trans_let *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> `EVERY IS_SOME (MAP (FLOOKUP ((s with queue:=compile_queue conf s.queue) .bindings)) vl)`
          by(fs[EVERY_MAP])
      >> drule payloadSemanticsTheory.trans_let >> fs[payloadSemanticsTheory.reduction_def])
  >- ((* trans_par_l *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_l)
  >- ((* trans_par_r *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_r));

val compile_network_preservation_trans = Q.store_thm("compile_network_preservation_trans",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ choice_free_network p1
    ∧ reduction p1 p2
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `conf.payload_size > 0` mp_tac
  >> qpat_x_assum `choice_free_network _` mp_tac      
  >> fs[endpointSemanticsTheory.reduction_def,payloadSemanticsTheory.reduction_def]
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> (W(curry Q.SPEC_TAC)) `conf`
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac endpointSemanticsTheory.trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- ((* trans_com_l *)
      MAP_EVERY imp_res_tac [compile_network_preservation_send,
                             compile_network_preservation_receive,
                             compile_network_preservation_com_l]
      >> simp[compile_network_def])
  >- ((* trans_com_r *)
      MAP_EVERY imp_res_tac [compile_network_preservation_send,
                             compile_network_preservation_receive,
                             compile_network_preservation_com_r]
      >> simp[compile_network_def])
  >- ((*trans_com_choice_l*)
      fs[choice_free_network_def] >> metis_tac[choice_free_network_no_choice])
  >- ((*trans_com_choice_r*)
      fs[choice_free_network_def] >> metis_tac[choice_free_network_no_choice])
  >- ((* trans_dequeue *)
       simp[compile_network_def,compile_endpoint_def,compile_queue_def,compile_queue_append]
       >> drule compile_message_preservation_dequeue
       >> drule compile_queue_lift_ineq >> disch_then(qspec_then `conf` assume_tac)
       >> disch_then drule >> disch_then drule
       >> disch_then(qspecl_then [`d`,`[]`] mp_tac)
       >> simp[])
  >- ((* trans_ext_choice_l *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_ext_choice_r *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_if_true *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_if_true
      >> simp[])
  >- ((* trans_if_false *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_if_false
      >> simp[])
  >- ((* trans_let *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def]
      >> match_mp_tac RTC_SUBSET
      >> `EVERY IS_SOME (MAP (FLOOKUP ((s with queue:=compile_queue conf s.queue) .bindings)) vl)`
          by(fs[EVERY_MAP])
      >> drule payloadSemanticsTheory.trans_let >> fs[payloadSemanticsTheory.reduction_def])
  >- ((* trans_par_l *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_l)
  >- ((* trans_par_r *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_r));

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀conf p1 p2.
    conf.payload_size > 0
    ∧ reduction^* p1 p2 ∧ choice_free_network p1
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
  `,
  strip_tac >> simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  >> strip_tac
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[]
  >> fs[reduction_def]
  >> imp_res_tac choice_free_trans_pres
  >> first_x_assum drule >> strip_tac
  >> fs[GSYM reduction_def]
  >> drule compile_network_preservation_trans >> simp[Once CONJ_SYM]
  >> rpt(disch_then drule) >> strip_tac >> metis_tac[RTC_RTC]);

Theorem compile_queue_split_init:
  compile_queue conf q = (p1,d)::q2 /\ conf.payload_size > 0
  ==> ?ds q22. q = (p1,ds)::q22 /\ LENGTH(compile_message conf ds) > 0 /\
        HD(compile_message conf ds) = d
Proof
  Cases_on `q`
  >- rw[compile_queue_def]
  >> Cases_on `h` >> rw[compile_queue_def]
  >> fs[Once compile_message_def]
  >> every_case_tac >> fs[]
QED

Theorem compile_queue_split:
  !q1 q p1 d q2 conf.
  compile_queue conf q = q1 ++ [(p1,d)] ++ q2
  /\ EVERY (λ(p,_). p ≠ p1) q1
  /\ conf.payload_size > 0
  ==> ?q11 ds q22. q = q11 ++ [(p1,ds)] ++ q22 /\ LENGTH(compile_message conf ds) > 0 /\
        HD(compile_message conf ds) = d /\ EVERY (λ(p,_). p ≠ p1) q11
Proof
  Induct_on `q`
  >- rw[compile_queue_def]
  >> Cases >> Cases
  >- (rw[] >> qexists_tac `[]` >> PURE_REWRITE_TAC[APPEND,EVERY_DEF] >>
      metis_tac[compile_queue_split_init])
  >> rw[compile_queue_def,Once compile_message_def]
  >> fs[]
  >- (first_x_assum drule
      >> disch_then drule
      >> impl_tac >- simp[]
      >> strip_tac
      >> Q.REFINE_EXISTS_TAC `(_,_)::q11`
      >> rw[])
  >> fs[APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)]
  >> fs[MAP_EQ_APPEND]
  >> rveq
  >> fs[EVERY_APPEND]
  >> first_x_assum drule
  >> disch_then drule
  >> impl_tac >- simp[]
  >> strip_tac
  >> Q.REFINE_EXISTS_TAC `(_,_)::q11`
  >> rw[]
QED

val compile_network_reflection_single = Q.store_thm("compile_network_reflection_single",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ reduction conf (compile_network conf p1) p2
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ choice_free_network p1
    ==> ∃p3 p4. (reduction conf)^* p2 p3
             ∧ reduction p1 p4
             ∧ p3 = compile_network conf p4`,
  Induct_on `p1` >> rw[compile_network_def]
  >- (* NNil *)
     fs[payloadSemanticsTheory.reduction_def,trans_nil_false]
  >- (* NPar *)
     (fs[payloadSemanticsTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemanticsTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Com-L *)
         cheat
      >- (* Com-R *)
         cheat
      >- (* Par-L *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemanticsTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) reduction_par_l >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_l,reduction_def])
      >- (* Par-R *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemanticsTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) reduction_par_r >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_r,reduction_def]))
  >- (* NEndpoint *)
     (fs[payloadSemanticsTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemanticsTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Dequeue-last-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >>
          drule_all_then strip_assume_tac compile_queue_split >>
          `compile_message conf ds = [d]`
            by(fs[compile_queue_append,compile_queue_def,Once compile_message_def] >>
               rw[] >> rw[Once compile_message_def] >>
               rfs[] >> fs[]) >>
          fs[compile_queue_append,compile_queue_def] >>
          fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
          rveq >> fs[] >> rveq >> fs[] >>
          drule compile_queue_lift_ineq >> disch_then(qspec_then `conf` assume_tac) >>
          rfs[] >>
          rename1 `Receive _ _ ec` >>
          `ds = unpad d`
           by(Cases_on `d` >> fs[final_def,unpad_def] >>
              rfs[Once compile_message_def] >>
              every_case_tac >> fs[pad_def] >>
              every_case_tac >> fs[] >>
              rveq >> fs[final_def] >>
              fs[SPLITP_NIL_SND_EVERY] >>
              fs[SPLITP_APPEND,EXISTS_REPLICATE,APPEND_EQ_CONS] >>
              rveq >> fs[] >> fs[SPLITP]) >>
          rveq >>
          qexists_tac `NEndpoint l <|bindings := s.bindings |+ (s', unpad d);
                                     queue := q11 ++ q22|> ec` >>
          simp[compile_network_def,compile_queue_append,reduction_def] >>
          match_mp_tac(trans_dequeue |> SIMP_RULE (srw_ss()) []) >>
          rw[] >>
          metis_tac[compile_queue_unlift_ineq])
      >- (* Dequeue-intermediate-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >>
          drule_all_then strip_assume_tac compile_queue_split >>
          rename1 `endpointLang$Receive p v exp` >>
          qexists_tac `NEndpoint l <|queue := q11 ++ q22;bindings:=s.bindings |+ (v,ds)|> exp` >>
          reverse conj_asm2_tac >-
            (rw[reduction_def] >>
             match_mp_tac(trans_dequeue |> SIMP_RULE (srw_ss()) []) >>
             rw[]) >>
          simp[] >>
          `compile_message conf ds = d::compile_message conf(DROP conf.payload_size ds)`
            by(fs[compile_queue_append,compile_queue_def,Once compile_message_def] >>
               rw[] >> rw[Once compile_message_def] >>
               rfs[] >> fs[] >> metis_tac[pad_not_final]) >>
          fs[compile_network_def,compile_queue_append,compile_queue_def] >>
          fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
          rveq >> fs[] >> rveq >> fs[] >>
          drule compile_queue_lift_ineq >> disch_then(qspec_then `conf` assume_tac) >>
          rfs[] >>
          drule compile_message_preservation_dequeue >>
          disch_then drule >>
          qpat_x_assum `EVERY _ (compile_queue _ _)` assume_tac >>
          disch_then drule >>          
          disch_then(qspecl_then [`DROP conf.payload_size ds`,
                                  `[unpad d]`,`compile_queue conf q22`,
                                  `compile_endpoint exp`,
                                  `s`,`v`] mp_tac) >>
          simp[] >>
          `ds = unpad d ++ DROP conf.payload_size ds` suffices_by metis_tac[] >>
          qpat_x_assum `compile_message _ _ = _` mp_tac >>
          rw[Once compile_message_def]
          >- (fs[Once compile_message_def] >> every_case_tac >> fs[])
          >> fs[unpad_pad])
      >- (* If-L *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          qexists_tac `NEndpoint l s e1` >>
          simp[compile_network_def] >>
          simp[reduction_def] >>
          metis_tac[trans_if_true])
      >- (* If-R *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          qexists_tac `NEndpoint l s e1` >>
          simp[compile_network_def] >>
          simp[reduction_def] >>
          metis_tac[trans_if_false])
      >- (* Let *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          qexists_tac `NEndpoint l (s with bindings := s.bindings |+ (s',f (MAP (THE ∘ FLOOKUP s.bindings) l'))) e1` >> (* TODO: generated names*)
          simp[compile_network_def] >>
          simp[reduction_def] >>
          metis_tac[trans_let]))
  );

Theorem reduction_list_trans:
  (reduction conf)^* p q = ?n. list_trans conf p (REPLICATE n LTau) q
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (MAP_EVERY qid_spec_tac [`q`,`p`] >>
      ho_match_mp_tac RTC_INDUCT >>
      rw[]
      >- (qexists_tac `0` >> simp[list_trans_def])
      >- (fs[payloadSemanticsTheory.reduction_def] >>
          qexists_tac `SUC n` >>
          simp[list_trans_def] >>
          asm_exists_tac >> simp[]))
  >- (rpt strip_tac >> pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [`q`,`p`,`n`] >>
      Induct >>
      rw[list_trans_def] >>
      fs[GSYM payloadSemanticsTheory.reduction_def] >>
      metis_tac[RTC_RULES])
QED

Theorem compile_network_endpoints:
  MAP FST(endpoints(compile_network conf p1)) = MAP FST (endpoints p1)
Proof
  Induct_on `p1` >>
  rw[payloadPropsTheory.endpoints_def,endpointPropsTheory.endpoints_def,
     compile_network_def]
QED

val compile_network_reflection = Q.store_thm("compile_network_reflection",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ (reduction conf)^* (compile_network conf p1) p2
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ choice_free_network p1
    ==> ∃p3 p4. (reduction conf)^* p2 p3
             ∧ reduction^* p1 p4
             ∧ qcong p3 (compile_network conf p4)`,
  simp[reduction_list_trans,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases
  >- (rw[list_trans_def] >>
      CONV_TAC(RESORT_EXISTS_CONV rev) >>
      qexists_tac `0` >> rw[list_trans_def] >>
      metis_tac[qcong_refl,RTC_REFL])
  >- (rw[list_trans_def,GSYM payloadSemanticsTheory.reduction_def] >>
      drule_all(compile_network_reflection_single
                |> REWRITE_RULE[PULL_EXISTS,reduction_list_trans]) >>
      strip_tac >>
      rveq >>
      dxrule payload_confluence_weak_contract >>
      disch_then dxrule >>
      impl_tac
      >- (metis_tac[endpoint_names_trans,payloadSemanticsTheory.reduction_def,
                    compile_network_endpoints]) >>
      strip_tac >>
      rename1 `list_trans _ (compile_network _ _) (REPLICATE stepcount _) _` >>
      first_x_assum(qspec_then `stepcount` mp_tac ) >>
      impl_tac >- simp[] >>
      disch_then drule >>
      disch_then drule >>
      impl_tac >- (conj_tac >-
                     (metis_tac[reduction_def,endpointPropsTheory.endpoint_names_trans,
                                endpoint_names_list_trans]) >>
                   fs[reduction_def] >>
                   imp_res_tac choice_free_trans_pres) >>
      strip_tac >>
      qhdtm_x_assum `qcong` mp_tac >>
      drule_all_then strip_assume_tac qcong_list_trans_pres >>
      strip_tac >>
      rename1 `list_trans conf p2 (REPLICATE sc1 _) r` >>
      rename1 `list_trans conf r (REPLICATE sc2 _) t` >>
      `list_trans conf p2 (REPLICATE (sc1 + sc2) LTau) t`
        by(simp[GSYM REPLICATE_APPEND,list_trans_append] >>
           metis_tac[]) >>
      asm_exists_tac >>
      drule_all_then assume_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
      simp[] >> asm_exists_tac >>
      metis_tac[qcong_rules])
  );

val _ = export_theory ()

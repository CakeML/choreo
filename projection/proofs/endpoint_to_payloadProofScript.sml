open preamble endpointLangTheory payloadLangTheory endpoint_to_payloadTheory
              payloadSemanticsTheory endpointSemanticsTheory payloadPropsTheory;

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

val list_trans_def = Define `
    (list_trans conf p [] q = (p = q))
 /\ (list_trans conf p (alpha::l) q = ?p'. trans conf p alpha p' /\ list_trans conf p' l q)`

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
  `∀conf d p1 p2 e s.
    conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
        (NEndpoint p1 s
         (Send p2 (INR d) e))
        (MAP (λm. LSend p1 m p2) (compile_message conf d))
        (NEndpoint p1 s e)
  `,
  recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [compile_message_def]
  >> simp[]
  >> IF_CASES_TAC
  >- (simp[list_trans_def] >> match_mp_tac trans_send_last_payload >> simp[])
  >- (fs[list_trans_def,NOT_LESS_EQUAL]
      >> drule(trans_send_intermediate_payload|>REWRITE_RULE[GREATER_DEF])
      >> disch_then drule
      >> disch_then(qspecl_then [`s`,`e`] assume_tac)
      >> asm_exists_tac
      >> simp[]))

val compile_network_preservation_send = Q.store_thm("compile_network_preservation_send",
  `∀p1 p2 q1 d q2 conf.
    conf.payload_size > 0
    ∧ trans p1 (LSend q1 d q2) p2
    ==> list_trans conf (compile_network conf p1)
                        (LTau::MAP (λm. LSend q1 m q2) (compile_message conf d))
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
      >> qexists_tac `NEndpoint p1 (s with queue := compile_queue conf s.queue)
                      (Send p2 (INR d) (compile_endpoint e))`
      >> conj_tac
      >- (match_mp_tac trans_send_var >> simp[])
      >- (match_mp_tac compile_message_preservation_send >> simp[]))
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
  >- (fs[list_trans_def,NOT_LESS_EQUAL]
      >> drule payloadPropsTheory.trans_enqueue'
      >> disch_then (qspecl_then [`conf`,`s`,`2w::TAKE conf.payload_size d`,`e`,`q`] assume_tac)
      >> asm_exists_tac >> simp[]
      >> first_x_assum drule
      >> disch_then (qspec_then `q ++ [(p1,2w::TAKE conf.payload_size d)]` assume_tac)
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

val compile_network_preservation_int_choice = Q.store_thm("compile_network_preservation_int_choice",
  `∀p1 p2 q1 b q2 conf.
    trans p1 (LIntChoice q1 b q2) p2
    ==> trans conf (compile_network conf p1) (LIntChoice q1 b q2) (compile_network conf p2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`b`,`q2`,`conf`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- ((* trans_int_choice *)
      simp[compile_network_def,compile_endpoint_def]
      >> match_mp_tac payloadSemanticsTheory.trans_int_choice
      >> rw[])
  >- ((* trans_par_l *)
      simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_par_l])
  >- ((* trans_par_r *)
      simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_par_r]));

val compile_network_preservation_ext_choice = Q.store_thm("compile_network_preservation_ext_choice",
  `∀p1 p2 q1 b q2 conf.
    conf.payload_size > 0 /\ trans p1 (LExtChoice q1 b q2) p2
    ==> trans conf (compile_network conf p1) (LExtChoice q1 b q2) (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `_.payload_size > _` mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`b`,`q2`,`conf`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- ((* trans_enqueue_choice_l *)
     simp[compile_network_def,compile_endpoint_def,SNOC_APPEND,compile_queue_append,
          compile_queue_def]
     >> PURE_ONCE_REWRITE_TAC [compile_message_def]
     >> fs[] >> fs[GSYM SNOC_APPEND]
     >> match_mp_tac trans_enqueue_choice_l' >> rw[])
  >- ((* trans_enqueue_choice_r *)
     simp[compile_network_def,compile_endpoint_def,SNOC_APPEND,compile_queue_append,
          compile_queue_def]
     >> PURE_ONCE_REWRITE_TAC [compile_message_def]
     >> fs[] >> fs[GSYM SNOC_APPEND]
     >> match_mp_tac trans_enqueue_choice_r' >> rw[])
  >- ((* trans_par_l *)
      simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_par_l])
  >- ((* trans_par_r *)
      simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_par_r]));

val MAP_TL_compile_message = Q.store_thm("MAP_TL_compile_message",
  `!conf d. conf.payload_size > 0 ==> FLAT(MAP TL (compile_message conf d)) = d`,
  recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [compile_message_def]
  >> rw[])
  
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
      >> disch_then drule >> simp[SNOC_APPEND])
  >- (match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
      >> fs[] >> first_x_assum drule >> disch_then drule
      >> disch_then(qspecl_then [`ds ++ [TAKE conf.payload_size d]`,
                    `q2`,`e`,`s`,`v`] assume_tac)
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> fs[] >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,TAKE_DROP]
      >> asm_exists_tac >> simp[]
      >> simp[payloadSemanticsTheory.reduction_def]
      >> drule trans_dequeue_intermediate_payload'
      >> disch_then drule >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND]));

val compile_network_preservation_trans = Q.store_thm("compile_network_preservation_trans",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ reduction p1 p2
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
  `,
  rpt strip_tac
  >> qpat_x_assum `conf.payload_size > 0` mp_tac
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
                             compile_network_preservation_receive]
      >> fs[list_trans_def]
      >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> imp_res_tac compile_network_preservation_com_l
      >> simp[compile_network_def] >> asm_exists_tac
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_par_l
      >> simp[])
  >- ((* trans_com_r *)
      MAP_EVERY imp_res_tac [compile_network_preservation_send,
                             compile_network_preservation_receive]
      >> fs[list_trans_def]
      >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
      >> PURE_ONCE_REWRITE_TAC [CONJ_SYM]
      >> imp_res_tac compile_network_preservation_com_r
      >> simp[compile_network_def] >> asm_exists_tac
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac payloadSemanticsTheory.trans_par_r
      >> simp[])
  >- ((* trans_com_choice_l *)
      MAP_EVERY imp_res_tac [compile_network_preservation_ext_choice,
                             compile_network_preservation_int_choice]
      >> match_mp_tac RTC_SINGLE >> simp[payloadSemanticsTheory.reduction_def]
      >> simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_com_choice_l])
  >- ((* trans_com_choice_r *)
      MAP_EVERY imp_res_tac [compile_network_preservation_ext_choice,
                             compile_network_preservation_int_choice]
      >> match_mp_tac RTC_SINGLE >> simp[payloadSemanticsTheory.reduction_def]
      >> simp[compile_network_def]
      >> metis_tac[payloadSemanticsTheory.trans_com_choice_r])
  >- ((* trans_dequeue *)
       simp[compile_network_def,compile_endpoint_def,compile_queue_def,compile_queue_append]
       >> drule compile_message_preservation_dequeue
       >> drule compile_queue_lift_ineq >> disch_then(qspec_then `conf` assume_tac)
       >> disch_then drule >> disch_then drule
       >> disch_then(qspecl_then [`d`,`[]`] mp_tac)
       >> simp[])
  >- ((* trans_ext_choice_l *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def,compile_queue_append]
      >> PURE_ONCE_REWRITE_TAC[compile_message_def]
      >> fs[]
      >> drule compile_queue_lift_ineq
      >> disch_then (qspec_then `conf` assume_tac)
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac trans_ext_choice_l'
      >> simp[])
  >- ((* trans_ext_choice_r *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def,compile_queue_append]
      >> PURE_ONCE_REWRITE_TAC[compile_message_def]
      >> fs[]
      >> drule compile_queue_lift_ineq
      >> disch_then (qspec_then `conf` assume_tac)
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemanticsTheory.reduction_def]
      >> match_mp_tac trans_ext_choice_r'
      >> simp[])
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
      fs[compile_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_l)
  >- ((* trans_par_r *)
      fs[compile_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_r));

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ reduction^* p1 p2
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
  `,
  metis_tac[compile_network_preservation_trans,RTC_lifts_reflexive_transitive_relations,
            RTC_TRANSITIVE,RTC_REFLEXIVE]);

val compile_network_reflection = Q.store_thm("compile_network_reflection",
  `∀p1 p2 conf.
    conf.payload_size > 0
    ∧ (reduction conf)^* (compile_network conf p1) p2
    ==> ∃p3 p4. (reduction conf)^* p2 p3
             ∧ reduction^* p1 p4
             ∧ qcong p3 (compile_network conf p4)`,
  cheat);

val _ = export_theory ()

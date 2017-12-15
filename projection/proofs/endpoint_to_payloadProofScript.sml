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
  >> rpt strip_tac >> fs[]
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
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

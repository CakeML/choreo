open preamble endpointLangTheory payloadLangTheory endpoint_to_payloadTheory
              endpointPropsTheory
              payloadSemTheory endpointSemTheory payloadPropsTheory
              payloadConfluenceTheory;

val _ = new_theory "endpoint_to_payloadProof";

Theorem compile_queue_SNOC:
  ∀q p d conf.
        compile_queue conf (SNOC (p,d) q) =
        compile_queue conf q |+ (p, qlk(compile_queue conf q) p ++ compile_message conf d)
Proof
  Induct >- rw[compile_queue_def]
  >> Cases >> fs[compile_queue_def]
  >> rw[fmap_eq_flookup,FLOOKUP_UPDATE]
  >> rw[]
QED

(*
val compile_queue_append = Q.store_thm("compile_queue_append",
  `∀q1 q2 conf. compile_queue conf (q1 ++ q2) = compile_queue conf q2 |++ compile_queue conf q2`,
  Induct
  >- fs[compile_queue_def]
  >> Cases >> fs[compile_queue_def]);
*)

val compile_queue_lift_ineq = Q.store_thm("compile_queue_lift_ineq",
  `∀conf q1 p1. EVERY (λ(p,_). p ≠ p1) q1 ==> qlk (compile_queue conf q1) p1 = []`,
  recInduct compile_queue_ind
  >> rpt strip_tac
  >> fs[compile_queue_def,qlk_def,fget_def]
  >> rw[FLOOKUP_UPDATE]);

val compile_queue_lift_ineq' = Q.store_thm("compile_queue_lift_ineq'",
  `∀conf q1 q2 p1. EVERY (λ(p,_). p ≠ p1) q1 ==>
     qlk (compile_queue conf(q1 ++ q2)) p1 =
     qlk (compile_queue conf q2) p1`,
  recInduct compile_queue_ind
  >> rpt strip_tac
  >> fs[compile_queue_def,qlk_def,fget_def]
  >> rw[FLOOKUP_UPDATE]);

(*
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
*)
val list_trans_par_l = Q.store_thm("list_trans_par_l",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar p r) alpha (NPar q r)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemTheory.trans_par_l])

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemTheory.trans_par_r])

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
      >> match_mp_tac compile_message_preservation_send0 >> simp[compile_state_def])
  >- ((* trans_par_l *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_l)
  >- ((* trans_par_r *)
      first_x_assum drule >> simp[compile_network_def] >> MATCH_ACCEPT_TAC list_trans_par_r));

Theorem compile_message_preservation_enqueue:
  ∀conf d q p1 p2 e s.
    conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
  (NEndpoint p2 (s with queues := q) e)
  (MAP (λm. LReceive p1 m p2) (compile_message conf d))
  (NEndpoint p2
     (s with queues := q |+ (p1, qlk q p1 ++ compile_message conf d)) e)
Proof
  recInduct compile_message_ind
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC [compile_message_def]
  >> simp[]
  >> IF_CASES_TAC
  >- (simp[list_trans_def] >> drule payloadSemTheory.trans_enqueue
      >> disch_then(qspecl_then [`conf`,`s with queues := q`] mp_tac)
      >> simp[qpush_def,SNOC_APPEND])
  >- (fs[list_trans_def,NOT_LESS_EQUAL,pad_not_final]
      >> drule payloadPropsTheory.trans_enqueue'
      >> disch_then (qspecl_then [`conf`,`s`,`pad conf d`,`e`,`q`] assume_tac)
      >> asm_exists_tac >> simp[]
      >> first_x_assum drule
      >> disch_then (qspec_then `qpush q p1 (pad conf d)` assume_tac)
      >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND,qlk_qpush]
      >> full_simp_tac std_ss [qpush_def,FUPDATE_EQ]
      )
QED

Theorem compile_message_preservation_enqueue':
  ∀conf d q p1 p2 e b.
    conf.payload_size > 0
    ∧ p1 ≠ p2
    ==> list_trans conf
  (NEndpoint p2 <|bindings := b; funs := []; queues := q|> e)
  (MAP (λm. LReceive p1 m p2) (compile_message conf d))
  (NEndpoint p2
     <|bindings := b; funs := []; queues := q |+ (p1, qlk q p1 ++ compile_message conf d)|> e)
Proof
  rpt strip_tac >>
  drule_then drule compile_message_preservation_enqueue >>
  disch_then(qspecl_then [‘d’,‘q’,‘e’,‘<|bindings := b; funs := []|>’] mp_tac) >>
  simp[]
QED

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
      simp[compile_network_def,compile_endpoint_def,compile_state_def,compile_queue_SNOC,
           compile_queue_def,compile_message_preservation_enqueue'])
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
  >> imp_res_tac payloadSemTheory.trans_com_l
  >> simp [payloadSemTheory.reduction_def]
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
  >> imp_res_tac payloadSemTheory.trans_com_r
  >> simp [payloadSemTheory.reduction_def]
  >> asm_exists_tac
  >> simp[] >> metis_tac[])

Theorem normalise_queues_FUPDATE_idem[simp]:
  normalise_queues (normalise_queues(q) |+ (p2,d2)) =
  normalise_queues (q|+ (p2,d2))
Proof
  rw[normalise_queues_FUPDATE_NONEMPTY,DRESTRICT_normalise_queues]
QED

Theorem compile_message_preservation_dequeue:
  !conf d ds p1 p2 q1 e s v.
   p1 ≠ p2 /\ conf.payload_size > 0 ∧
   qlk s.queues p1 = compile_message conf d ++ q1
   ==>
   (reduction conf)^*
    (NEndpoint p2
               s
               (Receive p1 v ds e))
    (NEndpoint p2
               (s with <|bindings := s.bindings |+ (v,FLAT(ds) ++ d);
                         queues := normalise_queues(s.queues |+ (p1,q1))|>)
               e)
Proof
  recInduct compile_message_ind
  >> rpt strip_tac
  >> qpat_x_assum ‘qlk _ _ = _’ mp_tac
  >> PURE_ONCE_REWRITE_TAC[compile_message_def]
  >> simp[]
  >> IF_CASES_TAC >> strip_tac
  >- (match_mp_tac RTC_SINGLE
      >> simp[payloadSemTheory.reduction_def]
      >> drule trans_dequeue_last_payload'
      >> fs[]
      >> rpt(disch_then drule) >> simp[SNOC_APPEND,unpad_pad,final_pad_TAKE])
  >- (match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
      >> fs[pad_not_final] >> first_x_assum drule
      >> disch_then(qspecl_then [`ds ++ [TAKE conf.payload_size d]`,
                    `q1`,`e`,`s with queues := normalise_queues(s.queues |+ (p1,compile_message conf (DROP conf.payload_size d) ++ q1))`,`v`] mp_tac)
      >> impl_tac >- simp[]
      >> simp[]
      >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,TAKE_DROP]
      >> strip_tac >> HINT_EXISTS_TAC >> simp[]
      >> simp[payloadSemTheory.reduction_def]
      >> drule trans_dequeue_intermediate_payload'
      >> rpt(disch_then drule)
      >> FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND,
                                                        unpad_pad]
      >> disch_then match_mp_tac
      >> simp[])
QED

Theorem compile_queue_normalised:
  ∀conf q. conf.payload_size > 0 ⇒ normalised(compile_queue conf q)
Proof
  strip_tac >> Induct >-
    (rw[normalised_def,compile_queue_def,normalise_queues_def]) >>
  Cases >> rw[] >>
  fs[compile_queue_def,normalised_def] >>
  simp[normalise_queues_FUPDATE_NONEMPTY] >>
  IF_CASES_TAC >- fs[Once compile_message_def,CaseEq "bool"] >>
  simp[]
QED

Theorem compile_queue_normalise:
  ∀conf q. conf.payload_size > 0 ⇒ normalise_queues(compile_queue conf q) = compile_queue conf q
Proof
  metis_tac[compile_queue_normalised,normalised_def]
QED

Theorem compile_message_nonempty:
  ∀conf q. conf.payload_size > 0 ⇒ compile_message conf q ≠ []
Proof
  rw[Once compile_message_def]
QED

Theorem qlk_compile_queue_MAP_FILTER:
  ∀conf q p.
  qlk(compile_queue conf q) p =
  FLAT(MAP (compile_message conf o SND) (FILTER (λ(p',d). p' = p) q))
Proof
  rpt strip_tac >> Induct_on ‘q’ >>
  fs[qlk_def,compile_queue_def,fget_def,CaseEq"option"] >>
  Cases >> fs[compile_queue_def] >> rw[FLOOKUP_UPDATE] >>
  rw[qlk_def,fget_def]
QED

Theorem compile_queue_midskip_lemma:
  ∀conf p1 q1 d q2.
  conf.payload_size > 0 ∧ EVERY (λ(p,_). p ≠ p1) q1 ⇒
  normalise_queues(compile_queue conf (q1 ++ [(p1,d)] ++ q2) |+ (p1,qlk (compile_queue conf q2) p1)) =
  compile_queue conf (q1 ++ q2)
Proof
  Induct_on ‘q1’ >-
    (rw[compile_queue_def,normalise_queues_FUPDATE_NONEMPTY,DRESTRICT_normalise_queues,compile_queue_normalise] >-
       (‘normalised(compile_queue conf q2)’ by(metis_tac[compile_queue_normalised]) >>
        fs[normalised_def,normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,qlk_def,fget_def,
           CaseEq "option",CaseEq "bool"] >>
        rw[] >> fs[] >>
        first_x_assum(qspec_then ‘p1’ mp_tac) >>
        simp[]) >>
     rw[fmap_eq_flookup,FLOOKUP_UPDATE] >>
     rw[] >>
     fs[qlk_def,fget_def,CaseEq "option"] >>
     TOP_CASE_TAC >> fs[]) >>
  Cases >> rw[compile_queue_def] >> fs[] >> res_tac >>
  simp[FUPDATE_COMMUTES] >>
  simp[Once normalise_queues_FUPDATE_NONEMPTY] >>
  simp[compile_message_nonempty] >>
  simp[qlk_compile_queue_MAP_FILTER,FILTER_APPEND]
QED

Theorem compile_endpoint_dsubst:
  compile_endpoint (dsubst e dn e') =
  dsubst (compile_endpoint e) dn (compile_endpoint e')
Proof
  Induct_on ‘e’ >>
  rw[compile_endpoint_def,endpointLangTheory.dsubst_def,payloadLangTheory.dsubst_def]
QED
        
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
  >> fs[endpointSemTheory.reduction_def,payloadSemTheory.reduction_def]
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> (W(curry Q.SPEC_TAC)) `conf`
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac endpointSemTheory.trans_strongind
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
       simp[compile_network_def,compile_endpoint_def,compile_queue_def,compile_queue_SNOC,
            compile_state_def]
       >> drule compile_message_preservation_dequeue
       >> disch_then drule
       >> disch_then(qspecl_then [‘d’,‘[]’,‘qlk(compile_queue conf q2) p1’,‘compile_endpoint e’,
                                  ‘compile_state conf s’,‘v’] mp_tac)
       >> impl_tac
       >- (simp[compile_state_def] >>
           drule compile_queue_lift_ineq' >>
           SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
           disch_then kall_tac >>
           simp[compile_queue_def])
       >> simp[compile_queue_normalise]
       >> simp[compile_state_def]
       >> simp[compile_message_nonempty]
       >> simp[compile_queue_midskip_lemma])
  >- ((* trans_ext_choice_l *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_ext_choice_r *)
      fs[choice_free_network_def,choice_free_endpoint_def])
  >- ((* trans_if_true *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def,compile_state_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemTheory.reduction_def]
      >> match_mp_tac payloadSemTheory.trans_if_true
      >> simp[])
  >- ((* trans_if_false *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def,compile_state_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemTheory.reduction_def]
      >> match_mp_tac payloadSemTheory.trans_if_false
      >> simp[])
  >- ((* trans_let *)
      fs[compile_network_def,compile_queue_def,compile_endpoint_def,compile_state_def]
      >> match_mp_tac RTC_SUBSET
      >> simp[payloadSemTheory.reduction_def]
      >> `EVERY IS_SOME (MAP (FLOOKUP ((<|bindings := s.bindings; funs := []; queues:=compile_queue conf s.queue|> : closure state).bindings)) vl)`
          by(fs[EVERY_MAP])
      >> drule payloadSemTheory.trans_let >> simp[])
  >- ((* trans_par_l *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_l)
  >- ((* trans_par_r *)
      fs[compile_network_def,choice_free_network_def] >> first_x_assum drule
      >> MATCH_ACCEPT_TAC payloadPropsTheory.reduction_par_r)
  >- ((* trans_fix *)
      fs[compile_network_def,choice_free_network_def,compile_endpoint_dsubst,
         compile_endpoint_def] >>
      match_mp_tac RTC_SUBSET >>
      simp[payloadSemTheory.reduction_def] >>
      rw[Once payloadSemTheory.trans_cases]));

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

Theorem qlk_update_eq:
  qlk (q |+ (p1,x)) p2 = if p1 = p2 then x else qlk q p2
Proof
  rw[]
QED

Theorem compile_queue_split:
  ∀q p1 d q2 conf.
  qlk(compile_queue conf q) p1 = d::q2 /\ conf.payload_size > 0
  ==> ?ds q11 q22. q = q11 ++ [(p1,ds)] ++ q22 /\ LENGTH(compile_message conf ds) > 0 /\
        HD(compile_message conf ds) = d /\ EVERY (λ(p,_). p ≠ p1) q11
Proof
  Induct_on ‘q’ >- (rw[compile_queue_def]) >>
  Cases >>
  rw[compile_queue_def,qlk_update_eq] >-
   (rename1 ‘compile_message _ ds’ >>
    MAP_EVERY qexists_tac [‘ds’,‘[]’] >>
    simp[] >>
    fs[Once compile_message_def] >>
    rw[] >>
    simp[Once compile_message_def] >>
    rw[] >>
    fs[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rename1 ‘(q1,dd)::q’ >>
  MAP_EVERY qexists_tac [‘ds’,‘(q1,dd)::q11’] >>
  simp[]
QED

Theorem compile_network_reflection_single_send:
  ∀p1 p2 conf s d r.
    conf.payload_size > 0
    ∧ trans conf (compile_network conf p1) (LSend s d r) p2
    ==> ∃p3 od ds.
      HD(compile_message conf od) = d /\
      trans p1 (LSend s od r) p3 /\
      list_trans conf p2 (MAP (λd. LSend s d r) (TL(compile_message conf od)))
                 (compile_network conf p3)
Proof
  Induct_on `p1` >> rw[compile_network_def]
  >- (* NNil *)
     fs[payloadSemTheory.reduction_def,trans_nil_false]
  >- (* NPar *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Par-L *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) list_trans_par_l >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_l,reduction_def])
      >- (* Par-R *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) list_trans_par_r >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_r,reduction_def]))
  >- (* NEndpoint *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Send-last-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[] >>
          rename1 `pad _ d` >> rename1 `NEndpoint s s0 (Send p v e)` >>
          qexists_tac `NEndpoint s s0 e` >> qexists_tac `d` >>
          conj_tac >- rw[Once compile_message_def] >>
          conj_tac >- (fs[compile_state_def] >> metis_tac[trans_send]) >>
          fs[compile_state_def] >>
          rw[compile_network_def,Once compile_message_def,list_trans_def,DROP_LENGTH_TOO_LONG,
             compile_state_def] >>
          fs[final_pad_LENGTH])
      >- (* Send-intermediate-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def] >> rveq >> fs[] >>
          rename1 `pad _ d` >> rename1 `NEndpoint s s0 (Send p v e)` >>
          qexists_tac `NEndpoint s s0 e` >> qexists_tac `d` >>
          conj_tac >- rw[Once compile_message_def] >>
          conj_tac >- (fs[compile_state_def] >> metis_tac[trans_send]) >>
          rw[compile_network_def,Once compile_message_def,list_trans_def,DROP_LENGTH_TOO_LONG] >>
          fs[final_pad_LENGTH] >>
          match_mp_tac compile_message_preservation_send >>
          simp[])
     )
QED

Theorem compile_network_reflection_single_receive:
  ∀p1 p2 conf s d r.
    conf.payload_size > 0
    ∧ trans conf (compile_network conf p1) (LReceive s (HD(compile_message conf d)) r) p2
    ==> ∃p3.
      trans p1 (LReceive s d r) p3 /\
      list_trans conf p2 (MAP (λd. LReceive s d r) (TL(compile_message conf d)))
                 (compile_network conf p3)
Proof
  Induct_on `p1` >> rw[compile_network_def]
  >- (* NNil *)
     fs[payloadSemTheory.reduction_def,trans_nil_false]
  >- (* NPar *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Par-L *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) list_trans_par_l >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          metis_tac[trans_par_l])
      >- (* Par-R *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) list_trans_par_r >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          metis_tac[trans_par_r]))
  >- (* NEndpoint *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      rename1 ‘endpointLang$NEndpoint p st’ >>
      qexists_tac `NEndpoint p (st with queue := SNOC (s',d) st.queue) e` >>
      rw[trans_enqueue] >>
      fs[compile_network_def] >>
      rw[Once compile_message_def] >-
        (rw[Once compile_message_def,list_trans_def,compile_state_def] >>
         simp[compile_queue_SNOC,qpush_def |> REWRITE_RULE[SNOC_APPEND]] >>
         rw[Once compile_message_def]) >>
      rw[Once compile_message_def,compile_state_def] >>
      drule_all compile_message_preservation_enqueue >>
      simp[compile_queue_SNOC] >>
      qmatch_goalsub_abbrev_tac `_ with queues := qa` >>
      disch_then(qspecl_then [`DROP conf.payload_size d`,
                              `qa`,`compile_endpoint e`,`<|bindings := st.bindings; funs := []|>`] mp_tac) >>
      fs[] >>
      match_mp_tac(DECIDE “∀x y. x = y ⇒ (x ⇒ y)”) >>
      rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
      rw[Abbr ‘qa’,qpush_def] >>
      rpt AP_TERM_TAC >>
      simp[SimpR ``$=``,Once compile_message_def])
QED

Theorem compile_network_reflection_single:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ reduction conf (compile_network conf p1) p2
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ choice_free_network p1
    ==> ∃p3 p4. (reduction conf)^* p2 p3
             ∧ reduction p1 p4
             ∧ p3 = compile_network conf p4
Proof
  Induct_on `p1` >> rw[compile_network_def]
  >- (* NNil *)
     fs[payloadSemTheory.reduction_def,trans_nil_false]
  >- (* NPar *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Com-L *)
         (drule_all_then strip_assume_tac compile_network_reflection_single_send >>
          rveq >>
          drule_all_then strip_assume_tac compile_network_reflection_single_receive >>
          drule_all_then assume_tac compile_network_preservation_com_l >>
          drule_all_then assume_tac payloadSemTheory.trans_com_l >>
          drule_all_then assume_tac trans_com_l >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >>
          simp[reduction_def])
      >- (* Com-R *)
         (drule_all_then strip_assume_tac compile_network_reflection_single_send >>
          rveq >>
          drule_all_then strip_assume_tac compile_network_reflection_single_receive >>
          drule_all_then assume_tac compile_network_preservation_com_r >>
          drule_all_then assume_tac payloadSemTheory.trans_com_r >>
          drule_all_then assume_tac trans_com_r >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >>
          simp[reduction_def])
      >- (* Par-L *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) reduction_par_l >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_l,reduction_def])
      >- (* Par-R *)
         (fs[endpointPropsTheory.endpoints_def,ALL_DISTINCT_APPEND,choice_free_network_def] >>
          first_x_assum drule_all >> strip_tac >>
          fs[GSYM payloadSemTheory.reduction_def] >>
          rename1 `compile_network conf q` >>
          drule_then (qspec_then `compile_network conf q` assume_tac) reduction_par_r >>
          Q.REFINE_EXISTS_TAC `NPar _ _` >>
          simp[compile_network_def] >>
          asm_exists_tac >> simp[] >>
          metis_tac[trans_par_r,reduction_def]))
  >- (* NEndpoint *)
     (fs[payloadSemTheory.reduction_def] >>
      qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once payloadSemTheory.trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (* Dequeue-last-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          drule_all_then strip_assume_tac compile_queue_split >>
          `compile_message conf ds = [d]`
            by(fs[compile_queue_SNOC,compile_queue_def,Once compile_message_def] >>
               rw[] >> rw[Once compile_message_def] >>
               rfs[] >> fs[]) >>
          fs[compile_queue_SNOC,compile_queue_def] >>
          FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,compile_queue_lift_ineq'] >>
          fs[compile_queue_def] >>
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
          rename1 ‘NEndpoint p’ >>
          rename1 ‘s.bindings’ >>
          qexists_tac `NEndpoint p <|bindings := s.bindings |+ (s', unpad d);
                                     queue := q11 ++ q22|> ec` >>
          simp[compile_network_def,compile_queue_SNOC,reduction_def,compile_state_def] >>
          conj_tac >- simp[compile_queue_midskip_lemma] >>
          match_mp_tac(trans_dequeue |> SIMP_RULE (srw_ss()) []) >>
          rw[])
      >- (* Dequeue-intermediate-payload *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          drule_all_then strip_assume_tac compile_queue_split >>
          rename1 `endpointLang$Receive p v exp` >>
          rename1 ‘NEndpoint q’ >>
          rename1 ‘s.bindings’ >>
          qexists_tac `NEndpoint q <|queue := q11 ++ q22;bindings:=s.bindings |+ (v,ds)|> exp` >>
          reverse conj_asm2_tac >-
            (rw[reduction_def] >>
             match_mp_tac(trans_dequeue |> SIMP_RULE (srw_ss()) []) >>
             rw[]) >>
          simp[] >>
          `compile_message conf ds = d::compile_message conf(DROP conf.payload_size ds)`
            by(fs[compile_queue_SNOC,compile_queue_def,Once compile_message_def] >>
               rw[] >> rw[Once compile_message_def] >>
               rfs[] >> fs[] >> metis_tac[pad_not_final]) >>
          fs[compile_network_def,compile_queue_SNOC,compile_state_def,compile_queue_def] >>
          FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, compile_queue_lift_ineq'] >>
          fs[compile_queue_def] >>
          rveq >>
          simp[normalise_queues_FUPDATE_NONEMPTY,compile_message_nonempty,compile_queue_normalise] >>
          drule_then drule compile_message_preservation_dequeue >>
          qmatch_goalsub_abbrev_tac ‘<|bindings := ba; funs := _; queues := qa|>’ >>
          disch_then(qspecl_then [`DROP conf.payload_size ds`,
                                  `[unpad d]`,`qlk(compile_queue conf q22) p`,
                                  `compile_endpoint exp`,
                                  `<|bindings := ba; funs := []; queues := qa|>`,`v`] mp_tac) >>
          simp[Abbr ‘qa’,Abbr‘ba’] >>
          match_mp_tac(DECIDE “x = y ⇒ (x ⇒ y)”) >>
          rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
          rw[compile_queue_midskip_lemma] >>
          `ds = unpad d ++ DROP conf.payload_size ds` suffices_by metis_tac[] >>
          qpat_x_assum `compile_message _ _ = _` mp_tac >>
          rw[Once compile_message_def]
          >- (fs[Once compile_message_def] >> every_case_tac >> fs[])
          >> fs[unpad_pad])
      >- (* If-L *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          rename1 ‘NEndpoint p’ >>
          rename1 ‘NEndpoint _ s (IfThen _ _ _)’ >>
          qexists_tac `NEndpoint p s e1` >>
          simp[compile_network_def] >>
          simp[reduction_def,compile_state_def] >>
          metis_tac[trans_if_true])
      >- (* If-R *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          rename1 ‘NEndpoint p’ >>
          rename1 ‘NEndpoint _ s (IfThen _ _ _)’ >>
          qexists_tac `NEndpoint p s e1` >>
          simp[compile_network_def] >>
          simp[reduction_def,compile_state_def] >>
          metis_tac[trans_if_false])
      >- (* Let *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          rename1 ‘NEndpoint p’ >>
          rename1 ‘NEndpoint _ s (Let v _ _ _)’ >>
          qexists_tac `NEndpoint p (s with bindings := s.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s.bindings) l))) e1` >>
          simp[compile_network_def] >>
          simp[reduction_def,compile_state_def] >>
          metis_tac[trans_let])
      >- (* Fix *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def] >> rveq >>
          rename1 `compile_endpoint e1` >>
          rename1 ‘NEndpoint p’ >>
          rename1 ‘NEndpoint _ s (Fix dn _)’ >>
          simp[endpointSemTheory.reduction_def,Once endpointSemTheory.trans_cases] >>
          simp[compile_network_def,compile_endpoint_def,compile_endpoint_dsubst,compile_state_def])
      >- (* Letrec *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def])
      >- (* FCall *)
         (Cases_on `e` >> fs[compile_endpoint_def,compile_state_def])
     )
QED

Theorem reduction_list_trans:
  (reduction conf)^* p q = ?n. list_trans conf p (REPLICATE n LTau) q
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (MAP_EVERY qid_spec_tac [`q`,`p`] >>
      ho_match_mp_tac RTC_INDUCT >>
      rw[]
      >- (qexists_tac `0` >> simp[list_trans_def])
      >- (fs[payloadSemTheory.reduction_def] >>
          qexists_tac `SUC n` >>
          simp[list_trans_def] >>
          asm_exists_tac >> simp[]))
  >- (rpt strip_tac >> pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [`q`,`p`,`n`] >>
      Induct >>
      rw[list_trans_def] >>
      fs[GSYM payloadSemTheory.reduction_def] >>
      metis_tac[RTC_RULES])
QED

Theorem compile_network_endpoints:
  MAP FST(endpoints(compile_network conf p1)) = MAP FST (endpoints p1)
Proof
  Induct_on `p1` >>
  rw[payloadLangTheory.endpoints_def,endpointPropsTheory.endpoints_def,
     compile_network_def]
QED

Theorem compile_network_reflection:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ (reduction conf)^* (compile_network conf p1) p2
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ choice_free_network p1
    ==> ∃p3. (reduction conf)^* p2 (compile_network conf p3)
             ∧ reduction^* p1 p3
Proof
  simp[reduction_list_trans,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases
  >- (rw[list_trans_def] >>
      CONV_TAC(RESORT_EXISTS_CONV rev) >>
      qexists_tac `0` >> rw[list_trans_def] >>
      metis_tac[RTC_REFL])
  >- (rw[list_trans_def,GSYM payloadSemTheory.reduction_def] >>
      drule_all(compile_network_reflection_single
                |> REWRITE_RULE[PULL_EXISTS,reduction_list_trans]) >>
      strip_tac >>
      rveq >>
      dxrule payload_confluence_weak_contract >>
      disch_then dxrule >>
      impl_tac
      >- (metis_tac[endpoint_names_trans,payloadSemTheory.reduction_def,
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
      metis_tac[choreoUtilsTheory.RTC_TRANS,list_trans_append,REPLICATE_APPEND])
QED

val _ = export_theory ()

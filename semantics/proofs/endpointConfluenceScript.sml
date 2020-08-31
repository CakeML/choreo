open preamble endpointSemTheory endpointLangTheory endpointPropsTheory;

val _ = new_theory "endpointConfluence";

Theorem endpoint_local_confluence_send:
  ∀p1 alpha p2 p3 s d r.
  trans p1 alpha p2 /\ trans p1 (LSend s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LSend s d r) p4 /\
        trans p3 alpha p4
Proof
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Send *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue *)
      (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
       fs[] >> rveq >> fs[] >> rveq >> fs[]
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send >> simp[] >>
           disch_then dxrule >>
           rename1 `Send _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send >> simp[] >>
           disch_then dxrule >>
           rename1 `Send _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[]))
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          Cases_on `s = p1''` (* TODO: generated names *)
          >- metis_tac[trans_same_sender_determ] >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_par_l,trans_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_l,trans_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          Cases_on `s = p1''` (* TODO: generated names *)
          >- metis_tac[trans_same_sender_determ] >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r]))
  >- (* IntChoice *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[endpoints_def] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 (Send r v e))` >>
      qexists_tac `NEndpoint p2 s1 e` >>
      TRY(conj_tac
          >- (match_mp_tac trans_send >> simp[Abbr `s1`])
          >- metis_tac[trans_enqueue_choice_l]))
  >- (* Enqueue-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[endpoints_def] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 (Send r v e))` >>
      qexists_tac `NEndpoint p2 s1 e` >>
      TRY(conj_tac
          >- (match_mp_tac trans_send >> simp[Abbr `s1`])
          >- metis_tac[trans_enqueue_choice_r]))
  >- (* Com-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_choice_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          disch_then drule >>
          impl_tac >- simp[] >>
          strip_tac >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_l,trans_com_choice_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_r,trans_com_choice_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          metis_tac[trans_par_r,trans_com_choice_l]))
  >- (* Com-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_choice_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule(GEN_ALL trans_distinct_residual) >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          metis_tac[trans_par_l,trans_com_choice_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_r,trans_com_choice_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          metis_tac[trans_par_r,trans_com_choice_r]))
  >- (* Dequeue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* ExtChoice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* ExtChoice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_l])
      >- (metis_tac[trans_par_l,trans_par_r])
      >- (metis_tac[trans_par_l,trans_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_par_r,trans_par_l])
  >- (* Fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
QED

Theorem endpoint_local_confluence_send_rotated:
  ∀p1 alpha p2 p3 s d r.
  trans p1 (LSend s d r) p3 /\ trans p1 alpha p2 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LSend s d r) p4 /\
        trans p3 alpha p4
Proof
  metis_tac[endpoint_local_confluence_send]
QED

Theorem endpoint_local_confluence_int_choice:
  ∀p1 alpha p2 p3 s b r.
  trans p1 alpha p2 /\ trans p1 (LIntChoice s b r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LIntChoice s b r) p4 /\
        trans p3 alpha p4
Proof
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Send *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue *)
      (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
       fs[] >> rveq >> fs[] >> rveq >> fs[]
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           dxrule trans_int_choice >>
           rename1 `IntChoice _ _ e1` >>
           disch_then(qspecl_then [`s1`,`b`,`e1`] assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           dxrule trans_int_choice >> simp[] >>
           rename1 `IntChoice _ _ e1` >>
           disch_then(qspecl_then [`s1`,`b`,`e1`] assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[]))
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then dxrule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_l,trans_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then dxrule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then dxrule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_l,trans_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then dxrule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r]))
  >- (* IntChoice *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[endpoints_def] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 (IntChoice b r e))` >>
      qexists_tac `NEndpoint p2 s1 e` >>
      TRY(conj_tac
          >- (match_mp_tac trans_int_choice >> simp[Abbr `s1`])
          >- metis_tac[trans_enqueue_choice_l]))
  >- (* Enqueue-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[endpoints_def] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 (IntChoice b r e))` >>
      qexists_tac `NEndpoint p2 s1 e` >>
      TRY(conj_tac
          >- (match_mp_tac trans_int_choice >> simp[Abbr `s1`])
          >- metis_tac[trans_enqueue_choice_r]))
  >- (* Com-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_choice_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          Cases_on `p1'' = s` (* TODO: generated names *)
          >- (rveq >>
              imp_res_tac choice_sender_is_endpoint >>
              imp_res_tac choice_receiver_is_endpoint >>
              dxrule_all_then strip_assume_tac trans_same_sender_choice_determ >>
              rveq >> fs[]
             ) >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_l,trans_com_choice_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_r,trans_com_choice_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          metis_tac[trans_par_r,trans_com_choice_l]))
  >- (* Com-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_choice_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_l,trans_com_choice_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          Cases_on `p1'' = s` (* TODO: generated names *)
          >- (rveq >>
              dxrule_all_then strip_assume_tac trans_same_sender_choice_determ >>
              rveq >> fs[]
             ) >>
          dxrule(GEN_ALL trans_distinct_residual) >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          metis_tac[trans_par_r,trans_com_choice_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          Cases_on `p1'' = s` (* TODO: generated names *)
          >- (rveq >>
              dxrule_all_then strip_assume_tac trans_same_sender_choice_determ >>
              rveq >> fs[]
             ) >>
          dxrule trans_distinct_residual >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          impl_tac >- simp[] >>
          strip_tac >>
          metis_tac[trans_par_r,trans_com_choice_r]))
  >- (* Dequeue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* ExtChoice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* ExtChoice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_l])
      >- (metis_tac[trans_par_l,trans_par_r])
      >- (metis_tac[trans_par_l,trans_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_par_r,trans_par_l])
  >- (* Fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
QED

Theorem endpoint_local_confluence_int_choice_rotated:
  ∀p1 alpha p2 p3 s b r.
  trans p1 (LIntChoice s b r) p3 /\ trans p1 alpha p2 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LIntChoice s b r) p4 /\
        trans p3 alpha p4
Proof
  metis_tac[endpoint_local_confluence_int_choice]
QED

Theorem endpoint_local_confluence_receive:
  ∀p1 s1 d1 r1 p2 p3 s2 d2 r2.
  trans p1 (LReceive s1 d1 r1) p2 /\ trans p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LReceive s2 d2 r2) p4 /\
        trans p3 (LReceive s1 d1 r1) p5 /\
        qcong p4 p5
Proof
  `∀p1 alpha p2 s1 d1 r1 p3 s2 d2 r2.
  trans p1 alpha p2 /\ alpha = LReceive s1 d1 r1 /\
  trans p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LReceive s2 d2 r2) p4 /\
        trans p3 (LReceive s1 d1 r1) p5 /\
        qcong p4 p5` suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Enqueue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      dxrule trans_enqueue >> disch_then(qspecl_then [`s1`,`d2`,`e`] mp_tac) >>
      unabbrev_all_tac >> strip_tac >>
      asm_exists_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      qpat_x_assum `_ <> _` mp_tac >>
      dxrule trans_enqueue >> disch_then(qspecl_then [`s1`,`d`,`e`] mp_tac) >>
      unabbrev_all_tac >> rpt strip_tac >>
      asm_exists_tac >> simp[] >>
      simp[SNOC_APPEND] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
      match_mp_tac (qcong_queue_reorder'
                    |> CONV_RULE(RESORT_FORALL_CONV rev)
                    |> Q.SPEC `[]` |> REWRITE_RULE[APPEND_NIL]) >>
      first_x_assum ACCEPT_TAC)
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
QED

Theorem endpoint_local_confluence_receive_choice:
  ∀p1 s1 d r1 p2 p3 s2 b r2.
  trans p1 (LReceive s1 d r1) p2 /\ trans p1 (LExtChoice s2 b r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LExtChoice s2 b r2) p4 /\
        trans p3 (LReceive s1 d r1) p5 /\
        qcong p4 p5
Proof
  `∀p1 alpha p2 s1 d r1 p3 s2 b r2.
  trans p1 alpha p2 /\ alpha = LReceive s1 d r1 /\
  trans p1 (LExtChoice s2 b r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LExtChoice s2 b r2) p4 /\
        trans p3 (LReceive s1 d r1) p5 /\
        qcong p4 p5` suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Enqueue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      TRY((rename1 `[0w]` >> dxrule trans_enqueue_choice_r) ORELSE dxrule trans_enqueue_choice_l >>
          disch_then(qspecl_then [`s1`,`e`] mp_tac) >>
          unabbrev_all_tac >> strip_tac >>
          asm_exists_tac >> simp[] >>
          qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
          qpat_x_assum `_ <> _` mp_tac >>
          dxrule trans_enqueue >> disch_then(qspecl_then [`s1`,`d`,`e`] mp_tac) >>
          unabbrev_all_tac >> rpt strip_tac >>
          asm_exists_tac >> simp[] >>
          simp[SNOC_APPEND] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
          match_mp_tac (qcong_queue_reorder'
                          |> CONV_RULE(RESORT_FORALL_CONV rev)
                          |> Q.SPEC `[]` |> REWRITE_RULE[APPEND_NIL]) >>
          first_x_assum ACCEPT_TAC)
     )
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
QED

Theorem endpoint_local_confluence_choice:
  ∀p1 s1 b1 r1 p2 p3 s2 b2 r2.
  trans p1 (LExtChoice s1 b1 r1) p2 /\ trans p1 (LExtChoice s2 b2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LExtChoice s2 b2 r2) p4 /\
        trans p3 (LExtChoice s1 b1 r1) p5 /\
        qcong p4 p5
Proof
  `∀p1 alpha p2 s1 b1 r1 p3 s2 b2 r2.
  trans p1 alpha p2 /\ alpha = LExtChoice s1 b1 r1 /\
  trans p1 (LExtChoice s2 b2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans p2 (LExtChoice s2 b2 r2) p4 /\
        trans p3 (LExtChoice s1 b1 r1) p5 /\
        qcong p4 p5` suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Enqueue-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      TRY(
       (rename1 `trans _ (_ _ F _) _ /\ trans _ _ _ /\ _` >> dxrule trans_enqueue_choice_r) ORELSE dxrule trans_enqueue_choice_l >>
       disch_then(qspecl_then [`s1`,`e`] mp_tac) >>
       unabbrev_all_tac >> strip_tac >>
       asm_exists_tac >> simp[] >>
       qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
       qpat_x_assum `_ <> _` mp_tac >>
       dxrule trans_enqueue_choice_l >> disch_then(qspecl_then [`s1`,`e`] mp_tac) >>
       unabbrev_all_tac >> rpt strip_tac >>
       asm_exists_tac >> simp[] >>
       simp[SNOC_APPEND] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
       match_mp_tac (qcong_queue_reorder'
                     |> CONV_RULE(RESORT_FORALL_CONV rev)
                     |> Q.SPEC `[]` |> REWRITE_RULE[APPEND_NIL]) >>
       first_x_assum ACCEPT_TAC))
  >- (* Enqueue-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      TRY(
       (rename1 `trans _ (_ _ F _) _ /\ trans _ _ _ /\ _` >> dxrule trans_enqueue_choice_r) ORELSE dxrule trans_enqueue_choice_l >>
       disch_then(qspecl_then [`s1`,`e`] mp_tac) >>
       unabbrev_all_tac >> strip_tac >>
       asm_exists_tac >> simp[] >>
       qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
       qpat_x_assum `_ <> _` mp_tac >>
       dxrule trans_enqueue_choice_r >> disch_then(qspecl_then [`s1`,`e`] mp_tac) >>
       unabbrev_all_tac >> rpt strip_tac >>
       asm_exists_tac >> simp[] >>
       simp[SNOC_APPEND] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
       match_mp_tac (qcong_queue_reorder'
                     |> CONV_RULE(RESORT_FORALL_CONV rev)
                     |> Q.SPEC `[]` |> REWRITE_RULE[APPEND_NIL]) >>
       first_x_assum ACCEPT_TAC))
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]
     )
QED

Theorem endpoint_local_confluence_tau_receive:
  ∀p1 p2 p3 s d r.
  trans p1 LTau p2 /\ trans p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LReceive s d r) p4 /\
        trans p3 LTau p5 /\
        qcong p4 p5
Proof
  `∀p1 alpha p2 p3 s d r.
  trans p1 alpha p2 /\ alpha = LTau /\ trans p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LReceive s d r) p4 /\
        trans p3 LTau p5 /\
        qcong p4 p5` suffices_by metis_tac[]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >> metis_tac[sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[trans_distinct_residual,label_rel_def,
                       receive_ext_choice_rel_def,sender_is_endpoint,
                       receiver_is_endpoint,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_refl,qcong_sym,qcong_par]
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule endpoint_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule endpoint_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_refl,qcong_sym,qcong_par]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule endpoint_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule endpoint_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       label_rel_def,receive_ext_choice_rel_def,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_refl,qcong_sym,qcong_par]))
  >- (* Com-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_int_choice >> disch_then drule >>
          impl_tac >-
            (simp[] >> metis_tac[choice_sender_is_endpoint,choice_receiver_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_int_choice >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[trans_distinct_residual,label_rel_def,
                       receive_ext_choice_rel_def,choice_sender_is_endpoint,
                       choice_receiver_is_endpoint,
                       receiver_is_endpoint,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_refl,qcong_sym,qcong_par]
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_receive_choice >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_receive_choice >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_refl,qcong_sym,qcong_par]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_receive_choice >>
          disch_then dxrule >>
          impl_tac >- metis_tac[choice_sender_is_endpoint] >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          dxrule endpoint_local_confluence_receive_choice >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_int_choice >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       choice_receiver_is_endpoint,choice_sender_is_endpoint,
                       label_rel_def,receive_ext_choice_rel_def,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule endpoint_local_confluence_int_choice >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       choice_sender_is_endpoint,choice_receiver_is_endpoint,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_refl,qcong_sym,qcong_par]))
  >- (* Dequeue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 e) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`e`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      qunabbrev_tac `a1` >>
      simp[SNOC_APPEND] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      match_mp_tac(trans_dequeue'
                   |> REWRITE_RULE[SNOC_APPEND,FLAT_APPEND,FLAT,APPEND_NIL]) >>
      simp[])
  >- (* ExtChoice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      qunabbrev_tac `a1` >>
      simp[SNOC_APPEND] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      match_mp_tac(trans_ext_choice_l'
                   |> REWRITE_RULE[SNOC_APPEND,FLAT_APPEND,FLAT,APPEND_NIL]) >>
      simp[]
     )
  >- (* ExtChoice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 e2) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`e2`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      qunabbrev_tac `a1` >>
      simp[SNOC_APPEND] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      match_mp_tac(trans_ext_choice_r'
                   |> REWRITE_RULE[SNOC_APPEND,FLAT_APPEND,FLAT,APPEND_NIL]) >>
      simp[]
     )
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      unabbrev_all_tac >>
      match_mp_tac trans_if_true >>
      simp[]
     )
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      unabbrev_all_tac >>
      match_mp_tac trans_if_false >>
      simp[]
     )
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      unabbrev_all_tac >>
      simp[] >>
      match_mp_tac trans_let' >>
      simp[]
     )
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[qcong_refl,qcong_par,trans_par_l])
      >- (metis_tac[trans_par_l,trans_par_r,qcong_par,qcong_refl])
      >- (metis_tac[trans_par_l,trans_par_r,qcong_par,qcong_refl]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r,qcong_par,qcong_refl] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[qcong_refl,qcong_par,trans_par_r,trans_par_l])
  >- (* Fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[qcong_refl,trans_enqueue,trans_fix])
QED

Theorem endpoint_local_confluence_tau_choice:
  ∀p1 p2 p3 s b r.
  trans p1 LTau p2 /\ trans p1 (LExtChoice s b r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 (LExtChoice s b r) p4 /\
        trans p3 LTau p5 /\
        qcong p4 p5
Proof
 Cases_on `b` >>
 metis_tac[endpoint_local_confluence_tau_receive,trans_ext_choice_T_receive,
           trans_ext_choice_F_receive]
QED

Theorem endpoint_local_confluence_tau:
  ∀p1 p2 p3.
  trans p1 LTau p2 /\ trans p1 LTau p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1))
  ==>
  ?p4 p5. trans p2 LTau p4 /\
        trans p3 LTau p5 /\
        qcong p4 p5
Proof
  `∀p1 alpha p2.
    trans p1 alpha p2 ==> !p3. alpha = LTau /\ trans p1 LTau p3 /\ p2 <> p3 /\
    ALL_DISTINCT (MAP FST (endpoints p1))
    ==>
    ?p4 p5. trans p2 LTau p4 /\
            trans p3 LTau p5 /\
            qcong p4 p5` suffices_by metis_tac[]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_same_sender_determ >>
             rveq >> fs[]) >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive >>
          metis_tac[trans_com_l,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_same_sender_determ >>
             rveq >> fs[] >> metis_tac[trans_same_receiver_determ]) >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          first_x_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive >>
          metis_tac[trans_com_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >>
          strip_tac >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >>
          strip_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule_all endpoint_local_confluence_receive_choice >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          metis_tac[trans_com_l,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule_all endpoint_local_confluence_receive_choice >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >>
                       conj_tac >-
                        (match_mp_tac trans_distinct_residual >>
                         asm_exists_tac >> rw[] >> asm_exists_tac >>
                         rw[label_rel_def,receive_ext_choice_rel_def]) >>
                       metis_tac[]) >>
          metis_tac[trans_com_l,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- simp[] >>
          metis_tac[trans_com_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- simp[] >>
          metis_tac[trans_com_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >>
          strip_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >>
          strip_tac >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule(GEN_ALL trans_same_sender_determ) >>
             disch_then dxrule >> impl_tac >- fs[] >>
             strip_tac >>
             rveq >> fs[] >> metis_tac[trans_same_receiver_determ]) >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive >>
          metis_tac[trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule(GEN_ALL trans_same_sender_determ) >>
             disch_then dxrule >> impl_tac >- fs[] >>
             strip_tac >>
             rveq >> fs[] >> metis_tac[trans_same_receiver_determ]) >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive >>
          metis_tac[trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- (simp[] >> metis_tac[]) >>
          metis_tac[trans_com_r,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- (simp[] >> metis_tac[]) >>
          metis_tac[trans_com_r,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule_all endpoint_local_confluence_receive_choice >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >>
                       match_mp_tac trans_distinct_residual >>
                       asm_exists_tac >> rw[] >> asm_exists_tac >>
                       rw[label_rel_def,receive_ext_choice_rel_def]) >>
          metis_tac[trans_com_r,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule(GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule_all endpoint_local_confluence_receive_choice >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          metis_tac[trans_com_r,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule endpoint_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
  >- (* Com-Choice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _)` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          drule (GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive_choice >>
          metis_tac[trans_com_l,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _)` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          drule (GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qpat_x_assum `trans _ (LSend _ _ _) _` assume_tac >>
          drule trans_distinct_residual >>
          qpat_x_assum `trans _ (LIntChoice _ _ _) _` assume_tac >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          dxrule (GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive_choice >>
          metis_tac[trans_com_l,trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule trans_distinct_residual >>
          qpat_x_assum `trans _ (LExtChoice _ _ _) _` assume_tac >>
          disch_then drule >>
          impl_tac >- (simp[label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          dxrule_then assume_tac endpoint_local_confluence_send >>
          pop_assum drule >>
          impl_tac >- simp[] >>
          strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s1 _ _) _` >>
          qpat_x_assum `trans _ (LIntChoice s1 _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _) _` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          strip_tac >>
          Cases_on `s1 = s2` >-
            (rveq >>
             drule_then assume_tac (GEN_ALL trans_same_sender_choice_determ) >>
             qhdtm_x_assum `trans` mp_tac >>
             pop_assum dxrule >> disch_then drule >>
             strip_tac >> rveq >>
             fs[]
            ) >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >-
            (simp[] >> metis_tac[]
            ) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_choice >>
          metis_tac[trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s1 _ _) _` >>
          qpat_x_assum `trans _ (LIntChoice s1 _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _) _` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          strip_tac >>
          Cases_on `s1 = s2` >-
            (rveq >>
             drule_then assume_tac (GEN_ALL trans_same_sender_choice_determ) >>
             qhdtm_x_assum `trans` mp_tac >>
             pop_assum dxrule >> disch_then drule >>
             strip_tac >> rveq >>
             fs[] >> metis_tac[trans_same_receiver_choice_determ]
            ) >>
          drule_then strip_assume_tac trans_distinct_residual >>
          qpat_x_assum `trans _ (LIntChoice _ _ _) _` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          ntac 2 strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >-
            (simp[] >> metis_tac[]
            ) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_choice >>
          metis_tac[trans_com_choice_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- metis_tac[] >>
          metis_tac[trans_com_choice_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- metis_tac[] >>
          metis_tac[trans_com_choice_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_int_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_int_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
  >- (* Com-Choice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_com_l,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac (GEN_ALL trans_distinct_residual) >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_com_l,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _)` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          drule (GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qpat_x_assum `trans _ (LSend _ _ _) _` assume_tac >>
          drule trans_distinct_residual >>
          qpat_x_assum `trans _ (LIntChoice _ _ _) _` assume_tac >>
          disch_then drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          dxrule (GEN_ALL endpoint_local_confluence_send_rotated) >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive_choice >>
          metis_tac[trans_com_choice_r,trans_com_r,qcong_par,qcong_sym,qcong_refl])
      >- (qmatch_asmsub_abbrev_tac `trans _ (LSend s1 _ _)` >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _)` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          drule (GEN_ALL trans_send_choice_distinct_senders) >>
          rpt(disch_then drule) >> strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_send_rotated >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_receive_choice >>
          metis_tac[trans_com_r,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- metis_tac[] >>
          metis_tac[trans_com_choice_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          strip_tac >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then dxrule >> impl_tac >- metis_tac[] >>
          dxrule(GEN_ALL endpoint_local_confluence_int_choice_rotated) >>
          disch_then drule >> impl_tac >- metis_tac[] >>
          metis_tac[trans_com_choice_l,trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s1 _ _) _` >>
          qpat_x_assum `trans _ (LIntChoice s1 _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _) _` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          strip_tac >>
          Cases_on `s1 = s2` >-
            (rveq >>
             drule_then assume_tac (GEN_ALL trans_same_sender_choice_determ) >>
             qhdtm_x_assum `trans` mp_tac >>
             pop_assum dxrule >> disch_then drule >>
             strip_tac >> rveq >>
             fs[] >> metis_tac[trans_same_receiver_choice_determ]
            ) >>
          drule_then strip_assume_tac trans_distinct_residual >>
          qpat_x_assum `trans _ (LIntChoice _ _ _) _` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          ntac 2 strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >-
            (simp[] >> metis_tac[]
            ) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_choice >>
          metis_tac[trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s1 _ _) _` >>
          qpat_x_assum `trans _ (LIntChoice s1 _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ (LIntChoice s2 _ _) _` >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          strip_tac >>
          Cases_on `s1 = s2` >-
            (rveq >>
             drule_then assume_tac (GEN_ALL trans_same_sender_choice_determ) >>
             qhdtm_x_assum `trans` mp_tac >>
             pop_assum dxrule >> disch_then drule >>
             strip_tac >> rveq >>
             fs[] >> metis_tac[trans_same_receiver_choice_determ]
            ) >>
          drule_then strip_assume_tac trans_distinct_residual >>
          qpat_x_assum `trans _ (LIntChoice _ _ _) _` mp_tac >>
          pop_assum drule >>
          impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          ntac 2 strip_tac >>
          dxrule endpoint_local_confluence_int_choice_rotated >>
          disch_then dxrule >>
          impl_tac >-
            (simp[] >> metis_tac[]
            ) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac endpoint_local_confluence_choice >>
          metis_tac[trans_com_choice_r,qcong_par,qcong_sym,qcong_refl])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_tau_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[label_rel_def,receive_ext_choice_rel_def] >>
          rpt strip_tac >>
          dxrule endpoint_local_confluence_int_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_par,qcong_refl,qcong_sym])
      >- (imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          dxrule endpoint_local_confluence_int_choice >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
  >- (* Dequeue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[])
  >- (* ExtChoice-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[])
  >- (* ExtChoice-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[])
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- metis_tac[receiver_is_endpoint] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_int_choice >>
          disch_then drule >>
          impl_tac >- metis_tac[choice_receiver_is_endpoint] >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_int_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           choice_sender_is_endpoint,choice_receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_r,trans_par_l,qcong_par,qcong_refl]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac choice_sender_is_endpoint >>
          imp_res_tac choice_receiver_is_endpoint >>
          drule endpoint_local_confluence_tau_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def]) >>
          strip_tac >>
          metis_tac[trans_com_choice_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_int_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           choice_sender_is_endpoint,choice_receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ LTau _` assume_tac >>
          drule endpoint_local_confluence_int_choice >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           label_rel_def,receive_ext_choice_rel_def,
                                           choice_sender_is_endpoint,choice_receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_choice_r,trans_par_r,qcong_par,qcong_refl])
      >- (dxrule_then (qspec_then `p2` assume_tac) trans_par_l >>
          asm_exists_tac >> simp[] >> pop_assum kall_tac >>
          rename1 `NPar q` >>
          dxrule_then (qspec_then `q` assume_tac) trans_par_r >>
          asm_exists_tac >> simp[qcong_refl])
      >- (dxrule_then (qspec_then `p2` assume_tac) trans_par_l >>
          asm_exists_tac >> simp[] >> pop_assum kall_tac >>
          rename1 `NPar q` >>
          dxrule_then (qspec_then `q` assume_tac) trans_par_r >>
          asm_exists_tac >> simp[qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          imp_res_tac trans_par_r >>
          rpt(first_x_assum(qspec_then `n1` assume_tac)) >>
          ntac 2 (asm_exists_tac >> simp[]) >>
          metis_tac[qcong_rules]))
  >- (* Fix *)
   (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
    fs[] >> rveq >> fs[] >> rveq >> fs[] >>
    metis_tac[qcong_refl,trans_enqueue,trans_fix])
QED

(* TODO: move? *)
Theorem REPLICATE_SUC_SNOC:
  REPLICATE (SUC m) e = REPLICATE m e ++ [e]
Proof
  simp[REPLICATE_GENLIST] >>
  match_mp_tac LIST_EQ >>
  rw[EL_CONS_IF] >>
  rw[EL_APPEND_EQN] >>
  `x - m = 0` by intLib.COOPER_TAC >>
  simp[]
QED

Theorem endpoint_confluence_contract:
  ∀m p1 p2 p3.
   trans p1 LTau p2 /\
   list_trans p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1))
   ==>
   (?n p4. list_trans p2 (REPLICATE n LTau) p4 /\
        n <= m /\
        qcong p3 p4) \/
   (?n p4 p5. list_trans p2 (REPLICATE n LTau) p4 /\
        trans p3 LTau p5 /\
        n <= m /\
        qcong p4 p5)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_def] >> rveq >>
      disj2_tac >> asm_exists_tac >> simp[qcong_refl])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_append,list_trans_def]
  >> first_x_assum drule_all
  >> strip_tac
  >- (drule qcong_trans_pres >>
      disch_then drule >> strip_tac >>
      `list_trans p2 (REPLICATE (SUC n) LTau) q2`
        by(PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
           rw[list_trans_append,list_trans_def] >>
           metis_tac[]) >>
      disj1_tac >>
      asm_exists_tac >> simp[])
  >- (Cases_on `p3 = p5`
      >- (rveq >>
          disj1_tac >> asm_exists_tac >>
          simp[qcong_sym]) >>
      disj2_tac >>
      imp_res_tac endpoint_names_trans >>
      imp_res_tac endpoint_names_list_trans >>
      dxrule endpoint_local_confluence_tau >>
      disch_then dxrule >>
      impl_tac >- simp[] >>
      strip_tac >>
      qhdtm_x_assum `qcong` mp_tac >>
      drule_all(qcong_trans_pres |> PURE_ONCE_REWRITE_RULE [qcong_sym_eq]) >>
      rpt strip_tac >>
      `list_trans p2 (REPLICATE (SUC n) LTau) q2`
        by(PURE_ONCE_REWRITE_TAC [REPLICATE_SUC_SNOC] >>
           rw[list_trans_def,list_trans_append] >> metis_tac[]) >>
      asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      metis_tac[qcong_trans])
QED

Theorem endpoint_confluence_weak_contract:
  ∀n m p1 p2 p3.
   list_trans p1 (REPLICATE n LTau) p2 /\
   list_trans p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1))
   ==>
   (?n' m' p4 p5. list_trans p2 (REPLICATE n' LTau) p4 /\
        list_trans p3 (REPLICATE m' LTau) p5 /\
        n' <= m /\ m' <= n /\
        qcong p4 p5)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_def] >> rveq >>
      asm_exists_tac >> simp[qcong_refl])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_append,list_trans_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> drule endpoint_confluence_contract
  >> disch_then drule
  >> impl_tac
  >- (imp_res_tac endpoint_names_trans >>
      imp_res_tac endpoint_names_list_trans >>
      fs[])
  >> strip_tac
  >- (asm_exists_tac >> simp[] >> asm_exists_tac >> simp[] >> metis_tac[qcong_rules])
  >> qhdtm_x_assum `qcong` mp_tac
  >> drule qcong_trans_pres
  >> disch_then drule
  >> strip_tac
  >> `list_trans p3 (REPLICATE (SUC m') LTau) q2` (* TODO: (mild) generated names *)
        by(PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
           rw[list_trans_append,list_trans_def] >>
           metis_tac[])
  >> strip_tac
  >> asm_exists_tac >> simp[]
  >> asm_exists_tac >> simp[]
  >> metis_tac[qcong_rules]
QED

val _ = export_theory();

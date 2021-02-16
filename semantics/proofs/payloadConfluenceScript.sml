open preamble payloadSemTheory payloadLangTheory payloadPropsTheory;

val _ = new_theory "payloadConfluence";

Theorem payload_local_confluence_send:
  ∀conf p1 alpha p2 p3 s d r.
  trans conf p1 alpha p2 /\ trans conf p1 (LSend s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans conf p2 (LSend s d r) p4 /\
        trans conf p3 alpha p4
Proof
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Send-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Send-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue *)
      (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
       fs[] >> rveq >> fs[] >> rveq >> fs[]
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send_last_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send_intermediate_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[]))
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          Cases_on `s = p1''` (* TODO: generated names *)
          >- metis_tac[trans_same_sender_determ] >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_par_l,trans_com_l])
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
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Dequeue-intermediate-payload *)
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
      >- (metis_tac[trans_par_l,trans_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_par_r,trans_par_l])
  >- (* trans_fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* trans_letrec *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* trans_call *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
QED

Theorem qpush_commute:
  p1 ≠ p2 ⇒ qpush (qpush q p1 d1) p2 d2 = qpush (qpush q p2 d2) p1 d1
Proof
  rw[qpush_def,qlk_def,fget_def,fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[]
QED

Theorem payload_local_confluence_receive:
  ∀conf p1 s1 d1 r1 p2 p3 s2 d2 r2.
  trans conf p1 (LReceive s1 d1 r1) p2 /\ trans conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4. trans conf p2 (LReceive s2 d2 r2) p4 /\
        trans conf p3 (LReceive s1 d1 r1) p4
Proof
  `∀conf p1 alpha p2 s1 d1 r1 p3 s2 d2 r2.
  trans conf p1 alpha p2 /\ alpha = LReceive s1 d1 r1 /\
  trans conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4. trans conf p2 (LReceive s2 d2 r2) p4 /\
        trans conf p3 (LReceive s1 d1 r1) p4` suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Enqueue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      dxrule trans_enqueue >> disch_then(qspecl_then [`conf`,`s1`,`d2`,`e`] mp_tac) >>
      unabbrev_all_tac >> strip_tac >>
      asm_exists_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      qpat_x_assum `_ <> _` mp_tac >>
      dxrule trans_enqueue >> disch_then(qspecl_then [`conf`,`s1`,`d`,`e`] mp_tac) >>
      unabbrev_all_tac >> rpt strip_tac >>
      simp[] >> fs[qpush_commute])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r])
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r])
QED

Theorem payload_local_confluence_tau_receive:
  ∀conf p1 p2 p3 s d r.
  trans conf p1 LTau p2 /\ trans conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans conf p2 (LReceive s d r) p4 /\
        trans conf p3 LTau p4
Proof
  `∀conf p1 alpha p2 p3 s d r.
  trans conf p1 alpha p2 /\ alpha = LTau /\ trans conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans conf p2 (LReceive s d r) p4 /\
        trans conf p3 LTau p4` suffices_by metis_tac[]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[trans_distinct_residual,sender_is_endpoint,
                       receiver_is_endpoint,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule payload_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule payload_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      fs[endpoints_def] >>
      rename1 ‘qpush _ p3 d2’ >>
      (Cases_on ‘p1 = p3’ >-
         (dep_rewrite.DEP_REWRITE_TAC[trans_dequeue_last_payload'] >>
          fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND,
             normalise_queues_FUPDATE_NONEMPTY] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT]
         ) >>
       dep_rewrite.DEP_REWRITE_TAC[trans_dequeue_last_payload'] >>
       fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
       fs[FUPDATE_COMMUTES] >>
       rw[normalise_queues_FUPDATE_NONEMPTY]
      ))
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      rename1 ‘qpush _ p3 d2’ >>
      (Cases_on ‘p1 = p3’ >-
         (dep_rewrite.DEP_REWRITE_TAC[trans_dequeue_intermediate_payload'] >>
          fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT] >>
          fs[FLOOKUP_normalise_queues_FUPDATE] >> rw[]
          ) >>
       dep_rewrite.DEP_REWRITE_TAC[trans_dequeue_intermediate_payload'] >>
       fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
       fs[FUPDATE_COMMUTES] >> rw[normalise_queues_FUPDATE_NONEMPTY] >>
       rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT] >>
       fs[FLOOKUP_normalise_queues] >> every_case_tac >> fs[])
     )
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      match_mp_tac trans_if_true >>
      simp[])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      match_mp_tac trans_if_false >>
      simp[])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      simp[] >>
      match_mp_tac trans_let'' >> simp[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_l])
      >- (metis_tac[trans_par_l,trans_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_par_r,trans_par_l])
  >- (* Fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      metis_tac[trans_fix,trans_enqueue])
  >- (* Letrec *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_cases] >>
      fs[PULL_EXISTS])
  >- (* Call *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_cases] >>
      fs[PULL_EXISTS])
QED

Theorem payload_local_confluence_tau:
  ∀conf p1 p2 p3.
  trans conf p1 LTau p2 /\ trans conf p1 LTau p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans conf p2 LTau p4 /\
        trans conf p3 LTau p4
Proof
  `∀conf p1 alpha p2.
    trans conf p1 alpha p2 ==> !p3. alpha = LTau /\ trans conf p1 LTau p3 /\ p2 <> p3 /\
    ALL_DISTINCT (MAP FST (endpoints p1)) /\ conf.payload_size > 0
    ==>
    ?p4. trans conf p2 LTau p4 /\
            trans conf p3 LTau p4` suffices_by metis_tac[]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (qmatch_asmsub_abbrev_tac `trans _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ _ (LSend s2 _ _)` >>
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
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          first_x_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive >>
          metis_tac[trans_com_l])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac trans_send_receive_distinct >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac []) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac trans_send_receive_distinct >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r])
      >- (qmatch_asmsub_abbrev_tac `trans _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans _ _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_same_sender_determ >>
             rveq >> fs[] >>
             dxrule_all trans_same_receiver_determ >> simp[]
            ) >>
          drule_then assume_tac (GEN_ALL trans_different_sender) >>
          pop_assum(qspec_then `s2` mp_tac) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive >>
          metis_tac[trans_com_r])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule_then assume_tac trans_distinct_residual >>
          qhdtm_x_assum `trans` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[] >>
      imp_res_tac intermediate_final_IMP)
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[] >>
      imp_res_tac intermediate_final_IMP)
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
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_par_r,trans_par_l]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r])
      >- (dxrule_then (qspec_then `p2` assume_tac) trans_par_l >>
          asm_exists_tac >> simp[] >> pop_assum kall_tac >>
          rename1 `NPar q` >>
          dxrule_then (qspec_then `q` assume_tac) trans_par_r >>
          asm_exists_tac >> simp[])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          imp_res_tac trans_par_r >>
          rpt(first_x_assum(qspec_then `n1` assume_tac)) >>
          ntac 2 (asm_exists_tac >> simp[]) >>
          metis_tac[]))
  >- (* Fix *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_cases] >>
      fs[PULL_EXISTS])
  >- (* Letrec *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_cases] >>
      fs[PULL_EXISTS])
  >- (* Call *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_cases] >>
      fs[PULL_EXISTS])
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

Theorem payload_confluence_contract:
  ∀m conf p1 p2 p3.
   trans conf p1 LTau p2 /\
   list_trans conf p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1)) /\
   conf.payload_size > 0
   ==>
   (?n. list_trans conf p2 (REPLICATE n LTau) p3 /\
        n <= m) \/
   (?n p4. list_trans conf p2 (REPLICATE n LTau) p4 /\
        trans conf p3 LTau p4 /\
        n <= m)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_def] >> rveq >>
      disj2_tac >> asm_exists_tac >> simp[])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_append,list_trans_def]
  >> first_x_assum drule_all
  >> strip_tac
  >- (disj1_tac >>
      qexists_tac ‘SUC n’ >>
      PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
      rw[list_trans_append,list_trans_def] >>
      metis_tac[])
  >- (Cases_on `p3 = p4`
      >- (rveq >>
          disj1_tac >> asm_exists_tac >>
          simp[]) >>
      disj2_tac >>
      imp_res_tac endpoint_names_trans >>
      imp_res_tac endpoint_names_list_trans >>
      dxrule payload_local_confluence_tau >>
      disch_then dxrule >>
      impl_tac >- simp[] >>
      strip_tac >>
      qexists_tac ‘SUC n’ >>
      PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
      rw[list_trans_append,list_trans_def] >>
      metis_tac[])
QED

Theorem payload_confluence_weak_contract:
  ∀n m conf p1 p2 p3.
   list_trans conf p1 (REPLICATE n LTau) p2 /\
   list_trans conf p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1)) /\
   conf.payload_size > 0
   ==>
   (?n' m' p4. list_trans conf p2 (REPLICATE n' LTau) p4 /\
        list_trans conf p3 (REPLICATE m' LTau) p4 /\
        n' <= m /\ m' <= n)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_def] >> rveq >>
      asm_exists_tac >> simp[])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_append,list_trans_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> drule payload_confluence_contract
  >> disch_then drule
  >> impl_tac
  >- (imp_res_tac endpoint_names_trans >>
      imp_res_tac endpoint_names_list_trans >>
      fs[])
  >> strip_tac
  >- (asm_exists_tac >> simp[] >> asm_exists_tac >> simp[] >> metis_tac[])
  >> goal_assum drule >> simp[]
  >> qexists_tac ‘SUC m'’
  >> PURE_REWRITE_TAC[REPLICATE_SUC_SNOC]
  >> rw[list_trans_append,list_trans_def]
  >> metis_tac[]
QED

Theorem payload_confluence:
  ∀conf p1 p2 p3.
   (reduction conf)^* p1 p2 /\
   (reduction conf)^* p1 p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1)) /\
   conf.payload_size > 0
   ==>
   (∃p4. (reduction conf)^* p2 p4 /\
         (reduction conf)^* p3 p4)
Proof
  rw[reduction_list_trans] >>
  metis_tac[payload_confluence_weak_contract]
QED

val _ = export_theory();

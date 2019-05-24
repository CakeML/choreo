open preamble payloadSemanticsTheory payloadLangTheory payloadPropsTheory;

val _ = new_theory "payloadConfluence";

(* TODO: conclusion can probably be weakend from qcong to syntactic equality *)
Theorem payload_local_confluence_send:
  ∀conf p1 alpha p2 p3 s d r.
  trans conf p1 alpha p2 /\ trans conf p1 (LSend s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans conf p2 (LSend s d r) p4 /\
        trans conf p3 alpha p5 /\
        qcong p4 p5
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
           metis_tac[qcong_refl])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send_last_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>           
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[qcong_refl])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_send_intermediate_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>           
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_enqueue >>
           metis_tac[qcong_refl]))
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_l,qcong_par,qcong_refl,trans_par_l])
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
          strip_tac >> metis_tac[trans_par_l,trans_com_l,qcong_refl,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l,qcong_refl,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_l,qcong_refl,qcong_par]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_com_r,qcong_par,qcong_refl,trans_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_l,trans_com_r,qcong_refl,qcong_par])      
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
          strip_tac >> metis_tac[trans_par_r,trans_com_r,qcong_refl,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          impl_tac >- metis_tac[trans_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_par_r,trans_com_r,qcong_refl,qcong_par]))
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
          metis_tac[qcong_refl,qcong_par,trans_par_l])
      >- (metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par])
      >- (metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[qcong_refl,qcong_par,trans_par_r,trans_par_l])
QED

Theorem payload_local_confluence_receive:
  ∀conf p1 s1 d1 r1 p2 p3 s2 d2 r2.
  trans conf p1 (LReceive s1 d1 r1) p2 /\ trans conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans conf p2 (LReceive s2 d2 r2) p4 /\
        trans conf p3 (LReceive s1 d1 r1) p5 /\
        qcong p4 p5
Proof
  `∀conf p1 alpha p2 s1 d1 r1 p3 s2 d2 r2.
  trans conf p1 alpha p2 /\ alpha = LReceive s1 d1 r1 /\
  trans conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4 p5. trans conf p2 (LReceive s2 d2 r2) p4 /\
        trans conf p3 (LReceive s1 d1 r1) p5 /\
        qcong p4 p5` suffices_by metis_tac[] >>
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
      asm_exists_tac >> simp[] >>
      simp[SNOC_APPEND] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
      match_mp_tac (qcong_queue_reorder'
                    |> CONV_RULE(RESORT_FORALL_CONV rev)
                    |> Q.SPEC `[]` |> REWRITE_RULE[APPEND_NIL]) >>
      first_x_assum ACCEPT_TAC)
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par])
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par])
QED

Theorem payload_local_confluence_tau_receive:
  ∀conf p1 p2 p3 s d r.
  trans conf p1 LTau p2 /\ trans conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans conf p2 (LReceive s d r) p4 /\
        trans conf p3 LTau p5 /\
        qcong p4 p5
Proof
  `∀conf p1 alpha p2 p3 s d r.
  trans conf p1 alpha p2 /\ alpha = LTau /\ trans conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans conf p2 (LReceive s d r) p4 /\
        trans conf p3 LTau p5 /\
        qcong p4 p5` suffices_by metis_tac[]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >> metis_tac[sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[trans_distinct_residual,sender_is_endpoint,
                       receiver_is_endpoint,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_refl,qcong_sym,qcong_par]
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule payload_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule payload_local_confluence_receive >>
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
          dxrule payload_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint >>
          imp_res_tac sender_is_endpoint >>
          dxrule payload_local_confluence_receive >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_refl,qcong_sym,qcong_par])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint,receiver_is_endpoint,trans_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_refl,qcong_sym,qcong_par]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      qunabbrev_tac `a1` >>
      simp[SNOC_APPEND] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      match_mp_tac(trans_dequeue_last_payload'
                   |> REWRITE_RULE[SNOC_APPEND,FLAT_APPEND,FLAT,APPEND_NIL]) >>
      simp[])
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `qcong a1` >>
      qexists_tac `a1` >>
      simp[qcong_refl] >>
      qunabbrev_tac `a1` >>
      simp[SNOC_APPEND] >>
      PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      match_mp_tac(trans_dequeue_intermediate_payload'
                   |> REWRITE_RULE[SNOC_APPEND,FLAT_APPEND,FLAT,APPEND_NIL]) >>
      simp[]
     )
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
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
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
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
      qmatch_goalsub_abbrev_tac `trans _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
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
      >- (metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par])
      >- (metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_par_l,trans_par_r,qcong_refl,qcong_par] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[qcong_refl,qcong_par,trans_par_r,trans_par_l])
QED

Theorem payload_local_confluence_tau:
  ∀conf p1 p2 p3.
  trans conf p1 LTau p2 /\ trans conf p1 LTau p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans conf p2 LTau p4 /\
        trans conf p3 LTau p5 /\
        qcong p4 p5
Proof
  `∀conf p1 alpha p2.
    trans conf p1 alpha p2 ==> !p3. alpha = LTau /\ trans conf p1 LTau p3 /\ p2 <> p3 /\
    ALL_DISTINCT (MAP FST (endpoints p1)) /\ conf.payload_size > 0
    ==>
    ?p4 p5. trans conf p2 LTau p4 /\
            trans conf p3 LTau p5 /\
            qcong p4 p5` suffices_by metis_tac[]
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
             rveq >> fs[]) >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive >>
          metis_tac[trans_com_l,qcong_par,qcong_sym])
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
          metis_tac[trans_com_l,qcong_par,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule payload_local_confluence_send >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
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
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl,qcong_sym])
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
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl,qcong_sym])
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
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>          
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule(GEN_ALL trans_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>          
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_com_l,trans_com_r,qcong_par,qcong_sym])
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
          metis_tac[trans_com_r,qcong_par,qcong_sym])
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
          metis_tac[trans_com_r,qcong_par,qcong_sym])
      >- (imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          dxrule payload_local_confluence_tau_receive >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl,qcong_sym]
         )
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
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl,qcong_sym])
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
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl,qcong_sym])
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
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl,qcong_sym]))
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
          impl_tac >- metis_tac[receiver_is_endpoint] >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_l,qcong_par,qcong_refl])
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
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint >>
          imp_res_tac receiver_is_endpoint >>
          drule payload_local_confluence_tau_receive >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_com_l,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_distinct_residual,label_distinct,
                                           sender_is_endpoint,receiver_is_endpoint]) >>
          strip_tac >>
          metis_tac[trans_com_r,trans_par_r,qcong_par,qcong_refl])
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
QED  
  
val _ = export_theory();

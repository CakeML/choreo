open preamble payloadSemTheory payloadLangTheory choreoUtilsTheory payload_altSemTheory payloadPropsTheory
     payloadConfluenceTheory;

val _ = new_theory "payload_altProps";

Theorem trans_alt_nontau_eq:
  ∀conf n1 α n2.
    α ≠ LTau ⇒
    trans_alt conf n1 α n2 = trans conf n1 α n2
Proof
  simp[EQ_IMP_THM,IMP_CONJ_THM,FORALL_AND_THM] >>
  simp[AND_IMP_INTRO] >>
  MAP_EVERY (fn path => CONV_TAC(path(PURE_ONCE_REWRITE_CONV [CONJ_SYM])))
    [LAND_CONV, RAND_CONV] >>
  conj_tac
  >- (simp[GSYM AND_IMP_INTRO] >>
      ho_match_mp_tac trans_alt_ind >>
      rw[] >>
      rw[Once trans_cases])
  >- (simp[GSYM AND_IMP_INTRO] >>
      ho_match_mp_tac trans_ind >>
      rw[] >>
      rw[Once trans_alt_cases])
QED

Theorem reduction_alt_IMP:
  ∀conf n1 n2.
    reduction_alt conf n1 n2 ⇒
    (reduction conf)^* n1 n2
Proof
  rpt GEN_TAC >>
  simp[reduction_alt_def] >>
  qmatch_goalsub_abbrev_tac ‘trans_alt _ _ α’ >>
  strip_tac >>
  qhdtm_x_assum ‘Abbrev’ (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘n2’,‘α’,‘n1’,‘conf’] >>
  ho_match_mp_tac trans_alt_strongind >> rpt strip_tac >>
  fs[] >> rveq >> fs[trans_alt_nontau_eq] >>
  TRY(drule_then MATCH_ACCEPT_TAC reduction_par_l) >>
  TRY(drule_then MATCH_ACCEPT_TAC reduction_par_r) >>
  TRY(rename1 ‘Letrec’ >>
      match_mp_tac RTC_TRANS >>
      simp[reduction_def,Once trans_cases] >>
      match_mp_tac RTC_SUBSET >>
      simp[reduction_def,Once trans_cases] >>
      simp[state_component_equality] >>
      rw[fmap_eq_flookup,flookup_fupdate_list] >>
      TOP_CASE_TAC >>
      fs[REVERSE_ZIP,GSYM MAP_REVERSE,ALOOKUP_ZIP_MAP_SND] >>
      rveq >>
      fs[ALOOKUP_ZIP_SELF] >> rveq >>
      fs[EVERY_MEM,IS_SOME_EXISTS] >>
      res_tac >> fs[]) >>
  match_mp_tac RTC_SUBSET >>
  simp[reduction_def,Once trans_cases] >>
  metis_tac[]
QED

Definition instacall_endpoint_def:
   (instacall_endpoint Nil = T)
∧ (instacall_endpoint (Send p v n e) = instacall_endpoint e)
∧ (instacall_endpoint (Receive p v d e) = instacall_endpoint e)
∧ (instacall_endpoint (IfThen v e1 e2) = (instacall_endpoint e1 ∧ instacall_endpoint e2))
∧ (instacall_endpoint (Let v f vl e) = instacall_endpoint e)
∧ (instacall_endpoint (Fix dv e) = instacall_endpoint e)
∧ (instacall_endpoint (Call dv) = T)
∧ (instacall_endpoint (Letrec dv vars e1 e2) = (instacall_endpoint e1 ∧ e2 = FCall dv vars))
∧ (instacall_endpoint (FCall dv vars) = T)
End

Definition instacall_closure_def:
  instacall_closure (Closure vars (fs,bds) e) =
  (instacall_endpoint e ∧ EVERY instacall_closure (MAP SND fs))
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  rw[MEM_MAP] >>
  rename1 ‘SND pair’ >> Cases_on ‘pair’ >>
  imp_res_tac closure_size_MEM >> fs[] >>
  DECIDE_TAC
End

Definition instacall_network_def:
   (instacall_network NNil = T)
∧ (instacall_network (NEndpoint p s e) = (instacall_endpoint e ∧ EVERY instacall_closure (MAP SND s.funs)))
∧ (instacall_network (NPar n1 n2) = (instacall_network n1 ∧ instacall_network n2))
End

Theorem RC_REFL:
  RC R x x
Proof
  rw[RC_DEF]
QED

Theorem instacall_endpoint_dsubst:
  ∀e1 dn e2.
  instacall_endpoint e1 ∧ instacall_endpoint e2 ⇒
  instacall_endpoint(dsubst e1 dn e2)
Proof
  rpt strip_tac >> Induct_on ‘e1’ >> rw[dsubst_def,instacall_endpoint_def]
QED

Theorem instacall_network_trans_pres:
  ∀conf n1 α n2.
    trans conf n1 α n2 ∧ instacall_network n1 ⇒ instacall_network n2
Proof
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_ind >> rpt strip_tac >>
  fs[instacall_network_def,instacall_endpoint_def,instacall_closure_def,instacall_endpoint_dsubst] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  res_tac >>
  fs[instacall_closure_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem reduction_IMP_reduction_alt:
  ∀conf n1 n2.
    reduction conf n1 n2 ∧
    instacall_network n1 ∧ no_undefined_vars_network n1 ⇒
    ∃n3. reduction_alt conf n1 n3 ∧ RC(reduction conf) n2 n3
Proof
  rpt GEN_TAC >>
  simp[reduction_def] >>
  qmatch_goalsub_abbrev_tac ‘trans _ _ α’ >>
  strip_tac >>
  qhdtm_x_assum ‘Abbrev’ (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘n2’,‘α’,‘n1’,‘conf’] >>
  ho_match_mp_tac trans_strongind >> rpt strip_tac >>
  fs[] >> rveq >> fs[GSYM trans_alt_nontau_eq,no_undefined_vars_network_NPar] >>
  TRY(rfs[instacall_network_def] >>
      first_x_assum(drule_then strip_assume_tac) >>
      metis_tac[reduction_alt_def,RC_DEF,reduction_def,trans_alt_par_l,trans_par_l,trans_alt_par_r,trans_par_r]) >>
  TRY(rename1 ‘Letrec’ >>
      fs[instacall_network_def,instacall_endpoint_def,no_undefined_vars_network_def,endpoints_def] >>
      rveq >>
      fs[free_var_names_endpoint_def] >>
      simp[reduction_alt_def,Once trans_alt_cases] >>
      conj_asm1_tac >-
        (rw[EVERY_MEM,IS_SOME_EXISTS] >>
         drule_all_then strip_assume_tac SUBSET_THM >>
         fs[FDOM_FLOOKUP]) >>
      match_mp_tac RC_SUBSET >>
      simp[reduction_def,Once trans_cases] >>
      simp[state_component_equality] >>
      rw[fmap_eq_flookup,flookup_fupdate_list] >>
      TOP_CASE_TAC >>
      fs[REVERSE_ZIP,GSYM MAP_REVERSE,ALOOKUP_ZIP_MAP_SND] >>
      rveq >>
      fs[ALOOKUP_ZIP_SELF] >> rveq >>
      fs[EVERY_MEM,IS_SOME_EXISTS] >>
      res_tac >> fs[]) >>
  goal_assum(resolve_then (Pos last) mp_tac RC_REFL) >>
  simp[reduction_alt_def,Once trans_alt_cases] >>
  metis_tac[]
QED

Theorem instacall_network_trans_alt_pres:
  ∀conf n1 α n2.
    trans_alt conf n1 α n2 ∧ instacall_network n1 ⇒ instacall_network n2
Proof
  rpt strip_tac >>
  Cases_on ‘α = LTau’ >-
    (rveq >> fs[GSYM reduction_alt_def] >>
     drule reduction_alt_IMP >>
     pop_assum mp_tac >> simp[AND_IMP_INTRO] >>
     match_mp_tac RTC_lifts_invariants >>
     metis_tac[reduction_def,instacall_network_trans_pres]) >>
  metis_tac[instacall_network_trans_pres,trans_alt_nontau_eq]
QED

Theorem trans_alt_send_receive_distinct:
  trans_alt conf p1 (LSend s1 d1 r1) p2
  /\ trans_alt conf p1 (LReceive s2 d2 r2) p3
  /\ conf.payload_size > 0 (* not strictly needed *)
  ==> p2 <> p3
Proof
  metis_tac[trans_send_receive_distinct,trans_alt_nontau_eq,label_distinct]
QED

Theorem trans_alt_different_sender:
  trans_alt conf p1 (LSend s1 d1 r1) p2
  /\ trans_alt conf p1 (LSend s2 d2 r2) p3
  /\ conf.payload_size > 0
  /\ s1 <> s2
  ==> p2 <> p3
Proof
  metis_tac[trans_different_sender,trans_alt_nontau_eq,label_distinct]
QED

Theorem trans_alt_same_sender_determ:
  trans_alt conf p1 (LSend q2 d1 q1) p2
  /\ trans_alt conf p1 (LSend q2 d2 q3) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q1 = q3 /\ d1 = d2 /\ p2 = p3
Proof
  metis_tac[trans_same_sender_determ,trans_alt_nontau_eq,label_distinct]
QED

Theorem sender_is_endpoint_alt:
  ∀p1 p2 q1 d q2 conf.
    trans_alt conf p1 (LSend q1 d q2) p2 ==> MEM q1 (MAP FST (endpoints p1))
Proof
  metis_tac[sender_is_endpoint,trans_alt_nontau_eq,label_distinct]
QED

Theorem receiver_is_endpoint_alt:
  ∀p1 p2 q1 d q2 conf.
    trans_alt conf p1 (LReceive q1 d q2) p2 ==> MEM q2 (MAP FST (endpoints p1))
Proof
  metis_tac[receiver_is_endpoint,trans_alt_nontau_eq,label_distinct]
QED

Theorem payload_local_confluence_send_alt:
  ∀conf p1 alpha p2 p3 s d r.
  trans_alt conf p1 alpha p2 /\ trans_alt conf p1 (LSend s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM r (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4 p5. trans_alt conf p2 (LSend s d r) p4 /\
        trans_alt conf p3 alpha p4
Proof
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_alt_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Send-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Send-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Enqueue *)
      (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
       fs[] >> rveq >> fs[] >> rveq >> fs[]
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_alt_send_last_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_alt_enqueue >>
           metis_tac[])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_alt_send_last_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_alt_enqueue >>
           metis_tac[])
       >- (qmatch_goalsub_abbrev_tac `NEndpoint _ s1` >>
           rename1 `FLOOKUP s.bindings v = SOME data` >>
           `FLOOKUP s1.bindings v = SOME data` by simp[Abbr`s1`] >>
           drule trans_alt_send_intermediate_payload >> simp[] >>
           disch_then drule >> disch_then dxrule >>
           rename1 `Send _ _ _ e1` >>
           disch_then(qspec_then `e1` assume_tac) >>
           asm_exists_tac >> simp[] >>
           drule trans_alt_enqueue >>
           metis_tac[]))
  >- (* Com-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          Cases_on `s = p1''` (* TODO: generated names *)
          >- metis_tac[trans_alt_same_sender_determ] >>
          drule_then assume_tac (GEN_ALL trans_alt_different_sender) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_alt_par_l,trans_alt_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          impl_tac >- metis_tac[trans_alt_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_alt_par_r,trans_alt_com_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          impl_tac >- metis_tac[trans_alt_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_alt_par_r,trans_alt_com_l]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          impl_tac >- metis_tac[trans_alt_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_alt_par_l,trans_alt_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          Cases_on `s = p1''` (* TODO: generated names *)
          >- metis_tac[trans_alt_same_sender_determ] >>
          drule_then assume_tac (GEN_ALL trans_alt_different_sender) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          ntac 2 strip_tac >> impl_tac >- simp[] >>
          strip_tac >> metis_tac[trans_alt_par_r,trans_alt_com_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          last_x_assum drule >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          impl_tac >- metis_tac[trans_alt_send_receive_distinct] >>
          strip_tac >> metis_tac[trans_alt_par_r,trans_alt_com_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* If-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Let *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_alt_par_l])
      >- (metis_tac[trans_alt_par_l,trans_alt_par_r])
      >- (metis_tac[trans_alt_par_l,trans_alt_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_alt_par_l,trans_alt_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_alt_par_r,trans_alt_par_l])
  >- (* trans_alt_fix *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* trans_alt_letrec *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
  >- (* trans_alt_call *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[])
QED

Theorem payload_local_confluence_receive_alt:
  ∀conf p1 s1 d1 r1 p2 p3 s2 d2 r2.
  trans_alt conf p1 (LReceive s1 d1 r1) p2 /\ trans_alt conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4. trans_alt conf p2 (LReceive s2 d2 r2) p4 /\
        trans_alt conf p3 (LReceive s1 d1 r1) p4
Proof
  `∀conf p1 alpha p2 s1 d1 r1 p3 s2 d2 r2.
  trans_alt conf p1 alpha p2 /\ alpha = LReceive s1 d1 r1 /\
  trans_alt conf p1 (LReceive s2 d2 r2) p3 /\ s1 <> s2
  ==>
  ?p4. trans_alt conf p2 (LReceive s2 d2 r2) p4 /\
        trans_alt conf p3 (LReceive s1 d1 r1) p4` suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_alt_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Enqueue *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      dxrule trans_alt_enqueue >> disch_then(qspecl_then [`conf`,`s1`,`d2`,`e`] mp_tac) >>
      unabbrev_all_tac >> strip_tac >>
      asm_exists_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `NEndpoint p2 s1 e` >>
      qpat_x_assum `_ <> _` mp_tac >>
      dxrule trans_alt_enqueue >> disch_then(qspecl_then [`conf`,`s1`,`d`,`e`] mp_tac) >>
      unabbrev_all_tac >> rpt strip_tac >>
      simp[] >> fs[qpush_commute])
  >- (* Par-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_alt_par_l,trans_alt_par_r])
  >- (* Par-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      metis_tac[trans_alt_par_l,trans_alt_par_r])
QED

Theorem trans_alt_let'':
  ∀conf s v p f vl e q.
         EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl) ⇒
         trans_alt conf (NEndpoint p (s with queues:= q) (Let v f vl e)) LTau
           (NEndpoint p
              (s with<|
                 bindings := s.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s.bindings) vl));
                 queues:= q
                 |>) e)
Proof
  rw[Once trans_alt_cases]
QED

Theorem trans_alt_dequeue_last_payload':
  ∀conf s1 s2 v p1 p2 e d tl ds q.
     p1 ≠ p2 ∧ qlk s1.queues p1 = d::tl ∧ final d ∧
     s2.funs = s1.funs ∧
     s2.bindings = s1.bindings |+ (v,FLAT (SNOC (unpad d) ds)) ∧
     s2.queues = normalise_queues(s1.queues |+ (p1,tl))
     ⇒
     trans_alt conf (NEndpoint p2 s1 (Receive p1 v ds e)) LTau
       (NEndpoint p2 s2 e)
Proof
  rw[Once trans_alt_cases] >> rw[state_component_equality]
QED

Theorem trans_alt_dequeue_intermediate_payload':
  ∀conf s1 s2 v p1 p2 e d ds tl.
     p1 ≠ p2 ∧ qlk s1.queues p1 = d::tl ∧ intermediate d ∧
     s2.funs = s1.funs ∧
     s2.bindings = s1.bindings ∧
     s2.queues = normalise_queues(s1.queues |+ (p1,tl))
      ⇒
     trans_alt conf (NEndpoint p2 s1 (Receive p1 v ds e)) LTau
       (NEndpoint p2 s2
          (Receive p1 v (SNOC (unpad d) ds) e))
Proof
  rw[Once trans_alt_cases] >> rw[state_component_equality]
QED

Theorem trans_alt_same_receiver_determ:
  trans_alt conf p1 (LReceive s d r) p2
  /\ trans_alt conf p1 (LReceive s d r) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> p2 = p3
Proof
  metis_tac[trans_same_receiver_determ,trans_alt_nontau_eq,label_distinct]
QED

Theorem trans_alt_no_selfloop:
  !conf p1 alpha p2.
  trans_alt conf p1 alpha p2 ∧ conf.payload_size > 0 ∧ alpha ≠ LTau
  ==> p1 <> p2
Proof
  metis_tac[trans_no_selfloop,trans_alt_nontau_eq,label_distinct]
QED

Theorem trans_alt_distinct_residual:
  !conf p1 alpha p2 beta p3.
  trans_alt conf p1 alpha p2
  /\ trans_alt conf p1 beta p3
  /\ alpha <> beta
  /\ conf.payload_size > 0
  ==> p2 <> p3
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_alt_strongind >> rpt strip_tac >>
  fs[] >> rveq
  >- (* Send-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Send-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Enqueue *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Com-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_alt_no_selfloop,label_distinct])
  >- (* Com-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_alt_no_selfloop,label_distinct])
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* If-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* If-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Let *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Par-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_alt_no_selfloop,label_distinct])
  >- (* Par-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_alt_no_selfloop,label_distinct])
  >- (* Fix *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[state_component_equality])
  >- (* Letrec *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[state_component_equality])
  >- (* Call *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[state_component_equality])
QED

Theorem payload_local_confluence_tau_receive_alt:
  ∀conf p1 p2 p3 s d r.
  trans_alt conf p1 LTau p2 /\ trans_alt conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans_alt conf p2 (LReceive s d r) p4 /\
        trans_alt conf p3 LTau p4
Proof
  `∀conf p1 alpha p2 p3 s d r.
  trans_alt conf p1 alpha p2 /\ alpha = LTau /\ trans_alt conf p1 (LReceive s d r) p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  ~MEM s (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans_alt conf p2 (LReceive s d r) p4 /\
        trans_alt conf p3 LTau p4` suffices_by metis_tac[]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_alt_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send_alt >> disch_then drule >>
          impl_tac >-
            (simp[] >> metis_tac[sender_is_endpoint_alt,receiver_is_endpoint_alt]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send_alt >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[trans_alt_distinct_residual,sender_is_endpoint_alt,
                       receiver_is_endpoint_alt,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l]
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint_alt >>
          imp_res_tac sender_is_endpoint_alt >>
          dxrule payload_local_confluence_receive_alt >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint_alt >>
          imp_res_tac sender_is_endpoint_alt >>
          dxrule payload_local_confluence_receive_alt >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint_alt >>
          imp_res_tac sender_is_endpoint_alt >>
          dxrule payload_local_confluence_receive_alt >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac receiver_is_endpoint_alt >>
          imp_res_tac sender_is_endpoint_alt >>
          dxrule payload_local_confluence_receive_alt >>
          disch_then dxrule >>
          impl_tac >- metis_tac[] >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send_alt >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint_alt,receiver_is_endpoint_alt,trans_alt_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          drule payload_local_confluence_send_alt >> disch_then drule >>
          impl_tac >-
            (simp[] >>
             metis_tac[sender_is_endpoint_alt,receiver_is_endpoint_alt,trans_alt_distinct_residual,
                       label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans_alt _ (NEndpoint p2 s1 e) (LReceive _ data _)` >>
      dxrule trans_alt_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      fs[endpoints_def] >>
      rename1 ‘qpush _ p3 d2’ >>
      (Cases_on ‘p1 = p3’ >-
         (dep_rewrite.DEP_REWRITE_TAC[trans_alt_dequeue_last_payload'] >>
          fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND,
             normalise_queues_FUPDATE_NONEMPTY] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT]
         ) >>
       dep_rewrite.DEP_REWRITE_TAC[trans_alt_dequeue_last_payload'] >>
       fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
       fs[FUPDATE_COMMUTES] >>
       rw[normalise_queues_FUPDATE_NONEMPTY]
      ))
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans_alt _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_alt_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      rename1 ‘qpush _ p3 d2’ >>
      (Cases_on ‘p1 = p3’ >-
         (dep_rewrite.DEP_REWRITE_TAC[trans_alt_dequeue_intermediate_payload'] >>
          fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
          rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT] >>
          fs[FLOOKUP_normalise_queues_FUPDATE] >> rw[]
          ) >>
       dep_rewrite.DEP_REWRITE_TAC[trans_alt_dequeue_intermediate_payload'] >>
       fs[qpush_def,qlk_def,fget_def,FLOOKUP_UPDATE,CaseEq"option",SNOC_APPEND] >>
       fs[FUPDATE_COMMUTES] >> rw[normalise_queues_FUPDATE_NONEMPTY] >>
       rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[DRESTRICT_normalise_queues,FLOOKUP_DRESTRICT] >>
       fs[FLOOKUP_normalise_queues] >> every_case_tac >> fs[])
     )
  >- (* If-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans_alt _ (NEndpoint p2 s1 e1) (LReceive _ data _)` >>
      dxrule trans_alt_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`e1`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      match_mp_tac trans_alt_if_true >>
      simp[]
     )
  >- (* If-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans_alt _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_alt_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      match_mp_tac trans_alt_if_false >>
      simp[]
     )
  >- (* Let *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      qmatch_goalsub_abbrev_tac `trans_alt _ (NEndpoint p2 s1 ee) (LReceive _ data _)` >>
      dxrule trans_alt_enqueue >>
      disch_then(qspecl_then [`conf`,`s1`,`data`,`ee`] assume_tac) >>
      asm_exists_tac >> simp[] >> unabbrev_all_tac >>
      simp[] >>
      match_mp_tac trans_alt_let'' >> simp[]
     )
  >- (* Par-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_alt_par_l])
      >- (metis_tac[trans_alt_par_l,trans_alt_par_r])
      >- (metis_tac[trans_alt_par_l,trans_alt_par_r]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- metis_tac[trans_alt_par_l,trans_alt_par_r] >>
      fs[endpoints_def,ALL_DISTINCT_APPEND] >>
      metis_tac[trans_alt_par_r,trans_alt_par_l])
  >- (* Fix *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      metis_tac[trans_alt_fix,trans_alt_enqueue])
  >- (* Letrec *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_alt_cases] >>
      fs[PULL_EXISTS])
  >- (* Call *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_alt_cases] >>
      fs[PULL_EXISTS])
QED

Theorem payload_local_confluence_tau_alt:
  ∀conf p1 p2 p3.
  trans_alt conf p1 LTau p2 /\ trans_alt conf p1 LTau p3 /\ p2 <> p3 /\
  ALL_DISTINCT (MAP FST (endpoints p1)) /\
  conf.payload_size > 0
  ==>
  ?p4. trans_alt conf p2 LTau p4 /\
        trans_alt conf p3 LTau p4
Proof
  `∀conf p1 alpha p2.
    trans_alt conf p1 alpha p2 ==> !p3. alpha = LTau /\ trans_alt conf p1 LTau p3 /\ p2 <> p3 /\
    ALL_DISTINCT (MAP FST (endpoints p1)) /\ conf.payload_size > 0
    ==>
    ?p4. trans_alt conf p2 LTau p4 /\
            trans_alt conf p3 LTau p4` suffices_by metis_tac[]
  >> ho_match_mp_tac trans_alt_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_alt_same_sender_determ >>
             rveq >> fs[]) >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive_alt >>
          metis_tac[trans_alt_com_l])
      >- (qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_alt_same_sender_determ >>
             rveq >> fs[] >> metis_tac[trans_alt_same_receiver_determ]) >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac (GEN_ALL trans_alt_different_sender) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          first_x_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive_alt >>
          metis_tac[trans_alt_com_l])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule(GEN_ALL trans_alt_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_com_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_alt_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- simp[] >>
          rpt strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_com_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_tau_receive_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_tau_receive_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r]))
  >- (* Com-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          drule(GEN_ALL trans_alt_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_com_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule(GEN_ALL trans_alt_send_receive_distinct) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          dxrule_then assume_tac payload_local_confluence_send_alt >>
          strip_tac >> first_x_assum dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          rpt strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_com_r])
      >- (qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_alt_same_sender_determ >>
             rveq >> fs[] >>
             dxrule_all trans_alt_same_receiver_determ >> simp[]
            ) >>
          drule_then assume_tac (GEN_ALL trans_alt_different_sender) >>
          pop_assum(qspec_then `s2` mp_tac) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive_alt >>
          metis_tac[trans_alt_com_r])
      >- (qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s1 _ _)` >>
          qpat_x_assum `trans_alt _ _ (LSend _ _ _) _` mp_tac >>
          qmatch_asmsub_abbrev_tac `trans_alt _ _ (LSend s2 _ _)` >>
          strip_tac >>
          rpt(qhdtm_x_assum `Abbrev` kall_tac) >>
          Cases_on `s1 = s2` >-
            (rveq >>
             fs[endpoints_def,ALL_DISTINCT_APPEND] >>
             dxrule_all_then strip_assume_tac trans_alt_same_sender_determ >>
             rveq >> fs[] >>
             dxrule_all trans_alt_same_receiver_determ >> simp[]
            ) >>
          drule_then assume_tac (GEN_ALL trans_alt_different_sender) >>
          pop_assum(qspec_then `s2` mp_tac) >>
          disch_then drule >> impl_tac >- simp[] >>
          strip_tac >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          dxrule_all_then strip_assume_tac payload_local_confluence_receive_alt >>
          metis_tac[trans_alt_com_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          dxrule payload_local_confluence_tau_receive_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l]
         )
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_tau_receive_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r])
      >- (imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule_then assume_tac trans_alt_distinct_residual >>
          qhdtm_x_assum `trans_alt` mp_tac >>
          pop_assum drule >> impl_tac >- simp[] >>
          rpt strip_tac >>
          dxrule payload_local_confluence_send_alt >>
          disch_then dxrule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r]))
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[] >>
      imp_res_tac intermediate_final_IMP)
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      fs[APPEND_EQ_APPEND_MID] >> rveq >>
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[] >>
      imp_res_tac intermediate_final_IMP)
  >- (* If-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* If-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* Let *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[])
  >- (* Par-L *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send_alt >>
          disch_then drule >>
          impl_tac >- metis_tac[receiver_is_endpoint_alt] >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct,
                                           sender_is_endpoint_alt,receiver_is_endpoint_alt]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule payload_local_confluence_tau_receive_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule payload_local_confluence_tau_receive_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_alt_par_r,trans_alt_par_l])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          metis_tac[trans_alt_par_r,trans_alt_par_l]))
  >- (* Par-R *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[]
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule payload_local_confluence_tau_receive_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          imp_res_tac sender_is_endpoint_alt >>
          imp_res_tac receiver_is_endpoint_alt >>
          drule payload_local_confluence_tau_receive_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct]) >>
          strip_tac >>
          metis_tac[trans_alt_com_l,trans_alt_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct,
                                           sender_is_endpoint_alt,receiver_is_endpoint_alt]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          qpat_x_assum `_ _ _ LTau _` assume_tac >>
          drule payload_local_confluence_send_alt >>
          disch_then drule >>
          impl_tac >- (simp[] >> metis_tac[trans_alt_distinct_residual,label_distinct,
                                           sender_is_endpoint_alt,receiver_is_endpoint_alt]) >>
          strip_tac >>
          metis_tac[trans_alt_com_r,trans_alt_par_r])
      >- (dxrule_then (qspec_then `p2` assume_tac) trans_alt_par_l >>
          asm_exists_tac >> simp[] >> pop_assum kall_tac >>
          rename1 `NPar q` >>
          dxrule_then (qspec_then `q` assume_tac) trans_alt_par_r >>
          asm_exists_tac >> simp[])
      >- (dxrule_then (qspec_then `p2` assume_tac) trans_alt_par_l >>
          asm_exists_tac >> simp[] >> pop_assum kall_tac >>
          rename1 `NPar q` >>
          dxrule_then (qspec_then `q` assume_tac) trans_alt_par_r >>
          asm_exists_tac >> simp[])
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          imp_res_tac trans_alt_par_r >>
          rpt(first_x_assum(qspec_then `n1` assume_tac)) >>
          ntac 2 (asm_exists_tac >> simp[]) >>
          metis_tac[]))
  >- (* Fix *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_alt_cases] >>
      fs[PULL_EXISTS])
  >- (* Letrec *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_alt_cases] >>
      fs[PULL_EXISTS])
  >- (* Call *)
     (qhdtm_x_assum `trans_alt` (assume_tac o SIMP_RULE std_ss [Once trans_alt_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >>
      PURE_ONCE_REWRITE_TAC[trans_alt_cases] >>
      fs[PULL_EXISTS])
QED

val list_trans_alt_def = Define `
    (list_trans_alt conf p [] q = (p = q))
 /\ (list_trans_alt conf p (alpha::l) q = ?p'. trans_alt conf p alpha p' /\ list_trans_alt conf p' l q)`

val list_trans_alt_append = Q.store_thm("list_trans_alt_append",
  `!l1 n1 l2 n2 conf. list_trans_alt conf n1 (l1 ++ l2) n2 =
  ?n3. list_trans_alt conf n1 l1 n3 /\ list_trans_alt conf n3 l2 n2`,
  Induct_on `l1` >> rpt strip_tac >> fs[list_trans_alt_def]
  >> rw[EQ_IMP_THM] >> fs[] >> metis_tac[]);

val endpoint_names_trans_alt = Q.store_thm("endpoint_names_trans_alt",
  `!conf n1 alpha n2. trans_alt conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  ho_match_mp_tac trans_alt_strongind >> rpt strip_tac >> fs[endpoints_def]);

val endpoint_names_list_trans_alt = Q.store_thm("endpoint_names_list_trans_alt",
  `!conf n1 alpha n2. list_trans_alt conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  Induct_on `alpha` >> rw[list_trans_alt_def] >>
  metis_tac[endpoint_names_trans_alt]);

Theorem payload_confluence_contract_alt:
  ∀m conf p1 p2 p3.
   trans_alt conf p1 LTau p2 /\
   list_trans_alt conf p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1)) /\
   conf.payload_size > 0
   ==>
   (?n. list_trans_alt conf p2 (REPLICATE n LTau) p3 /\
        n <= m) \/
   (?n p4. list_trans_alt conf p2 (REPLICATE n LTau) p4 /\
        trans_alt conf p3 LTau p4 /\
        n <= m)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_alt_def] >> rveq >>
      disj2_tac >> asm_exists_tac >> simp[])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_alt_append,list_trans_alt_def]
  >> first_x_assum drule_all
  >> strip_tac
  >- (disj1_tac >>
      qexists_tac ‘SUC n’ >>
      PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
      rw[list_trans_alt_append,list_trans_alt_def] >>
      metis_tac[])
  >- (Cases_on `p3 = p4`
      >- (rveq >>
          disj1_tac >> asm_exists_tac >>
          simp[]) >>
      disj2_tac >>
      imp_res_tac endpoint_names_trans_alt >>
      imp_res_tac endpoint_names_list_trans_alt >>
      dxrule payload_local_confluence_tau_alt >>
      disch_then dxrule >>
      impl_tac >- simp[] >>
      strip_tac >>
      qexists_tac ‘SUC n’ >>
      PURE_REWRITE_TAC[REPLICATE_SUC_SNOC] >>
      rw[list_trans_alt_append,list_trans_alt_def] >>
      metis_tac[])
QED

Theorem payload_confluence_weak_contract_alt:
  ∀n m conf p1 p2 p3.
   list_trans_alt conf p1 (REPLICATE n LTau) p2 /\
   list_trans_alt conf p1 (REPLICATE m LTau) p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1)) /\
   conf.payload_size > 0
   ==>
   (?n' m' p4. list_trans_alt conf p2 (REPLICATE n' LTau) p4 /\
        list_trans_alt conf p3 (REPLICATE m' LTau) p4 /\
        n' <= m /\ m' <= n)
Proof
  Induct >> rpt strip_tac
  >- (fs[list_trans_alt_def] >> rveq >>
      asm_exists_tac >> simp[])
  >> FULL_SIMP_TAC bool_ss [REPLICATE_SUC_SNOC]
  >> fs[list_trans_alt_append,list_trans_alt_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> drule payload_confluence_contract_alt
  >> disch_then drule
  >> impl_tac
  >- (imp_res_tac endpoint_names_trans_alt >>
      imp_res_tac endpoint_names_list_trans_alt >>
      fs[])
  >> strip_tac
  >- (asm_exists_tac >> simp[] >> asm_exists_tac >> simp[] >> metis_tac[])
  >> goal_assum drule >> simp[]
  >> qexists_tac ‘SUC m'’
  >> PURE_REWRITE_TAC[REPLICATE_SUC_SNOC]
  >> rw[list_trans_alt_append,list_trans_alt_def]
  >> metis_tac[]
QED

Theorem reduction_list_trans_alt:
  (reduction_alt conf)^* p q = ?n. list_trans_alt conf p (REPLICATE n LTau) q
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (MAP_EVERY qid_spec_tac [`q`,`p`] >>
      ho_match_mp_tac RTC_INDUCT >>
      rw[]
      >- (qexists_tac `0` >> simp[list_trans_alt_def])
      >- (fs[reduction_alt_def] >>
          qexists_tac `SUC n` >>
          simp[list_trans_alt_def] >>
          asm_exists_tac >> simp[]))
  >- (rpt strip_tac >> pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [`q`,`p`,`n`] >>
      Induct >>
      rw[list_trans_alt_def] >>
      fs[GSYM reduction_alt_def] >>
      metis_tac[RTC_RULES])
QED

val _ = export_theory();

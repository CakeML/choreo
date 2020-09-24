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

Theorem ALOOKUP_ZIP_SELF:
  ALOOKUP (ZIP (l,l)) x =
  if MEM x l then SOME x else NONE
Proof
  Induct_on ‘l’ >>
  rw[] >> fs[]
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

val _ = export_theory();

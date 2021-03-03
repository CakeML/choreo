open preamble payloadSemTheory payloadLangTheory choreoUtilsTheory payload_closureTheory payloadPropsTheory
     payload_bisimTheory payloadConfluenceTheory ConseqConv;

val _ = new_theory "payload_closureProof";

Definition fsubst_def:
   fsubst payloadLang$Nil fn e' = payloadLang$Nil
∧ fsubst (Send p v n e) fn e' = Send p v n (fsubst e fn e')
∧ fsubst (Receive p v d e) fn e' = Receive p v d (fsubst e fn e')
∧ fsubst (IfThen v e1 e2) fn e' = IfThen v (fsubst e1 fn e') (fsubst e2 fn e')
∧ fsubst (Let v f vl e) fn e' = Let v f vl (fsubst e fn e')
∧ fsubst (Fix fn' e) fn e' =
   Fix fn' (fsubst e fn e')
∧ fsubst (Call fn') fn e' =
   Call fn'
∧ fsubst (Letrec fn' vars e1) fn e' =
   (if fn = fn' then
     Letrec fn' vars e1
    else
     Letrec fn' vars (fsubst e1 fn e')
   )
∧ fsubst (FCall fn' vars) fn e' =
   (if fn = fn' then
      e'
    else
      FCall fn' vars)
End

Definition no_undefined_writes_def:
  no_undefined_writes n =
  EVERY (λ(p,s,e). set(written_var_names_endpoint e) ⊆ FDOM s.bindings) (endpoints n)
End

Theorem no_undefined_writes_NPar:
  no_undefined_writes (NPar n1 n2) = (no_undefined_writes n1 ∧ no_undefined_writes n2)
Proof
  rw[no_undefined_writes_def,endpoints_def]
QED

Theorem MEM_written_var_names_endpoint_until_IMP:
  MEM v (written_var_names_endpoint_until e) ⇒
  MEM v (written_var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[written_var_names_endpoint_def,written_var_names_endpoint_until_def] >> fs[]
QED

Theorem written_var_names_endpoint_dsubst:
  MEM x (written_var_names_endpoint (dsubst e dn e')) ⇒
  MEM x (written_var_names_endpoint e) ∨ MEM x (written_var_names_endpoint e')
Proof
  Induct_on ‘e’ >> rw[dsubst_def,written_var_names_endpoint_def] >> fs[]
QED

Theorem written_var_names_endpoint_dsubst':
  MEM x (written_var_names_endpoint e) ⇒
  MEM x (written_var_names_endpoint (dsubst e dn e'))
Proof
  Induct_on ‘e’ >> rw[dsubst_def,written_var_names_endpoint_def] >> fs[]
QED

Theorem set_written_var_names_endpoint_until:
  set(written_var_names_endpoint_until e) ⊆ set(written_var_names_endpoint e)
Proof
  metis_tac[SUBSET_DEF,MEM_written_var_names_endpoint_until_IMP]
QED

Theorem free_var_names_endpoint_compile_endpoint:
  ∀x ar e.
  set(free_fix_names_endpoint e) ⊆ set(MAP FST ar) ∧
  MEM x (free_var_names_endpoint(compile_endpoint ar e)) ⇒
  MEM x (FLAT(MAP SND ar)) ∨ MEM x (free_var_names_endpoint e) ∨ MEM x (written_var_names_endpoint e)
Proof
  strip_tac >> Induct_on ‘e’ >>
  fs[free_var_names_endpoint_def,compile_endpoint_def,MEM_FILTER,MEM_nub',
     free_fix_names_endpoint_def,LIST_TO_SET_FILTER,SUBSET_DEF,
     DISJ_IMP_THM,FORALL_AND_THM,written_var_names_endpoint_def] >>
  rw[] >>
  res_tac >> fs[MEM_nub'] >> fs[] >>
  rfs[]
  >- metis_tac[]
  >- (PURE_FULL_CASE_TAC >> fs[free_var_names_endpoint_def] >>
      fs[MEM_FLAT,MEM_MAP] >>
      metis_tac[ALOOKUP_MEM,SND])
QED

Theorem free_var_names_endpoint_compile_endpoint_NIL:
  ∀x e.
  free_fix_names_endpoint e = [] ∧
  MEM x (free_var_names_endpoint(compile_endpoint [] e)) ⇒
  MEM x (free_var_names_endpoint e) ∨ MEM x (written_var_names_endpoint e)
Proof
  rw[] >>
  drule_at (Pos last) free_var_names_endpoint_compile_endpoint >>
  rw[]
QED

Theorem compile_network_preservation_send:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf p1 (LSend p3 d p4) p2
    ⇒ trans conf (compile_network_alt p1) (LSend p3 d p4) (compile_network_alt p2)
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,no_undefined_writes_NPar,compile_network_alt_def] >>
  rw[compile_network_alt_def] >>
  TRY(rename1 ‘NPar’ >> rw[Once trans_cases] >> NO_TAC) >>
  fs[no_undefined_writes_def,endpoints_def] >>
  simp[compile_endpoint_def] >>
  rw[Once trans_cases,PULL_EXISTS] >>
  rw[flookup_update_list_some,ALOOKUP_MAP,written_var_names_endpoint_def,ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,FDOM_FLOOKUP,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

Theorem compile_network_reflection_send:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf (compile_network_alt p1) (LSend p3 d p4) p2
    ∧ fix_network p1
    ∧ no_undefined_vars_network p1
    ⇒ ∃p2'. trans conf p1 (LSend p3 d p4) p2' ∧ p2 = compile_network_alt p2'
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,compile_network_alt_def,fix_network_NPar,no_undefined_vars_network_NPar]
  >- metis_tac[trans_par_l,network_11,compile_network_alt_def]
  >- metis_tac[trans_par_r,network_11,compile_network_alt_def]
  >- ((* trans_send_intermediate_payload *)
      rename [‘compile_endpoint _ e’] >> Cases_on ‘e’ >> fs[compile_endpoint_def] >> rveq >> fs[] >>
      fs[written_var_names_endpoint_def] >>
      fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def] >>
      fs[flookup_fupdate_list] >>
      reverse(fs[CaseEq "option"])
      >- (imp_res_tac ALOOKUP_MEM >> fs[MAP_REVERSE,MAP_ZIP,MEM_MAP,MEM_FILTER]) >>
      simp[Once trans_cases] >>
      simp[compile_network_alt_def])
  >- ((* trans_send_final_payload *)
      rename [‘compile_endpoint _ e’] >> Cases_on ‘e’ >> fs[compile_endpoint_def] >> rveq >> fs[] >>
      fs[written_var_names_endpoint_def] >>
      fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def] >>
      fs[flookup_fupdate_list] >>
      reverse(fs[CaseEq "option"])
      >- (imp_res_tac ALOOKUP_MEM >> fs[MAP_REVERSE,MAP_ZIP,MEM_MAP,MEM_FILTER]) >>
      simp[Once trans_cases] >>
      simp[compile_network_alt_def,compile_endpoint_def,written_var_names_endpoint_def])
QED

Theorem compile_network_reflection_receive:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf (compile_network_alt p1) (LReceive p3 d p4) p2
    ∧ fix_network p1
    ∧ no_undefined_vars_network p1
    ⇒ ∃p2'. trans conf p1 (LReceive p3 d p4) p2' ∧ p2 = compile_network_alt p2'
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,compile_network_alt_def,fix_network_NPar,no_undefined_vars_network_NPar]
  >- metis_tac[trans_par_l,network_11,compile_network_alt_def]
  >- metis_tac[trans_par_r,network_11,compile_network_alt_def]
  >- ((* trans_enqueue *)
      simp[Once trans_cases] >>
      simp[compile_network_alt_def])
QED

Theorem compile_network_preservation_receive:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf p1 (LReceive p3 d p4) p2
    ⇒ trans conf (compile_network_alt p1) (LReceive p3 d p4) (compile_network_alt p2)
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,no_undefined_writes_NPar,compile_network_alt_def] >>
  rw[compile_network_alt_def] >>
  TRY(rename1 ‘NPar’ >> rw[Once trans_cases] >> NO_TAC) >>
  fs[no_undefined_writes_def,endpoints_def] >>
  simp[compile_endpoint_def] >>
  rw[Once trans_cases,PULL_EXISTS] >>
  rw[flookup_update_list_some,ALOOKUP_MAP,written_var_names_endpoint_def,ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,FDOM_FLOOKUP,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

Theorem compile_endpoint_ALOOKUP_eq:
  ∀e ar ar'. (∀x. ALOOKUP ar x = ALOOKUP ar' x) ⇒ compile_endpoint ar e = compile_endpoint ar' e
Proof
  Induct >> rw[compile_endpoint_def]
QED

Theorem compile_endpoint_ALOOKUP_eq_strong:
  ∀e ar ar'. (∀x. MEM x (free_fix_names_endpoint e) ⇒ ALOOKUP ar x = ALOOKUP ar' x) ⇒ compile_endpoint ar e = compile_endpoint ar' e
Proof
  Induct >> rw[compile_endpoint_def,free_fix_names_endpoint_def,MEM_FILTER]
QED

Theorem compile_endpoint_free_fix_names:
  ∀e ar. compile_endpoint ar e = compile_endpoint (FILTER (λ(dn,_). MEM dn (free_fix_names_endpoint e)) ar) e
Proof
  Induct >> rw[]
  >- (rw[compile_endpoint_def,free_fix_names_endpoint_def])
  >- (first_x_assum(qspec_then ‘ar’ mp_tac) >>
      rw[compile_endpoint_def,free_fix_names_endpoint_def])
  >- (first_x_assum(qspec_then ‘ar’ mp_tac) >>
      rw[compile_endpoint_def,free_fix_names_endpoint_def])
  >- (SIMP_TAC (srw_ss()) [compile_endpoint_def,free_fix_names_endpoint_def] >>
      EVERY_ASSUM (qspec_then ‘ar’ (ONCE_REWRITE_TAC o single)) >>
      SIMP_TAC (srw_ss()) [FILTER_FILTER,ELIM_UNCURRY,LEFT_AND_OVER_OR] >>
      rpt(pop_assum kall_tac) >>
      conj_tac >> AP_THM_TAC >> AP_TERM_TAC >>
      rw[FILTER_EQ,EQ_IMP_THM])
  >- (first_x_assum(qspec_then ‘ar’ mp_tac) >>
      rw[compile_endpoint_def,free_fix_names_endpoint_def])
  >- (SIMP_TAC (srw_ss()) [compile_endpoint_def,free_fix_names_endpoint_def,LET_THM] >>
      EVERY_ASSUM (qspec_then ‘ar’ (ONCE_REWRITE_TAC o single)) >>
      rpt(pop_assum kall_tac) >>
      rw[compile_endpoint_def,free_fix_names_endpoint_def] >>
      TRY(rename1 ‘~MEM _ (free_fix_names_endpoint _)’ >>
          rw[FILTER_FILTER,MEM_FILTER] >>
          AP_THM_TAC >> AP_TERM_TAC >> rw[FILTER_EQ,EQ_IMP_THM] >>
          fs[ELIM_UNCURRY] >>
          spose_not_then strip_assume_tac >> fs[] >> NO_TAC) >>
      match_mp_tac compile_endpoint_ALOOKUP_eq >>
      rw[ALOOKUP_FILTER] >>
      fs[MEM_FILTER] >> fs[])
  >- (rw[compile_endpoint_def,ALOOKUP_FILTER,free_fix_names_endpoint_def])
  >- (SIMP_TAC (srw_ss()) [compile_endpoint_def,free_fix_names_endpoint_def] >>
      EVERY_ASSUM (qspec_then ‘ar’ (ONCE_REWRITE_TAC o single)) >>
      SIMP_TAC (srw_ss()) [FILTER_FILTER,ELIM_UNCURRY,LEFT_AND_OVER_OR] >>
      rpt(pop_assum kall_tac) >>
      conj_tac >> AP_THM_TAC >> AP_TERM_TAC >>
      rw[FILTER_EQ,EQ_IMP_THM])
  >- (rw[compile_endpoint_def])
QED

Theorem compile_endpoint_free_fix_names:
  free_fix_names_endpoint e = [] ⇒
  compile_endpoint ar e = compile_endpoint [] e
Proof
  rw[Once compile_endpoint_free_fix_names,ELIM_UNCURRY]
QED

Theorem MEM_free_fix_names_endpoint_dsubst:
  ∀e dn e'.
  MEM x (free_fix_names_endpoint (dsubst e dn e')) ⇒
  MEM x (free_fix_names_endpoint e) ∨
  MEM x (free_fix_names_endpoint e')
Proof
  Induct >> rw[free_fix_names_endpoint_def,dsubst_def] >>
  fs[MEM_FILTER] >> res_tac >> fs[]
QED


Theorem free_fix_names_endpoint_dsubst_IMP:
  ∀e' e dn.
  free_fix_names_endpoint (Fix dn e) = [] ∧
  MEM x (free_fix_names_endpoint (dsubst e' dn (Fix dn e))) ⇒
  MEM x (free_fix_names_endpoint e')
Proof
  Induct >> rw[free_fix_names_endpoint_def,dsubst_def,fix_endpoint_def] >>
  fs[MEM_FILTER] >> res_tac >> fs[] >>
  fs[free_fix_names_endpoint_def] >>
  fs[FILTER_EQ_NIL,EVERY_MEM] >>
  res_tac
QED

Theorem free_fix_names_endpoint_IMP_dsubst:
  ∀e' e dn.
  free_fix_names_endpoint (Fix dn e) = [] ∧
  x ≠ dn ∧
  MEM x (free_fix_names_endpoint e') ⇒
  MEM x (free_fix_names_endpoint (dsubst e' dn (Fix dn e)))
Proof
  Induct >> rw[free_fix_names_endpoint_def,dsubst_def,fix_endpoint_def] >>
  fs[MEM_FILTER] >> res_tac >> fs[] >>
  fs[free_fix_names_endpoint_def] >>
  fs[FILTER_EQ_NIL,EVERY_MEM]
QED

Inductive saturates:
  (∀vars. saturates vars Nil Nil) ∧
  (∀vars e e' p v n.
     saturates vars e e' ⇒
     saturates vars (Send p v n e) (Send p v n e')) ∧
  (∀vars e e' p v d.
     saturates vars e e' ⇒
     saturates vars (Receive p v d e) (Receive p v d e')) ∧
  (∀vars e1 e2 e3 e4 v.
     saturates vars e1 e2 ∧ saturates vars e3 e4 ⇒
     saturates vars (IfThen v e1 e3) (IfThen v e2 e4)) ∧
  (∀vars e e' v f vl.
     saturates vars e e' ⇒
     saturates vars (Let v f vl e) (Let v f vl e')) ∧
  (∀vars e1 e2 dn vars' vars''.
     saturates vars e1 e2 ∧
     ALL_DISTINCT vars' ∧
     ALL_DISTINCT vars'' ∧
     set vars' ⊆ set vars'' ∧
     set vars'' ⊆ set vars ∪ set vars' ⇒
     saturates vars (Letrec dn vars' e1) (Letrec dn vars'' e2)) ∧
  (∀vars dn vars' vars''.
     ALL_DISTINCT vars' ∧
     ALL_DISTINCT vars'' ∧
     set vars' ⊆ set vars'' ∧
     set vars'' ⊆ set vars ∪ set vars' ⇒
     saturates vars (FCall dn vars') (FCall dn vars'')
  )
End

Theorem saturates_compile_endpoint_refl:
  ∀ar e vars.
  (∀s x. ALOOKUP ar s = SOME x ⇒ ALL_DISTINCT x)
  ⇒
  saturates vars (compile_endpoint ar e) (compile_endpoint ar e)
Proof
  Induct_on ‘e’ >> rw[] >>
  simp[compile_endpoint_def] >> simp[Once saturates_cases,PULL_EXISTS,all_distinct_nub'] >>
  res_tac >> simp[] >-
    (first_x_assum match_mp_tac >> rw[] >> fs[all_distinct_nub'] >> res_tac) >>
  TOP_CASE_TAC >> fs[] >> res_tac
QED

Theorem saturates_trans:
  ∀vars e1 e2 e3. saturates vars e1 e2  ∧ saturates vars e2 e3 ⇒
                  saturates vars e1 e3
Proof
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac saturates_ind >>
  rw[] >>
  qhdtm_x_assum ‘saturates’ (strip_assume_tac o ONCE_REWRITE_RULE[saturates_cases]) >>
  fs[] >> rveq >> fs[] >> res_tac >>
  simp[Once saturates_cases] >>
  fs[SUBSET_DEF,UNION_DEF,IN_DEF] >>
  rw[] >>
  res_tac >> fs[]
QED

Theorem saturates_compile_endpoint_ar:
  ∀ar ar' e vars.
  (∀s x. ALOOKUP ar s = SOME x ⇒ ALL_DISTINCT x) ∧
  (∀s x. ALOOKUP ar' s = SOME x ⇒ ALL_DISTINCT x) ∧
  LIST_REL (λ(s,vs) (s',vs'). s = s' ∧ set vs ⊆ set vs' ∧ set vs' ⊆ set vs ∪ set vars) ar ar'
  ⇒
  saturates vars (compile_endpoint ar e) (compile_endpoint ar' e)
Proof
  Induct_on ‘e’ >> rw[compile_endpoint_def] >>
  simp[Once saturates_cases] >>
  TRY(res_tac >> NO_TAC)
  >- metis_tac[]
  >- (simp[all_distinct_nub'] >>
      first_x_assum match_mp_tac >>
      rw[] >> simp[all_distinct_nub'] >>
      res_tac) >>
  TOP_CASE_TAC >> fs[]
  >- (‘ALOOKUP ar' s = NONE’ suffices_by simp[] >>
      ntac 2 (pop_assum mp_tac) >> rpt(pop_assum kall_tac) >>
      MAP_EVERY qid_spec_tac [‘ar'’,‘ar’] >>
      ho_match_mp_tac LIST_REL_ind >>
      rw[] >>
      rpt(pairarg_tac >> fs[] >> rveq) >>
      fs[AllCaseEqs()])
  >- (simp[AllCaseEqs()] >>
      fs[ALOOKUP_SOME_SPLIT] >> rveq >>
      fs[LIST_REL_SPLIT1] >> rveq >> fs[] >>
      pairarg_tac >> fs[] >> rveq >>
      simp[PULL_EXISTS,AC CONJ_SYM CONJ_ASSOC] >>
      goal_assum(resolve_then (Pat ‘_ = _’) mp_tac EQ_REFL) >>
      fs[UNION_COMM] >>
      fs[PULL_EXISTS] >>
      rpt(first_x_assum(resolve_then (Pat ‘_ = _’) assume_tac EQ_REFL)) >>
      rfs[] >>
      csimp[] >>
      spose_not_then strip_assume_tac >>
      fs[MEM_MAP,PULL_EXISTS] >>
      drule_all_then strip_assume_tac LIST_REL_MEM_IMP_SYM >>
      rpt(pairarg_tac >> fs[] >> rveq) >>
      metis_tac[FST])
QED

Theorem compile_endpoint_swap_init_ar:
  s ≠ s' ⇒
  compile_endpoint ((s,vars)::(s',vars')::ar) e =
  compile_endpoint ((s',vars')::(s,vars)::ar) e
Proof
  rw[] >>
  match_mp_tac compile_endpoint_ALOOKUP_eq_strong >>
  rw[]
QED

Definition arities_def:
  (arities payloadLang$Nil = []) ∧
  (arities (Send p v n e) = arities e) ∧
  (arities (Receive p v l e) = arities e) ∧
  (arities (IfThen v e1 e2) =
   (arities e1 ++ arities e2)) ∧
  (arities (Let v f vl e) =
   arities e) ∧
  (arities (Letrec dn vars e1) =
   FILTER ($≠ dn o FST) (arities e1)) ∧
  (arities (FCall dn vars) = [(dn,LENGTH vars)]) ∧
  (arities (Fix dn e) = arities e) ∧
  (arities (Call dn) = [])
End

Definition arsof_def:
  arsof dn e = set(MAP SND (FILTER ($= dn o FST) (arities e)))
End

Theorem MEM_arities_arsof:
  ∀dn n vars e.
    MEM (dn,n) (arities e) ⇒
    n ∈ arsof dn e
Proof
  rw[arsof_def,MEM_MAP,MEM_FILTER] >>
  metis_tac[FST,SND]
QED

Theorem arsof_simps[simp]:
  arsof dn (Send p v n e) = arsof dn e ∧
  arsof dn (Receive p v d e) = arsof dn e ∧
  arsof dn (Let v f vl e) = arsof dn e ∧
  arsof dn (IfThen v e1 e2) = arsof dn e1 ∪ arsof dn e2 ∧
  arsof dn (FCall dn vars) = {LENGTH vars}
Proof
  rw[arsof_def,arities_def,FILTER_APPEND]
QED

Theorem arsof_Nil:
  arsof dn Nil = {}
Proof
  rw[arsof_def,arities_def]
QED

Theorem arsof_letrec_lemma:
  dn ≠ s ⇒
  arsof dn (Letrec s l e1) =
  arsof dn e1
Proof
  rw[arsof_def,arities_def,SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
  metis_tac[FST,SND]
QED

Theorem arsof_FCall_lemma:
  dn ≠ s ⇒
  arsof dn (FCall s vars) = {}
Proof
  rw[arsof_def,arities_def]
QED

Definition consistent_arities_def:
  (consistent_arities payloadLang$Nil = T) ∧
  (consistent_arities (Send p v n e) = consistent_arities e) ∧
  (consistent_arities (Receive p v l e) = consistent_arities e) ∧
  (consistent_arities (IfThen v e1 e2) =
   (consistent_arities e1 ∧ consistent_arities e2)) ∧
  (consistent_arities (Let v f vl e) =
   consistent_arities e) ∧
  (consistent_arities (Letrec dn vars e1) =
   (consistent_arities e1 ∧
    (∀n. MEM (dn,n) (arities e1) ⇒ n = LENGTH vars))) ∧
  (consistent_arities (FCall dn vars) = T) ∧
  (consistent_arities (Fix dn e) = F) ∧
  (consistent_arities (Call dn) = F)
End

Theorem MEM_arities_compile_endpoint_IMP:
  ∀dn n ar e. MEM (dn,n) (arities(compile_endpoint ar e)) ⇒
    ∃vars. ALOOKUP ar dn = SOME vars ∧ LENGTH vars = n
Proof
  ntac 2 strip_tac >>
  Induct_on ‘e’ >>
  fs[arities_def,compile_endpoint_def] >>
  rw[] >> res_tac >> fs[] >>
  fs[MEM_FILTER] >>
  res_tac >>
  rfs[] >>
  PURE_FULL_CASE_TAC >> fs[arities_def]
QED

Theorem compile_endpoint_consistent_arities:
  ∀ar e. consistent_arities (compile_endpoint ar e)
Proof
  Induct_on ‘e’ >>
  rw[compile_endpoint_def,consistent_arities_def,arities_def] >>
  imp_res_tac MEM_arities_compile_endpoint_IMP >> rveq >>
  fs[] >>
  PURE_FULL_CASE_TAC >> fs[consistent_arities_def]
QED

Theorem compile_endpoint_dsubst:
  ∀dn e' e ar.
  free_fix_names_endpoint (Fix dn e) = [] ∧
  set(written_var_names_endpoint e') ⊆ set(written_var_names_endpoint e) ∧
  fix_endpoint e' ∧
  (∀s x. ALOOKUP ar s = SOME x ⇒ ALL_DISTINCT x) ⇒
  ∃e''.
    compile_endpoint ar (dsubst e' dn (Fix dn e)) =
    fsubst e'' dn (compile_endpoint [] (Fix dn e)) ∧
    saturates (written_var_names_endpoint e)
              (compile_endpoint ((dn,nub'(written_var_names_endpoint e))::ar) e')
              e'' ∧
    arsof dn e'' ⊆ {LENGTH(nub'(written_var_names_endpoint e))}
Proof
  strip_tac >> Induct >> rpt strip_tac
  >- ((* Nil *)
      fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def,Once saturates_cases,arsof_Nil])
  >- ((* Send *)
      fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
      simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
      fs[written_var_names_endpoint_def,free_fix_names_endpoint_def] >>
      metis_tac[]
     )
  >- ((* Receive *)
     fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
     simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
     fs[written_var_names_endpoint_def,free_fix_names_endpoint_def] >> metis_tac[])
  >- ((* If *)
     fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
     simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
     fs[written_var_names_endpoint_def,free_fix_names_endpoint_def,DIFF_UNION']
     >> metis_tac[])
  >- ((* Let *)
     fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
     simp[Once saturates_cases,PULL_EXISTS,fsubst_def,consistent_arities_def] >>
     fs[written_var_names_endpoint_def,free_fix_names_endpoint_def] >> metis_tac[])
  >- ((* Fix *)
     fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
     rw[] >> fs[compile_endpoint_def] >-
       (simp[Once saturates_cases,PULL_EXISTS] >>
        simp[fsubst_def] >>
        simp[all_distinct_nub'] >>
        reverse(rpt conj_tac)
        >- (simp[arsof_def,arities_def,FILTER_FILTER]) >>
        qmatch_goalsub_abbrev_tac ‘saturates _ a1 a2’ >>
        ‘a1 = a2’
          by(rw[Abbr ‘a1’,Abbr ‘a2’] >>
             match_mp_tac compile_endpoint_ALOOKUP_eq_strong >>
             rw[]) >>
        pop_assum(SUBST_TAC o single) >>
        unabbrev_all_tac >>
        ho_match_mp_tac saturates_compile_endpoint_refl >>
        rw[] >> fs[all_distinct_nub'] >>
        res_tac) >>
     simp[Once saturates_cases,PULL_EXISTS] >>
     simp[fsubst_def,all_distinct_nub',set_nub'] >>
     qmatch_goalsub_abbrev_tac ‘compile_endpoint a1’ >>
     first_x_assum drule >>
     disch_then(qspec_then ‘a1’ mp_tac) >>
     impl_tac
     >- (rw[Abbr ‘a1’] >>
         rfs[all_distinct_nub',written_var_names_endpoint_def,free_fix_names_endpoint_def,LIST_TO_SET_FILTER] >>
         res_tac >>
         fs[SUBSET_DEF,INTER_DEF] >>
         rw[] >>
         metis_tac[]) >>
     strip_tac >>
     goal_assum drule >>
     simp[Abbr ‘a1’] >>
     qspec_then ‘FCall x y’ (simp o single) (saturates_cases |> CONV_RULE SWAP_FORALL_CONV) >>
     simp[PULL_EXISTS,all_distinct_nub'] >>
     simp[fsubst_def,all_distinct_nub'] >>
     simp[set_nub'] >>
     conj_tac >-
       (drule_at_then (Pos last) match_mp_tac saturates_trans >>
        drule_then (REWRITE_TAC o single) compile_endpoint_swap_init_ar >>
        match_mp_tac saturates_compile_endpoint_ar >>
        simp[] >>
        conj_tac >- (rw[] >> fs[all_distinct_nub'] >> res_tac) >>
        conj_tac >- (rw[] >> fs[all_distinct_nub'] >> res_tac) >>
        simp[set_nub'] >>
        conj_tac >- (fs[written_var_names_endpoint_def] >>
                     reverse conj_tac >-
                       (rw[SUBSET_DEF,written_var_names_endpoint_dsubst] >>
                        drule_all written_var_names_endpoint_dsubst >>
                        rw[] >> fs[written_var_names_endpoint_def]) >>
                     metis_tac[SUBSET_DEF,written_var_names_endpoint_dsubst']) >>
        match_mp_tac EVERY2_refl >>
        rw[] >>
        pairarg_tac >> rveq >> fs[]) >>
     fs[written_var_names_endpoint_def] >>
     rw[SUBSET_DEF] >>
     TRY(drule_then MATCH_ACCEPT_TAC written_var_names_endpoint_dsubst') >>
     imp_res_tac written_var_names_endpoint_dsubst >> fs[written_var_names_endpoint_def] >>
     rfs[arsof_letrec_lemma,arsof_FCall_lemma] >>
     imp_res_tac SUBSET_THM >> fs[])
  >- (fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
      reverse(rw[] >> fs[compile_endpoint_def,fsubst_def]) >-
       (TOP_CASE_TAC >> rw[] >>
        simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
        res_tac >>
        fs[arsof_FCall_lemma,arsof_Nil]) >>
      fs[free_fix_names_endpoint_def] >>
      simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
      goal_assum(resolve_then (Pos hd) mp_tac compile_endpoint_ALOOKUP_eq_strong) >>
      fs[FILTER_EQ_NIL,EVERY_MEM] >>
      metis_tac[SUBSET_UNION,all_distinct_nub',set_nub',SUBSET_REFL])
  >- (fs[fix_endpoint_def])
  >- (fs[fix_endpoint_def])
QED

Definition compile_rel_def:
  compile_rel conf n1 n2 =
  (letrec_network n1 ∧ letrec_network n2 ∧
   BISIM_REL (trans conf) n1 n2
  )
End

Theorem compile_rel_refl:
  letrec_network x ⇒ compile_rel conf x x
Proof
  rw[compile_rel_def,bisim_refl]
QED

Theorem compile_rel_reflI:
  ∀conf x y. letrec_network x ∧ x = y ⇒ compile_rel conf x y
Proof
  simp[compile_rel_refl]
QED

Theorem ALOOKUP_ZIP_SELF:
  ALOOKUP (ZIP (l,l)) x =
  if MEM x l then SOME x else NONE
Proof
  Induct_on ‘l’ >>
  rw[] >> fs[]
QED

Theorem ALOOKUP_MAP_CONST_EQ:
  ALOOKUP(MAP (λx. (x,k)) l) x =
  if MEM x l then SOME k else NONE
Proof
  Induct_on ‘l’ >> rw[] >> fs[]
QED

Theorem letrec_endpoint_compile_endpoint:
  ∀ar e. letrec_endpoint (compile_endpoint ar e)
Proof
  Induct_on ‘e’ >> rw[letrec_endpoint_def,compile_endpoint_def] >>
  TOP_CASE_TAC >> rw[letrec_endpoint_def]
QED

Theorem letrec_network_compile_network_alt:
  ∀n. fix_network n ⇒ letrec_network(compile_network_alt n)
Proof
  Induct >> rw[compile_network_alt_def,letrec_network_def,endpoints_def,fix_network_def] >>
  fs[letrec_network_def,letrec_endpoint_compile_endpoint,fix_network_def]
QED

Theorem letrec_network_compile_network:
  ∀n. fix_network n ⇒ letrec_network(compile_network n)
Proof
  Induct >> rw[compile_network_def,letrec_network_def,endpoints_def,fix_network_def] >>
  fs[letrec_network_def,letrec_endpoint_compile_endpoint,fix_network_def] >>
  rename1 ‘FOLDL _ _ l’ >>
  qid_spec_tac ‘l’ >> ho_match_mp_tac SNOC_INDUCT >>
  rw[letrec_endpoint_def,letrec_endpoint_compile_endpoint,FOLDL_SNOC]
QED

Theorem saturates_nub':
  ∀e1 e2 vars. saturates (nub' vars) e1 e2 = saturates vars e1 e2
Proof
  Induct >> PURE_ONCE_REWRITE_TAC[saturates_cases] >>
  rw[set_nub']
QED

Theorem saturates_mono:
  ∀e1 e2 vars. saturates vars e1 e2 ∧ set vars ⊆ set vars' ⇒
               saturates vars' e1 e2
Proof
  Induct >> PURE_ONCE_REWRITE_TAC[saturates_cases] >>
  rw[set_nub'] >> res_tac >>
  fs[] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem written_var_names_endpoint_compile_endpoint_SUBSET:
  ∀ar e. fix_endpoint e ⇒
         set(written_var_names_endpoint e) ⊆ set(written_var_names_endpoint(compile_endpoint ar e))
Proof
  Induct_on ‘e’ >>
  fs[written_var_names_endpoint_def,compile_endpoint_def,fix_endpoint_def] >>
  rw[] >>
  fs[SUBSET_DEF]
QED

Theorem written_var_names_endpoint_compile_endpoint_SUBSET':
  ∀ar e. fix_endpoint e ⇒
         set(written_var_names_endpoint(compile_endpoint ar e)) ⊆
         set(written_var_names_endpoint e) ∪
         set(FLAT(MAP SND ar))
Proof
  Induct_on ‘e’ >>
  fs[written_var_names_endpoint_def,compile_endpoint_def,fix_endpoint_def] >>
  rw[] >> fs[SUBSET_DEF,MEM_FLAT,MEM_MAP,MEM_nub'] >>
  rw[] >> res_tac >> fs[PULL_EXISTS] >>
  rveq >> fs[] >>
  fs[MEM_nub'] >>
  TRY(PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_def,ALOOKUP_NONE] >>
      imp_res_tac ALOOKUP_MEM) >>
  metis_tac[MEM_written_var_names_endpoint_until_IMP,SND]
QED

Definition closure_args_def:
  closure_args (Closure vars1 env e) = vars1
End

Definition closure_var_env_def:
  closure_var_env (Closure vars1 env e) = SND env
End

Theorem MEM_arities_saturates:
  ∀dn n vars e1 e2.
    MEM (dn,n) (arities e1) ∧
    saturates vars e1 e2 ⇒
    ∃m. MEM (dn,m) (arities e2)
Proof
  ntac 3 strip_tac >>
  Induct_on ‘e1’ >>
  fs[arities_def] >> rw[Once saturates_cases] >> rw[arities_def] >>
  fs[MEM_FILTER] >>
  metis_tac[]
QED

Theorem letrec_endpoint_fsubst:
  ∀e1 dn e2.
    letrec_endpoint e1 ∧ letrec_endpoint e2 ⇒
    letrec_endpoint(fsubst e1 dn e2)
Proof
  Induct >> rw[letrec_endpoint_def,fsubst_def]
QED

Theorem letrec_endpoint_fsubst':
  ∀e1 dn e2.
    letrec_endpoint(fsubst e1 dn e2) ⇒
    letrec_endpoint e1
Proof
  Induct >> rw[letrec_endpoint_def,fsubst_def] >> res_tac
QED

Theorem MEM_arities_fsubst_IMP:
  ∀e1 dn e2.
    MEM (s,n) (arities(fsubst e1 dn e2)) ⇒
    (MEM (s,n) (arities e1) ∧ dn ≠ s) ∨ MEM (s,n) (arities e2)
Proof
  Induct >> rw[arities_def,fsubst_def,MEM_FILTER] >>
  res_tac >>
  fs[]
QED

Theorem MEM_arities_IMP_fsubst:
  ∀e1 dn e2.
    MEM (s,n) (arities e1) ∧ s ≠ dn ⇒
    MEM (s,n) (arities(fsubst e1 dn e2))
Proof
  Induct >> rw[arities_def,fsubst_def,MEM_FILTER] >>
  res_tac >>
  fs[]
QED

Theorem MEM_arities_imp_free_fun_names:
  ∀s n e. MEM (s,n) (arities e) ⇒ MEM s (free_fun_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[arities_def,free_fun_names_endpoint_def,MEM_FILTER] >>
  res_tac >> fs[]
QED

Theorem consistent_arities_fsubst_nofrees:
  ∀e1 dn e2.
    consistent_arities e1 ∧ consistent_arities e2 ∧
    free_fun_names_endpoint e2 = [] ⇒
    consistent_arities (fsubst e1 dn e2)
Proof
  Induct >> rw[consistent_arities_def,fsubst_def] >>
   (imp_res_tac MEM_arities_fsubst_IMP >- metis_tac[] >>
    imp_res_tac MEM_arities_imp_free_fun_names >> rfs[])
QED

Theorem fsubst_consistent_arities_nofrees:
  ∀e1 dn e2 n.
    consistent_arities (fsubst e1 dn e2) ∧
    arsof dn e1 ⊆ {n} ⇒
    consistent_arities e1
Proof
  Induct >> rw[consistent_arities_def,fsubst_def,arsof_letrec_lemma] >>
  res_tac >> metis_tac[MEM_arities_IMP_fsubst]
QED

Definition always_same_args_def:
   (always_same_args funs Nil = T)
∧ (always_same_args funs (Send p v n e) =
    always_same_args funs e)
∧ (always_same_args funs (Receive p v d e) =
    always_same_args funs e)
∧ (always_same_args funs (IfThen v e1 e2) =
    (always_same_args funs e1 ∧ always_same_args funs e2))
∧ (always_same_args funs (Let v f vl e) =
    always_same_args funs e)
∧ (always_same_args funs (Fix dv e) =
    always_same_args funs e)
∧ (always_same_args funs (Call dv) = T)
∧ (always_same_args funs (Letrec dv vars e1) =
    (always_same_args ((dv,vars)::funs) e1))
∧ (always_same_args funs (FCall dv vars) =
    case ALOOKUP funs dv of
      NONE => T
    | SOME vars' => vars' = vars)
End

Definition good_letrecs_def:
   (good_letrecs known Nil = T)
∧ (good_letrecs known (Send p v n e) =
    good_letrecs known e)
∧ (good_letrecs known (Receive p v d e) =
    good_letrecs known e)
∧ (good_letrecs known (IfThen v e1 e2) =
    (good_letrecs known e1 ∧ good_letrecs known e2))
∧ (good_letrecs known (Let v f vl e) =
    good_letrecs known e)
∧ (good_letrecs known (Fix dv e) =
    good_letrecs known e)
∧ (good_letrecs known (Call dv) = T)
∧ (good_letrecs known (Letrec dv vars e1) =
    (good_letrecs ((dv,vars)::known) e1 ∧
     (∀dn vars'. MEM dn (free_fun_names_endpoint e1) ∧
                 ALOOKUP known dn = SOME vars' ⇒
                 set vars ⊆ set vars') ∧
     set(written_var_names_endpoint_before dv e1) ⊆ set vars))
∧ (good_letrecs known (FCall dv vars) =
    T)
End

Definition compile_fix_closure_rel_def:
  compile_fix_closure_rel dn e vars dn' (Closure vars1 (fs1,bds1) e1) (Closure vars2 (fs2,bds2) e2) ⇔
  ∃shadow e'.
    bds1 = bds2 ∧
    letrec_endpoint e ∧ letrec_endpoint e1 ∧ letrec_endpoint e2 ∧
    consistent_arities e ∧ consistent_arities e1 ∧ consistent_arities e' ∧
    arsof dn e ⊆ {LENGTH vars} ∧
    set(written_var_names_endpoint e) (* DIFF set vars *) ⊆ FDOM bds1 ∧
    (¬shadow ⇒ set(written_var_names_endpoint_before dn e1) ⊆ set vars) ∧
    set(written_var_names_endpoint_before dn' e1) ⊆ set vars1 ∧
    set(written_var_names_endpoint e') ⊆ set(written_var_names_endpoint e) ∧
    good_letrecs ((dn',vars1)::MAP (λ(x,y). (x, closure_args y)) fs1) e1 ∧
    ALL_DISTINCT vars ∧
    (* ¬MEM dn (bound_fun_names_endpoint e1) ∧ *)
    always_same_args ((dn',vars1)::MAP (λ(x,y). (x, closure_args y)) fs1) e1 ∧
    always_same_args ((dn',vars2)::MAP (λ(x,y). (x, closure_args y)) fs2) e' ∧
    set(free_fun_names_endpoint e) ⊆ {dn} ∧
    saturates (written_var_names_endpoint e) e1 e' ∧
    (if shadow then
      e2 = e'
    else
      e2 = fsubst e' dn (Letrec dn vars e) ∧
      dn ≠ dn'
    )
      ∧
    ALL_DISTINCT vars1 ∧ ALL_DISTINCT vars2 ∧
    set vars = set(written_var_names_endpoint e) ∧
    set vars1 ⊆ set vars2 ∧
    set vars2 ⊆ set(written_var_names_endpoint e) ∪ set vars1 ∧
    (¬shadow ⇒
     ∃fs3 bds3.
        ALOOKUP fs1 dn = SOME(Closure vars (fs3,bds3) e) ∧
        (MEM dn (free_fun_names_endpoint e1) ⇒
         DRESTRICT bds3 (λk. ~MEM k vars) =
         DRESTRICT bds1 (λk. ~MEM k vars))
    ) ∧
    (∀dn'' ar1.
      (¬shadow ⇒ dn ≠ dn'') ∧ dn' ≠ dn'' ∧ MEM (dn'',ar1) (arities e1) ∧ MEM dn'' (free_fun_names_endpoint e1) ⇒
      ∃cl1 cl2. ALOOKUP fs1 dn'' = SOME cl1 ∧ ALOOKUP fs2 dn'' = SOME cl2 ∧
                arsof dn'' e' = {LENGTH(closure_args cl2)} ∧
                DRESTRICT (closure_var_env cl1) (λk. MEM k (closure_args cl2) ∧ ¬MEM k (closure_args cl1) (* ∧ ¬MEM k vars1 *) ) =
                DRESTRICT bds2 (λk. MEM k (closure_args cl2) ∧ ¬MEM k (closure_args cl1) (*∧ ¬MEM k vars1*) ) ∧
                set(written_var_names_endpoint_before dn'' e1) ⊆ set(closure_args cl1) ∧
                set vars1 ⊆ set(closure_args cl1) ∧
                (ALOOKUP fs1 dn'' = SOME cl1 ∧ ALOOKUP fs2 dn'' = SOME cl2 ⇒
                 compile_fix_closure_rel dn e vars dn'' cl1 cl2))
Termination
  WF_REL_TAC ‘inv_image $< (closure_size o FST o SND o SND o SND o SND)’ >>
  rw[closure_size_def] >> imp_res_tac ALOOKUP_MEM >>
  imp_res_tac closure_size_MEM >>
  DECIDE_TAC
End

Definition compile_fix_closure_endpoint_rel_def:
  compile_fix_closure_endpoint_rel vars dn e n1 n2 ⇔
  ∃shadow p s1 s2 e1 e2 e'.
    s1.queues = s2.queues ∧
    s1.bindings = s2.bindings ∧
    n1 = NEndpoint p s1 e1 ∧
    n2 = NEndpoint p s2 e2 ∧
    (if shadow then
       e' = e2
     else
        e2 = fsubst e' dn (Letrec dn vars e)) ∧
    saturates (written_var_names_endpoint e) e1 e' ∧
    letrec_endpoint e ∧ letrec_endpoint e1 ∧ letrec_endpoint e' ∧
    consistent_arities e ∧ consistent_arities e1 ∧
    consistent_arities e' ∧
    arsof dn e ⊆ {LENGTH vars} ∧
    good_letrecs (MAP (λ(x,y). (x, closure_args y)) s1.funs) e1 ∧
    set vars = set(written_var_names_endpoint e) ∧
    set(written_var_names_endpoint e) (* DIFF set vars *) ⊆ FDOM s2.bindings ∧
    (¬shadow ⇒ set(written_var_names_endpoint_before dn e1) ⊆ set vars) ∧
    set(free_fun_names_endpoint e) ⊆ {dn} ∧
    set(written_var_names_endpoint e') ⊆ set(written_var_names_endpoint e) ∧
    ALL_DISTINCT vars ∧
    (*¬MEM dn (bound_fun_names_endpoint e1) ∧*)
    always_same_args (MAP (λ(x,y). (x, closure_args y)) s1.funs) e1 ∧
    always_same_args (MAP (λ(x,y). (x, closure_args y)) s2.funs) e' ∧
    (¬shadow ⇒
     ∃fs3 bds3.
     ALOOKUP s1.funs dn = SOME(Closure vars (fs3,bds3) e) ∧
      (MEM dn (free_fun_names_endpoint e1) ⇒
       DRESTRICT s1.bindings (λk. ~MEM k vars) =
       DRESTRICT bds3 (λk. ~MEM k vars))
    ) ∧
    (∀dn' ar1.
      (¬shadow ⇒ dn ≠ dn') ∧ MEM (dn',ar1) (arities e1) ∧ MEM dn' (free_fun_names_endpoint e1) ⇒
      ∃cl1 cl2. ALOOKUP s1.funs dn' = SOME cl1 ∧ ALOOKUP s2.funs dn' = SOME cl2 ∧
                DRESTRICT (closure_var_env cl1) (λk. MEM k (closure_args cl2) ∧ ¬MEM k (closure_args cl1)) =
                DRESTRICT s2.bindings (λk. MEM k (closure_args cl2) ∧ ¬MEM k (closure_args cl1)) ∧
                set(written_var_names_endpoint_before dn' e1) ⊆ set(closure_args cl1) ∧
                arsof dn' e' = {LENGTH(closure_args cl2)} ∧
                compile_fix_closure_rel dn e vars dn' cl1 cl2)
End

Theorem compile_fix_closure_rel_closure_args:
  compile_fix_closure_rel dn e vars dn' cl1 cl2 ⇒
  set(closure_args cl1) ⊆ set(closure_args cl2) ∧
  set(closure_args cl2) ⊆ set(written_var_names_endpoint e) ∪ set(closure_args cl1)
Proof
  MAP_EVERY Cases_on [‘cl1’,‘cl2’] >>
  rename1 ‘compile_fix_closure_rel _ _ _ _ (Closure _ p1 _) (Closure _ p2 _)’ >>
  MAP_EVERY Cases_on [‘p1’,‘p2’] >>
  rw[compile_fix_closure_rel_def,closure_args_def] >> fs[]
QED

Theorem written_var_names_endpoint_before_fresh_eq_NIL:
  ∀dn e.
  ~MEM dn (free_fun_names_endpoint e) ⇒
  written_var_names_endpoint_before dn e = []
Proof
  strip_tac >> Induct >> fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
  rw[] >>
  fs[MEM_FILTER] >> rveq >> fs[]
QED

Theorem NOT_free_fun_names_endpoint_arsof:
  ~MEM dn (free_fun_names_endpoint e) ⇒
  arsof dn e = {}
Proof
  Induct_on ‘e’ >> rw[free_fun_names_endpoint_def] >>
  rw[arsof_def,arities_def,FILTER_EQ_NIL,EVERY_MEM] >>
  res_tac >> fs[arsof_def,arities_def,FILTER_EQ_NIL,EVERY_MEM,MEM_FILTER] >>
  rveq >> fs[]
QED

Theorem saturates_free_fun_names_endpoint:
  ∀vars e1 e2.
  saturates vars e1 e2 ⇒
  free_fun_names_endpoint e1 = free_fun_names_endpoint e2
Proof
  ho_match_mp_tac saturates_ind >>
  rw[free_fun_names_endpoint_def]
QED

Theorem saturates_written_var_names_endpoint:
  ∀vars e1 e2.
  saturates vars e1 e2 ⇒
  set(written_var_names_endpoint e1) ⊆ set(written_var_names_endpoint e2)
Proof
  ho_match_mp_tac saturates_ind >>
  rw[written_var_names_endpoint_def] >>
  fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[]
QED

Theorem saturates_written_var_names_endpoint':
  ∀vars e1 e2.
  saturates vars e1 e2 ⇒
  set(written_var_names_endpoint e2) ⊆ set(written_var_names_endpoint e1) ∪ set vars
Proof
  ho_match_mp_tac saturates_ind >>
  rw[written_var_names_endpoint_def] >>
  fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[]
QED

Theorem arsof_lemma:
  ∀dn l e funs.
  MEM dn (free_fun_names_endpoint e) ∧
  always_same_args funs e ∧
  ALOOKUP funs dn = SOME l ⇒
  arsof dn e = {LENGTH l}
Proof
  ntac 2 GEN_TAC >> Induct >>
  rw[free_fun_names_endpoint_def,always_same_args_def] >>
  res_tac >>
  TRY(Cases_on ‘MEM dn (free_fun_names_endpoint e')’ >> fs[] >>
      fs[NOT_free_fun_names_endpoint_arsof] >> NO_TAC) >>
  TRY(Cases_on ‘MEM dn (free_fun_names_endpoint e)’ >> fs[] >>
      fs[NOT_free_fun_names_endpoint_arsof] >> NO_TAC) >>
  fs[arsof_def,arities_def] >>
  fs[MEM_FILTER] >>
  rfs[] >>
  fs[o_DEF] >>
  fs[FILTER_FILTER,FILTER_APPEND] >>
  ‘(λx:string#num. dn = FST x ∧ s ≠ FST x) = (λx. dn = FST x)’ by(rw[FUN_EQ_THM,EQ_IMP_THM] >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  fs[] >>
  fs[IMP_DISJ_THM] >>
  imp_res_tac NOT_free_fun_names_endpoint_arsof >>
  fs[arsof_def,FILTER_EQ_NIL,EVERY_MEM] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF] >>
  fs[MEM_MAP,MEM_FILTER] >>
  rveq >>
  metis_tac[]
QED

Theorem written_var_names_endpoint_lemma:
  ∀dn l e funs.
  MEM dn (free_fun_names_endpoint e) ∧
  always_same_args funs e ∧
  ALOOKUP funs dn = SOME l ⇒
  set l ⊆ set(written_var_names_endpoint e)
Proof
  ntac 2 GEN_TAC >> Induct >>
  rw[free_fun_names_endpoint_def,always_same_args_def,written_var_names_endpoint_def] >>
  res_tac >>
  fs[SUBSET_INSERT_RIGHT] >>
  fs[MEM_FILTER] >>
  rfs[] >>
  rw[SUBSET_DEF] >> imp_res_tac SUBSET_THM >> simp[]
QED

Theorem written_var_names_endpoint_before_lemma:
  ∀dn l e funs.
  MEM dn (free_fun_names_endpoint e) ∧
  always_same_args funs e ∧
  ALOOKUP funs dn = SOME l ⇒
  set l ⊆ set(written_var_names_endpoint_before dn e)
Proof
  ntac 2 GEN_TAC >> Induct >>
  rw[free_fun_names_endpoint_def,always_same_args_def,written_var_names_endpoint_before_def] >>
  res_tac >>
  fs[SUBSET_INSERT_RIGHT] >>
  fs[MEM_FILTER] >>
  rfs[] >>
  rw[SUBSET_DEF] >> imp_res_tac SUBSET_THM >> simp[]
QED

Theorem free_fun_names_endpoint_compile_endpoint:
  ∀dn funs e. MEM dn (free_fun_names_endpoint (compile_endpoint funs e)) ⇒
           MEM dn (free_fix_names_endpoint e) ∧ MEM dn (MAP FST funs)
Proof
  strip_tac >> Induct_on ‘e’ >>
  rw[good_letrecs_def,compile_endpoint_def,free_fix_names_endpoint_def,free_fun_names_endpoint_def] >>
  TRY(res_tac >> fs[] >> NO_TAC) >>
  TRY(rename1 ‘FILTER’ >>
      fs[MEM_FILTER,EVERY_MEM] >>
      res_tac >> rveq >> fs[] >> rveq >> fs[] >> NO_TAC) >>
  FULL_CASE_TAC >> fs[free_fun_names_endpoint_def] >>
  imp_res_tac ALOOKUP_MEM >>
  rw[MEM_MAP] >>
  metis_tac[FST]
QED

Theorem written_var_names_endpoint_before_compile_endpoint:
  ∀x dn funs e vars.
    MEM x (written_var_names_endpoint_before dn (compile_endpoint funs e)) ∧
    ALOOKUP funs dn = SOME vars ∧
    set(written_var_names_endpoint e) ⊆ set vars ⇒
    MEM x vars
Proof
  ntac 2 strip_tac >> Induct_on ‘e’ >>
  rw[written_var_names_endpoint_before_def,compile_endpoint_def,written_var_names_endpoint_def] >>
  TRY(res_tac >> fs[] >> NO_TAC) >>
  FULL_CASE_TAC >> fs[written_var_names_endpoint_before_def] >>
  FULL_CASE_TAC >> fs[] >> rveq >> simp[]
QED

Theorem good_letrecs_compile_endpoint:
  ∀funs e.
        (∀dn vars. ALOOKUP funs dn = SOME vars ⇒ set(written_var_names_endpoint e) ⊆ set vars) ⇒
        good_letrecs funs (compile_endpoint funs e)
Proof
  Induct_on ‘e’ >>
  rw[good_letrecs_def,compile_endpoint_def,free_fun_names_endpoint_def,
     written_var_names_endpoint_before_def,
     written_var_names_endpoint_def,IMP_CONJ_THM,FORALL_AND_THM] >>
  TRY(first_x_assum match_mp_tac >>
      rw[] >> rw[set_nub'] >> res_tac >> NO_TAC) >>
  TRY(imp_res_tac free_fun_names_endpoint_compile_endpoint >>
      fs[] >> rveq >>
      res_tac >> fs[set_nub'] >> NO_TAC) >>
  TRY(rw[SUBSET_DEF,set_nub'] >>
      drule written_var_names_endpoint_before_compile_endpoint >>
      simp[set_nub'] >> NO_TAC) >>
  TOP_CASE_TAC >> simp[good_letrecs_def]
QED

Theorem arities_compile_endpoint_IMP:
  ∀dn l funs e.
  MEM (dn,l) (arities (compile_endpoint funs e)) ⇒
  (∃vars. ALOOKUP funs dn = SOME vars ∧ l = LENGTH vars ∧ MEM dn (free_fix_names_endpoint e))
Proof
  ntac 2 strip_tac >> Induct_on ‘e’ >>
  rw[arities_def,free_fix_names_endpoint_def,compile_endpoint_def,MEM_FILTER]
  >- metis_tac[]
  >- metis_tac[]
  >- (res_tac >> fs[CaseEq "bool"] >> rveq >> fs[])
  >- (FULL_CASE_TAC >> fs[arities_def])
QED

Theorem IMP_arities_compile_endpoint:
  ∀dn vars funs e.
  ALOOKUP funs dn = SOME vars ∧ MEM dn (free_fix_names_endpoint e) ∧ fix_endpoint e ⇒
  MEM (dn,LENGTH vars) (arities (compile_endpoint funs e))
Proof
  ntac 2 strip_tac >> Induct_on ‘e’ >>
  rw[arities_def,free_fix_names_endpoint_def,compile_endpoint_def,MEM_FILTER,fix_endpoint_def]
  >- metis_tac[]
  >- metis_tac[]
  >- simp[arities_def]
QED

Theorem arities_compile_endpoint_eq:
  ∀dn l funs e.
  fix_endpoint e ⇒
  (MEM (dn,l) (arities (compile_endpoint funs e)) ⇔
   (∃vars. ALOOKUP funs dn = SOME vars ∧ l = LENGTH vars ∧ MEM dn (free_fix_names_endpoint e)))
Proof
  metis_tac[IMP_arities_compile_endpoint,arities_compile_endpoint_IMP]
QED

Theorem compile_endpoint_always_same_args:
  ∀funs e. always_same_args funs (compile_endpoint funs e)
Proof
  Induct_on ‘e’ >> rw[compile_endpoint_def,always_same_args_def] >>
  TOP_CASE_TAC >> rw[always_same_args_def]
QED

Theorem arsof_compile_endpoint_SUBSET:
  ∀dn vars funs e.
    ALOOKUP funs dn = SOME vars ⇒
    arsof dn (compile_endpoint funs e) ⊆ {LENGTH vars}
Proof
  rpt strip_tac >>
  rw[arsof_def,SUBSET_DEF,MEM_FILTER,MEM_MAP] >>
  rename1 ‘MEM pair (arities _)’ >>
  Cases_on ‘pair’ >>
  imp_res_tac arities_compile_endpoint_IMP >>
  fs[]
QED

Theorem always_same_args_fsubst_lemma:
  ∀dn e' funs e.
    always_same_args funs (fsubst e dn e') ∧
    ~MEM dn (MAP FST funs) ⇒
    always_same_args funs e
Proof
  ntac 2 strip_tac >>
  Induct_on ‘e’ >> rw[always_same_args_def,fsubst_def] >>
  TOP_CASE_TAC >> imp_res_tac ALOOKUP_MEM >>
  metis_tac[MEM_MAP,FST]
QED

Theorem bisim_defer_fundef:
  ∀conf dn e vars n1 n2.
    compile_fix_closure_endpoint_rel vars dn e n1 n2 ⇒
    BISIM_REL (trans conf) n1 n2
Proof
  ntac 4 strip_tac >>
  ho_match_mp_tac BISIM_REL_strong_coind >> rw[]
  >- ((* LHS leads *)
      qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[Once trans_cases]) >>
      fs[] >> rveq
      >- ((* trans_send_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          reverse(Cases_on ‘shadow’) >-
            (fs[] >> rveq >> fs[] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
                written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             metis_tac[]) >>
          fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_send_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          reverse(Cases_on ‘shadow’) >-
            (fs[] >> rveq >> fs[] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >>
             rw[Once saturates_cases,PULL_EXISTS] >>
             rw[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
                written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             metis_tac[]) >>
          fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          simp[Once saturates_cases,PULL_EXISTS] >>
          rw[fsubst_def] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_enqueue *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >-
            (fs[] >> rveq >> fs[] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_enqueue) >>
             simp[] >>
             disj1_tac >> fs[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             metis_tac[]) >>
          fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_enqueue) >>
          simp[] >>
          disj1_tac >> fs[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          metis_tac[])
      >- ((* trans_com_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_com_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_dequeue_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
             fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
                written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
                good_letrecs_def] >>
             conj_tac >- (fs[SUBSET_DEF]) >>
             conj_tac >-
              (PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> rfs[]) >>
             conj_tac >- (fs[] >> rfs[]) >>
             rpt strip_tac >>
             first_x_assum(drule_all_then strip_assume_tac) >>
             rpt(goal_assum drule) >> rw[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
          fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
             good_letrecs_def] >>
          conj_tac >- fs[SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_dequeue_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
            simp[Once saturates_cases] >>
            simp[PULL_EXISTS,fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def] >>
            fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,written_var_names_endpoint_def,good_letrecs_def] >>
            metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
          simp[Once saturates_cases] >>
          simp[PULL_EXISTS,fsubst_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,written_var_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_if_true *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def] >>
            fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
            fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            conj_tac >- (rfs[]) >>
            conj_tac >- (metis_tac[]) >>
            rw[] >>
            res_tac >>
            drule_all_then strip_assume_tac MEM_arities_saturates >>
            imp_res_tac MEM_arities_arsof >>
            fs[] >>
            fs[SET_EQ_SUBSET,SUBSET_DEF] >>
            metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          fs[RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >- metis_tac[] >>
          rpt(goal_assum drule) >>
          simp[] >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_if_false *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def] >>
            fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
            fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            conj_tac >- (rfs[]) >>
            conj_tac >- (metis_tac[]) >>
            rw[] >>
            res_tac >>
            drule_all_then strip_assume_tac MEM_arities_saturates >>
            imp_res_tac MEM_arities_arsof >>
            fs[] >>
            fs[SET_EQ_SUBSET,SUBSET_DEF] >>
            metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          fs[RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >>
          rpt(goal_assum drule) >>
          simp[] >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_let *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
            fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
               written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
               good_letrecs_def] >>
            conj_tac >- (fs[SUBSET_DEF]) >>
            conj_tac >-
             (PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> rfs[]) >>
            rpt strip_tac >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rpt(goal_assum drule) >> rw[] >> rfs[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
          fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
             good_letrecs_def] >>
          conj_tac >- fs[SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_par_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_par_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_fix (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def,letrec_endpoint_def])
      >- ((* trans_letrec *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             IF_CASES_TAC >-
              (rveq >> fs[free_fun_names_endpoint_def,MEM_FILTER,bound_fun_names_endpoint_def] >>
               goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
               conj_tac
               >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
                   drule_all SUBSET_THM >> rw[] >> fs[] >>
                   drule_all SUBSET_THM >>
                   rw[FDOM_FLOOKUP]) >>
               disj1_tac >>
               simp[compile_fix_closure_endpoint_rel_def] >>
               qexists_tac ‘T’ >>
               simp[] >>
               fs[letrec_endpoint_def] >>
               fs[consistent_arities_def] >>
               fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                  always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
               fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
               fs[closure_args_def] >>
               rpt strip_tac >> fs[] >>
               IF_CASES_TAC >-
                 (fs[closure_args_def,closure_var_env_def] >> rveq >>
                  conj_asm1_tac >-
                    (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                     drule_all_then strip_assume_tac MEM_arities_saturates >>
                     qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
                     strip_tac >> rveq >>
                     drule arsof_lemma >>
                     disch_then drule >>
                     simp[]) >>
                  simp[compile_fix_closure_rel_def] >>
                  rpt strip_tac >>
                  first_x_assum drule_all >>
                  strip_tac >>
                  rpt(goal_assum drule) >>
                  simp[] >>
                  conj_tac >-
                    (qpat_x_assum ‘saturates _ e1 _’ assume_tac >>
                     drule_then (fs o single) saturates_free_fun_names_endpoint >>
                     drule arsof_lemma >>
                     disch_then drule >>
                     simp[ALOOKUP_MAP]) >>
                  last_x_assum(drule_then match_mp_tac) >>
                  simp[ALOOKUP_MAP,closure_args_def]) >>
               simp[] >>
               first_x_assum(drule_all_then strip_assume_tac) >>
               rpt(goal_assum drule) >>
               simp[] >>
               drule_then (fs o single) saturates_free_fun_names_endpoint >>
               drule arsof_lemma >>
               disch_then drule >>
               simp[ALOOKUP_MAP]) >>
             rveq >>
             fs[free_fun_names_endpoint_def,MEM_FILTER] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
             conj_tac
             >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
                 drule_all SUBSET_THM >> rw[] >> fs[] >>
                 drule_all SUBSET_THM >>
                 rw[FDOM_FLOOKUP]) >>
             disj1_tac >>
             simp[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def] >>
             fs[consistent_arities_def] >>
             fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
             conj_tac >- (fs[closure_args_def]) >>
             conj_tac >- (rfs[]) >>
             conj_tac >- (rw[closure_args_def]) >>
             conj_tac >- (rw[closure_args_def]) >>
             conj_tac >- metis_tac[] >>
             rw[closure_var_env_def,closure_args_def]
             >- (fs[] >> rfs[])
             >- (fs[arsof_def,closure_args_def,MEM_FILTER] >>
                 imp_res_tac MEM_arities_saturates >>
                 rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
                 metis_tac[PAIR,FST,SND])
             >- (simp[compile_fix_closure_rel_def] >>
                 qexists_tac ‘F’ >> simp[] >>
                 goal_assum(resolve_then (Pos hd) mp_tac letrec_endpoint_fsubst) >>
                 simp[letrec_endpoint_def] >>
                 goal_assum(resolve_then (Pat ‘fsubst _ _ _ = fsubst _ _ _’) mp_tac EQ_REFL) >>
                 simp[GSYM PULL_EXISTS] >>
                 rw[] >>
                 first_x_assum (drule_all_then strip_assume_tac) >>
                 simp[] >- rfs[] >>
                 conj_tac >- rfs[arsof_letrec_lemma] >>
                 last_x_assum(drule_then match_mp_tac) >>
                 simp[ALOOKUP_MAP,PULL_EXISTS]) >>
             first_x_assum(drule_all_then strip_assume_tac) >>
             rpt(goal_assum drule) >>
             simp[] >>
             rfs[arsof_letrec_lemma]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          rveq >> fs[free_fun_names_endpoint_def,MEM_FILTER,bound_fun_names_endpoint_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
          conj_tac
          >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
              drule_all SUBSET_THM >> rw[] >> fs[] >>
              drule_all SUBSET_THM >>
              rw[FDOM_FLOOKUP]) >>
          disj1_tac >>
          simp[compile_fix_closure_endpoint_rel_def] >>
          Cases_on ‘dn = dn'’ >-
           (rveq >>
            qexists_tac ‘T’ >> simp[] >>
            fs[letrec_endpoint_def] >>
            fs[consistent_arities_def] >>
            fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            fs[closure_args_def] >>
            rpt strip_tac >>
            IF_CASES_TAC >-
              (fs[closure_args_def,closure_var_env_def] >> rveq >>
               conj_asm1_tac >-
                (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule_all_then strip_assume_tac MEM_arities_saturates >>
                 qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
                 strip_tac >> rveq >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[]) >>
               simp[compile_fix_closure_rel_def] >>
               rpt strip_tac >>
               first_x_assum drule_all >>
               strip_tac >>
               rpt(goal_assum drule) >>
               simp[] >>
               conj_tac >-
                (qpat_x_assum ‘saturates _ e1 _’ assume_tac >>
                 drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[ALOOKUP_MAP]) >>
               last_x_assum(drule_then match_mp_tac) >>
               simp[ALOOKUP_MAP,closure_args_def]) >>
            simp[] >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rpt(goal_assum drule) >>
            simp[] >>
            drule_then (fs o single) saturates_free_fun_names_endpoint >>
            drule arsof_lemma >>
            disch_then drule >>
            simp[ALOOKUP_MAP]) >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def] >>
          fs[consistent_arities_def] >>
          fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[closure_args_def] >>
          rpt strip_tac >>
          IF_CASES_TAC >-
           (fs[closure_args_def,closure_var_env_def] >> rveq >>
            conj_asm1_tac >-
             (drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule_all_then strip_assume_tac MEM_arities_saturates >>
              qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
              strip_tac >> rveq >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[]) >>
            simp[compile_fix_closure_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            rpt strip_tac >>
            first_x_assum drule_all >>
            strip_tac >>
            rpt(goal_assum drule) >>
            simp[] >>
            conj_tac >-
             (qpat_x_assum ‘saturates _ e1 _’ assume_tac >>
              drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[ALOOKUP_MAP]) >>
            last_x_assum(drule_then match_mp_tac) >>
            simp[ALOOKUP_MAP,closure_args_def]) >>
          simp[] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          rpt(goal_assum drule) >>
          simp[] >>
          drule_then (fs o single) saturates_free_fun_names_endpoint >>
          drule arsof_lemma >>
          disch_then drule >>
          simp[ALOOKUP_MAP])
      >- ((* trans_call *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            IF_CASES_TAC
            >- ((* Actual call to dn *)
                rveq >>
                fs[] >> rveq >> fs[] >>
                simp[Once trans_cases] >>
                fs[written_var_names_endpoint_before_def] >>
                fs[always_same_args_def,bound_fun_names_endpoint_def,ALOOKUP_MAP,closure_args_def] >>
                rveq >> fs[] >>
                disj2_tac >>
                ‘bds3 |++ ZIP (args,MAP (THE ∘ FLOOKUP s2.bindings) args) =
                 s2.bindings |++ ZIP (args,MAP (THE ∘ FLOOKUP s2.bindings) args)’
                  by(fs[free_fun_names_endpoint_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,
                        flookup_fupdate_list] >>
                     rw[] >> TOP_CASE_TAC >>
                     fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                     metis_tac[]) >>
                pop_assum SUBST_ALL_TAC >>
                ‘BISIM_REL (trans conf)
                   (NEndpoint p
                              (s with <|bindings := s2.bindings |++ ZIP (args,MAP (THE ∘ FLOOKUP s2.bindings) args);
                                        funs := (dn,Closure args (fs3,bds3) e)::fs3|>)
                              e)
                   (NEndpoint p
                              (s with <|bindings := s2.bindings |++ ZIP (args,MAP (THE ∘ FLOOKUP s2.bindings) args);
                                        funs := [(dn,Closure args ([],bds3) e)]|>)
                              e)
                        ’
                  by(match_mp_tac bisim_used_closures_rel >>
                     simp[used_closures_rel_def,used_closures_endpoint_rel_def] >>
                     Q.REFINE_EXISTS_TAC ‘(s:closure state) with bindings := _’ >>
                     simp[state_component_equality] >>
                     rpt strip_tac >>
                     drule_all SUBSET_THM >> rw[] >>
                     rw[used_closures_rel_def] >>
                     drule_all SUBSET_THM >> rw[]) >>
                dxrule_then match_mp_tac bisim_trans >>
                ‘BISIM_REL (trans conf)
                   (NEndpoint p
                              (s2 with <|funs := [(dn,Closure args ([],s2.bindings) e)]|>)
                              e)
                   (NEndpoint p
                              (s2 with <|funs := (dn,Closure args (s2.funs,s2.bindings) e)::s2.funs|>)
                              e)
                        ’
                  by(match_mp_tac bisim_used_closures_rel >>
                     simp[used_closures_rel_def,used_closures_endpoint_rel_def] >>
                     simp[state_component_equality] >>
                     goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
                     simp[] >>
                     rpt strip_tac >>
                     drule_all SUBSET_THM >> rw[] >>
                     rw[used_closures_rel_def] >>
                     drule_all SUBSET_THM >> rw[]) >>
                first_x_assum(fn thm => resolve_then (Pos last) match_mp_tac thm bisim_trans) >>
                match_mp_tac junkcong_bisim >>
                goal_assum(resolve_then (Pos hd) mp_tac junkcong_trans) >>
                goal_assum(resolve_then (Pos hd) mp_tac junkcong_DRESTRICT_closure_hd') >>
                rfs[free_fun_names_endpoint_def] >>
                match_mp_tac junkcong_sym >>
                goal_assum(resolve_then (Pos hd) mp_tac junkcong_trans) >>
                goal_assum(resolve_then (Pos hd) mp_tac junkcong_DRESTRICT_closure_hd) >>
                match_mp_tac junkcong_refl_IMP >>
                AP_THM_TAC >> AP_TERM_TAC >>
                rw[state_component_equality] >>
                simp[fmap_eq_flookup,flookup_fupdate_list] >>
                strip_tac >>
                TOP_CASE_TAC >>
                fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >>
                fs[ALOOKUP_ZIP_SELF] >> rveq >>
                rfs[] >>
                drule_all SUBSET_THM >>
                rw[FDOM_FLOOKUP] >> rw[]) >>
            (* Call to something else *)
            goal_assum(resolve_then (Pos hd) mp_tac trans_call) >>
            fs[arities_def,free_fun_names_endpoint_def] >>
            Cases_on ‘cl2’ >> rveq >> fs[closure_args_def] >>
            fs[written_var_names_endpoint_before_def] >>
            rename1 ‘pair = (_,_)’ >> Cases_on ‘pair’ >> fs[] >>
            conj_tac
            >- (rw[EVERY_MEM,IS_SOME_EXISTS] >>
                fs[written_var_names_endpoint_def] >>
                imp_res_tac SUBSET_THM >>
                fs[FDOM_FLOOKUP]) >>
            rveq >> fs[written_var_names_endpoint_def,bound_fun_names_endpoint_def,free_fun_names_endpoint_def,
                       closure_args_def,closure_var_env_def,always_same_args_def,ALOOKUP_MAP] >>
            rveq >> fs[] >>
            disj1_tac >>
            qhdtm_x_assum ‘compile_fix_closure_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_rel_def]) >>
            rveq >> fs[] >>
            reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
              (simp[compile_fix_closure_endpoint_rel_def] >>
               qexists_tac ‘F’ >>
               simp[GSYM PULL_EXISTS] >>
               conj_asm1_tac >-
                 (simp[fmap_eq_flookup] >>
                  rw[flookup_fupdate_list] >>
                  TOP_CASE_TAC >-
                   (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                    rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                    fs[ALOOKUP_ZIP_MAP_SND] >>
                    rveq >>
                    fs[ALOOKUP_ZIP_SELF] >> rveq >>
                    rw[] >>
                    qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
                    rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                    pop_assum(qspec_then ‘x’ mp_tac) >>
                    rw[] >>
                    drule_all_then strip_assume_tac SUBSET_THM >>
                    drule_all_then strip_assume_tac SUBSET_THM >>
                    rfs[FDOM_FLOOKUP]) >>
                  rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                  fs[ALOOKUP_ZIP_MAP_SND] >>
                  rveq >>
                  fs[ALOOKUP_ZIP_SELF] >> rveq >>
                  drule_all_then strip_assume_tac SUBSET_THM >>
                  simp[]) >>
               goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
               imp_res_tac letrec_endpoint_fsubst' >>
               simp[closure_args_def] >>
               simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
               simp[GSYM PULL_EXISTS] >>
               conj_tac >- fs[SUBSET_DEF] >>
               conj_tac >- rfs[] >>
               conj_tac >-
                (rw[] >> fs[] >> rfs[] >>
                 rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                 rw[] >>
                 rw[flookup_fupdate_list] >>
                 TOP_CASE_TAC >>
                 rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                 fs[ALOOKUP_ZIP_MAP_SND] >>
                 rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                 metis_tac[SUBSET_DEF]) >>
               simp[PULL_EXISTS] >>
               rw[closure_var_env_def,closure_args_def] >> rfs[]
               >- (rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                   rw[] >>
                   rw[flookup_fupdate_list] >>
                   TOP_CASE_TAC >>
                   rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                   fs[ALOOKUP_ZIP_MAP_SND] >>
                   rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                   drule_all_then strip_assume_tac SUBSET_THM >>
                   drule_all_then strip_assume_tac SUBSET_THM >>
                   fs[FDOM_FLOOKUP] >>
                   qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _’ mp_tac >>
                   rw[fmap_eq_flookup] >>
                   pop_assum(qspec_then ‘x’ mp_tac) >>
                   rw[FLOOKUP_DRESTRICT] >>
                   metis_tac[THE_DEF])
               >- (match_mp_tac arsof_lemma >>
                   goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                   simp[] >>
                   metis_tac[saturates_free_fun_names_endpoint])
               >- (rw[compile_fix_closure_rel_def] >>
                   qexists_tac ‘F’ >> simp[] >>
                   goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                   simp[] >>
                   rpt strip_tac >>
                   metis_tac[])
               >- (first_x_assum(drule_all_then strip_assume_tac) >>
                   rpt(goal_assum drule) >>
                   simp[] >>
                   rfs[] >>
                   qpat_x_assum ‘bindings |++ _ = bindings |++ _’ (fn thm => SUBST_ALL_TAC(GSYM thm) >> assume_tac(GSYM thm)) >>
                   rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                   rw[] >>
                   rw[flookup_fupdate_list] >>
                   TOP_CASE_TAC >>
                   rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                   fs[ALOOKUP_ZIP_MAP_SND] >>
                   rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                   drule_then drule written_var_names_endpoint_lemma >>
                   simp[ALOOKUP_MAP] >>
                   strip_tac >>
                   metis_tac[SUBSET_THM])) >>
            simp[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            conj_asm1_tac >-
             (simp[fmap_eq_flookup] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >-
               (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >>
                fs[ALOOKUP_ZIP_SELF] >> rveq >>
                rw[] >>
                qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[] >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                rfs[FDOM_FLOOKUP]) >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              simp[]) >>
            simp[closure_args_def] >>
            simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
            simp[GSYM PULL_EXISTS] >>
            conj_tac >- fs[SUBSET_DEF] >>
            rpt strip_tac >>
            IF_CASES_TAC >-
              (fs[closure_var_env_def,closure_args_def] >> rveq >>
               conj_asm1_tac >-
                 (qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _ ’ (assume_tac o GSYM) >>
                  simp[] >>
                  qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
                  rw[] >> fs[] >> rfs[] >>
                  rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                  rw[] >>
                  rw[flookup_fupdate_list] >>
                  TOP_CASE_TAC >>
                  rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                  fs[ALOOKUP_ZIP_MAP_SND] >>
                  rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq) >>
               conj_asm1_tac >-
                (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule_all_then strip_assume_tac MEM_arities_saturates >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[]) >>
               simp[compile_fix_closure_rel_def] >>
               qexists_tac ‘T’ >> simp[] >>
               rpt strip_tac >>
               first_x_assum drule_all >>
               strip_tac >>
               rpt(goal_assum drule) >>
               simp[]) >>
            simp[] >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rfs[] >>
            qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
            rw[] >> fs[] >> rfs[] >>
            rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
            rw[] >>
            rw[flookup_fupdate_list] >>
            TOP_CASE_TAC >>
            rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
            fs[ALOOKUP_ZIP_MAP_SND] >>
            rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
            metis_tac[SUBSET_DEF]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_call) >>
          fs[arities_def,free_fun_names_endpoint_def] >>
          Cases_on ‘cl2’ >> rveq >> fs[closure_args_def] >>
          fs[written_var_names_endpoint_before_def] >>
          rename1 ‘pair = (_,_)’ >> Cases_on ‘pair’ >> fs[] >>
          conj_tac
          >- (rw[EVERY_MEM,IS_SOME_EXISTS] >>
              fs[written_var_names_endpoint_def] >>
              imp_res_tac SUBSET_THM >>
              fs[FDOM_FLOOKUP]) >>
          rveq >> fs[written_var_names_endpoint_def,bound_fun_names_endpoint_def,free_fun_names_endpoint_def,
                       closure_args_def,closure_var_env_def,always_same_args_def,ALOOKUP_MAP] >>
          rveq >> fs[] >>
          disj1_tac >>
          qhdtm_x_assum ‘compile_fix_closure_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_rel_def]) >>
          rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (simp[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >>
            simp[GSYM PULL_EXISTS] >>
            conj_asm1_tac >-
             (simp[fmap_eq_flookup] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >-
               (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >>
                fs[ALOOKUP_ZIP_SELF] >> rveq >>
                rw[] >>
                qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[] >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                rfs[FDOM_FLOOKUP]) >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              simp[]) >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            imp_res_tac letrec_endpoint_fsubst' >>
            simp[closure_args_def] >>
            simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
            simp[GSYM PULL_EXISTS] >>
            conj_tac >- fs[SUBSET_DEF] >>
            conj_tac >- rfs[] >>
            conj_tac >-
             (rw[] >> fs[] >> rfs[] >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              rw[] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
              metis_tac[SUBSET_DEF]) >>
            simp[PULL_EXISTS] >>
            rw[closure_var_env_def,closure_args_def] >> rfs[]
            >- (rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                rw[] >>
                rw[flookup_fupdate_list] >>
                TOP_CASE_TAC >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                fs[FDOM_FLOOKUP] >>
                qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _’ mp_tac >>
                rw[fmap_eq_flookup] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[FLOOKUP_DRESTRICT] >>
                metis_tac[THE_DEF])
            >- (match_mp_tac arsof_lemma >>
                goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                simp[] >>
                metis_tac[saturates_free_fun_names_endpoint])
            >- (rw[compile_fix_closure_rel_def] >>
                qexists_tac ‘F’ >> simp[] >>
                goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                simp[] >>
                rpt strip_tac >>
                metis_tac[])
            >- (first_x_assum(drule_all_then strip_assume_tac) >>
                rpt(goal_assum drule) >>
                simp[] >>
                rfs[] >>
                qpat_x_assum ‘bindings |++ _ = bindings |++ _’ (fn thm => SUBST_ALL_TAC(GSYM thm) >> assume_tac(GSYM thm)) >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                rw[] >>
                rw[flookup_fupdate_list] >>
                TOP_CASE_TAC >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                drule_then drule written_var_names_endpoint_lemma >>
                simp[ALOOKUP_MAP] >>
                strip_tac >>
                metis_tac[SUBSET_THM])) >>
          simp[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          conj_asm1_tac >-
           (simp[fmap_eq_flookup] >>
            rw[flookup_fupdate_list] >>
            TOP_CASE_TAC >-
             (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              rw[] >>
              qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              pop_assum(qspec_then ‘x’ mp_tac) >>
              rw[] >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              rfs[FDOM_FLOOKUP]) >>
            rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
            fs[ALOOKUP_ZIP_MAP_SND] >>
            rveq >>
            fs[ALOOKUP_ZIP_SELF] >> rveq >>
            drule_all_then strip_assume_tac SUBSET_THM >>
            simp[]) >>
          simp[closure_args_def] >>
          simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
          simp[GSYM PULL_EXISTS] >>
          conj_tac >- fs[SUBSET_DEF] >>
          rpt strip_tac >>
          IF_CASES_TAC >-
           (fs[closure_var_env_def,closure_args_def] >> rveq >>
            conj_asm1_tac >-
             (qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _ ’ (assume_tac o GSYM) >>
              simp[] >>
              qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
              rw[] >> fs[] >> rfs[] >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              rw[] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq) >>
            conj_asm1_tac >-
             (drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule_all_then strip_assume_tac MEM_arities_saturates >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[]) >>
            simp[compile_fix_closure_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            rpt strip_tac >>
            first_x_assum drule_all >>
            strip_tac >>
            rpt(goal_assum drule) >>
            simp[]) >>
          simp[] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          rfs[] >>
          qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
          rw[] >> fs[] >> rfs[] >>
          rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
          rw[] >>
          rw[flookup_fupdate_list] >>
          TOP_CASE_TAC >>
          rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
          fs[ALOOKUP_ZIP_MAP_SND] >>
          rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
          metis_tac[SUBSET_DEF])
     )
  >- ((* RHS leads *)
      qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[Once trans_cases]) >>
      fs[] >> rveq
      >- ((* trans_send_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[CaseEq "bool"] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >-
            (fs[] >> rveq >> fs[] >>
             Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
             fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
                written_var_names_endpoint_def,free_fun_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             metis_tac[]) >>
          fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
             written_var_names_endpoint_def,free_fun_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_send_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[CaseEq "bool"] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >-
            (fs[] >> rveq >> fs[] >>
             Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
             fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >>
             rw[Once saturates_cases,PULL_EXISTS] >>
             rw[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
                written_var_names_endpoint_def,free_fun_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             metis_tac[]) >>
          fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >>
          rw[Once saturates_cases,PULL_EXISTS] >>
          rw[fsubst_def] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
             written_var_names_endpoint_def,free_fun_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_enqueue *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_enqueue) >>
          simp[] >>
          reverse(Cases_on ‘shadow’) >-
            (disj1_tac >> fs[compile_fix_closure_endpoint_rel_def,always_same_args_def,bound_fun_names_endpoint_def] >>
             qexists_tac ‘F’ >> simp[] >>
             metis_tac[]) >>
          disj1_tac >> fs[compile_fix_closure_endpoint_rel_def,always_same_args_def,bound_fun_names_endpoint_def] >>
          qexists_tac ‘T’ >> simp[] >>
          metis_tac[])
      >- ((* trans_com_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_com_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_dequeue_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[CaseEq "bool"] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
             fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
                written_var_names_endpoint_def,free_fun_names_endpoint_def,
                always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
             conj_tac >- (fs[SUBSET_DEF]) >>
             conj_tac >-
              (PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> rfs[]) >>
             conj_tac >- (fs[] >> rfs[]) >>
             rpt strip_tac >>
             first_x_assum(drule_all_then strip_assume_tac) >>
             rpt(goal_assum drule) >> rw[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
             written_var_names_endpoint_def,free_fun_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          conj_tac >- (fs[SUBSET_DEF]) >>
          metis_tac[])
      >- ((* trans_dequeue_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
             fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
             fs[] >>
             disj1_tac >>
             rw[compile_fix_closure_endpoint_rel_def] >>
             qexists_tac ‘F’ >> simp[] >>
             fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
             simp[Once saturates_cases] >>
             simp[PULL_EXISTS,fsubst_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
             fs[letrec_endpoint_def,consistent_arities_def] >>
             fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,written_var_names_endpoint_def,good_letrecs_def] >>
             metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
          simp[Once saturates_cases] >>
          simp[PULL_EXISTS,fsubst_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,written_var_names_endpoint_def,good_letrecs_def] >>
          metis_tac[])
      >- ((* trans_if_true *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (Cases_on ‘e'’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
            fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def] >>
            fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
            fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            conj_tac >- (rfs[]) >>
            conj_tac >- (metis_tac[]) >>
            rw[] >>
            res_tac >>
            drule_all_then strip_assume_tac MEM_arities_saturates >>
            imp_res_tac MEM_arities_arsof >>
            fs[] >>
            fs[SET_EQ_SUBSET,SUBSET_DEF] >>
            metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          fs[RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >- metis_tac[] >>
          rpt(goal_assum drule) >>
          simp[] >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_if_false *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (Cases_on ‘e'’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
            fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def] >>
            fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
            fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            conj_tac >- (rfs[]) >>
            conj_tac >- (metis_tac[]) >>
            rw[] >>
            res_tac >>
            drule_all_then strip_assume_tac MEM_arities_saturates >>
            imp_res_tac MEM_arities_arsof >>
            fs[] >>
            fs[SET_EQ_SUBSET,SUBSET_DEF] >>
            rveq >> metis_tac[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          fs[RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >>
          rpt(goal_assum drule) >>
          simp[] >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_let *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
            fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
            goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
            fs[] >>
            disj1_tac >>
            rw[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >> simp[] >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
            fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
               written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
               good_letrecs_def] >>
            conj_tac >- (fs[SUBSET_DEF]) >>
            conj_tac >-
             (PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> rfs[]) >>
            rpt strip_tac >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rpt(goal_assum drule) >> rw[] >> rfs[]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def] >>
          fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,always_same_args_def,bound_fun_names_endpoint_def,
             good_letrecs_def] >>
          conj_tac >- fs[SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_par_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_par_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_fix (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def] >>
          Cases_on ‘shadow’ >> fs[] >> rveq >> fs[letrec_endpoint_def] >>
          Cases_on ‘e''’ >> fs[letrec_endpoint_def,fsubst_def] >>
          every_case_tac >> fs[])
      >- ((* trans_letrec *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq
             >- ((* letrec but it's dn (shadow case) *)
                 fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
                 rveq >> fs[free_fun_names_endpoint_def,MEM_FILTER,bound_fun_names_endpoint_def] >>
                 goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
                 conj_tac
                 >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
                     fs[written_var_names_endpoint_def] >>
                     drule_all SUBSET_THM >>
                     fs[FDOM_FLOOKUP]) >>
                 disj1_tac >>
                 simp[compile_fix_closure_endpoint_rel_def] >>
                 qexists_tac ‘T’ >>
                 simp[] >>
                 fs[letrec_endpoint_def] >>
                 fs[consistent_arities_def] >>
                 fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                    always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
                 fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
                 fs[closure_args_def] >>
                 rpt strip_tac >> fs[] >>
                 IF_CASES_TAC >-
                  (fs[closure_args_def,closure_var_env_def] >> rveq >>
                   conj_asm1_tac >-
                    (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                     drule_all_then strip_assume_tac MEM_arities_saturates >>
                     qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
                     strip_tac >> rveq >>
                     drule arsof_lemma >>
                     disch_then drule >>
                     simp[]) >>
                   simp[compile_fix_closure_rel_def] >>
                   rpt strip_tac >>
                   first_x_assum drule_all >>
                   strip_tac >>
                   rpt(goal_assum drule) >>
                   simp[] >>
                   conj_tac >-
                    (qpat_x_assum ‘saturates _ e1 _’ assume_tac >>
                     drule_then (fs o single) saturates_free_fun_names_endpoint >>
                     drule arsof_lemma >>
                     disch_then drule >>
                     simp[ALOOKUP_MAP]) >>
                   last_x_assum(drule_then match_mp_tac) >>
                   simp[ALOOKUP_MAP,closure_args_def]) >>
                 simp[] >>
                 first_x_assum(drule_all_then strip_assume_tac) >>
                 rpt(goal_assum drule) >>
                 simp[] >>
                 qpat_x_assum ‘saturates _ e2 _’ assume_tac >>
                 drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[ALOOKUP_MAP])
             >- ((* letrec but not dn (non-shadowed case) *)
                 fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
                 fs[free_fun_names_endpoint_def,MEM_FILTER] >>
                 goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
                 conj_tac
                 >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
                     fs[written_var_names_endpoint_def] >>
                     drule_all SUBSET_THM >>
                     fs[FDOM_FLOOKUP]) >>
                 disj1_tac >>
                 simp[compile_fix_closure_endpoint_rel_def] >>
                 qexists_tac ‘F’ >> simp[] >>
                 goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
                 fs[letrec_endpoint_def] >>
                 fs[consistent_arities_def] >>
                 fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
                    always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
                 fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
                 conj_tac >- (fs[closure_args_def]) >>
                 conj_tac >- (rfs[]) >>
                 conj_tac >- (rw[closure_args_def]) >>
                 conj_tac >- (rw[closure_args_def]) >>
                 conj_tac >- metis_tac[] >>
                 rw[closure_var_env_def,closure_args_def]
                 >- (fs[] >> rfs[])
                 >- (fs[arsof_def,closure_args_def,MEM_FILTER] >>
                     imp_res_tac MEM_arities_saturates >>
                     rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
                     metis_tac[PAIR,FST,SND])
                 >- (simp[compile_fix_closure_rel_def] >>
                     qexists_tac ‘F’ >> simp[] >>
                     goal_assum(resolve_then (Pos hd) mp_tac letrec_endpoint_fsubst) >>
                     simp[letrec_endpoint_def] >>
                     goal_assum(resolve_then (Pat ‘fsubst _ _ _ = fsubst _ _ _’) mp_tac EQ_REFL) >>
                     simp[GSYM PULL_EXISTS] >>
                     rw[] >>
                     first_x_assum (drule_all_then strip_assume_tac) >>
                     simp[]
                     >- rfs[]
                     >- (fs[] >> rfs[]) >>
                     conj_tac >-
                      (rfs[arsof_letrec_lemma]) >>
                     last_x_assum(drule_then match_mp_tac) >>
                     simp[ALOOKUP_MAP,PULL_EXISTS]) >>
                 first_x_assum(drule_all_then strip_assume_tac) >>
                 rpt(goal_assum drule) >>
                 simp[] >>
                 rfs[arsof_letrec_lemma])
             >- ((* actual call to dn *)
                 fs[Once saturates_cases] >> rveq >> fs[] >>
                 goal_assum(resolve_then (Pos hd) mp_tac trans_call) >>
                 fs[always_same_args_def,ALOOKUP_MAP,closure_args_def] >>
                 rveq >> fs[] >>
                 disj2_tac >>
                 simp[] >>
                 ‘bds3 |++ ZIP (vars,MAP (THE ∘ FLOOKUP s.bindings) vars) = s.bindings’
                   by(fs[free_fun_names_endpoint_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,
                         flookup_fupdate_list] >>
                      rw[] >> TOP_CASE_TAC >>
                      fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >- metis_tac[] >>
                      imp_res_tac ALOOKUP_MEM >>
                      fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                      rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                      fs[ALOOKUP_ZIP_MAP_SND] >>
                      rveq >>
                      fs[ALOOKUP_ZIP_SELF] >> rveq >>
                      rfs[] >>
                      drule_all SUBSET_THM >>
                      rw[FDOM_FLOOKUP] >> rw[]) >>
                 pop_assum SUBST_ALL_TAC >>
                 ‘BISIM_REL (trans conf)
                   (NEndpoint p
                              (s1 with <|bindings := s.bindings;
                                        funs := (dn,Closure vars (fs3,bds3) e)::fs3|>)
                              e)
                   (NEndpoint p
                              (s with <|bindings := s.bindings;
                                        funs := [(dn,Closure vars ([],bds3) e)]|>)
                              e)
                        ’
                   by(match_mp_tac bisim_used_closures_rel >>
                      simp[used_closures_rel_def,used_closures_endpoint_rel_def] >>
                      Q.REFINE_EXISTS_TAC ‘(s:closure state) with bindings := _’ >>
                      simp[state_component_equality] >>
                      rpt strip_tac >>
                      drule_all SUBSET_THM >> rw[] >>
                      rw[used_closures_rel_def] >>
                      drule_all SUBSET_THM >> rw[]) >>
                 dxrule_then match_mp_tac bisim_trans >>
                 ‘BISIM_REL (trans conf)
                   (NEndpoint p
                              (s with <|funs := [(dn,Closure vars ([],s.bindings) e)]|>)
                              e)
                   (NEndpoint p
                              (s with <|funs := (dn,Closure vars (s.funs,s.bindings) e)::s.funs|>)
                              e)
                        ’
                  by(match_mp_tac bisim_used_closures_rel >>
                     simp[used_closures_rel_def,used_closures_endpoint_rel_def] >>
                     Q.REFINE_EXISTS_TAC ‘(s:closure state) with bindings := _’ >>
                     simp[state_component_equality] >>
                     rpt strip_tac >>
                     drule_all SUBSET_THM >> rw[] >>
                     rw[used_closures_rel_def] >>
                     drule_all SUBSET_THM >> rw[]) >>
                 first_x_assum(fn thm => resolve_then (Pos last) match_mp_tac thm bisim_trans) >>
                 match_mp_tac junkcong_bisim >>
                 goal_assum(resolve_then (Pos hd) mp_tac junkcong_trans) >>
                 goal_assum(resolve_then (Pos hd) mp_tac junkcong_DRESTRICT_closure_hd') >>
                 rfs[free_fun_names_endpoint_def] >>
                 match_mp_tac junkcong_sym >>
                 goal_assum(resolve_then (Pos hd) mp_tac junkcong_trans) >>
                 goal_assum(resolve_then (Pos hd) mp_tac junkcong_DRESTRICT_closure_hd) >>
                 match_mp_tac junkcong_refl_IMP >>
                 AP_THM_TAC >> AP_TERM_TAC >>
                 rw[state_component_equality])) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          rveq >> fs[free_fun_names_endpoint_def,MEM_FILTER,bound_fun_names_endpoint_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
          conj_tac
          >- (fs[EVERY_MEM,IS_SOME_EXISTS] >> rw[] >>
              drule_all SUBSET_THM >> rw[] >> fs[] >>
              drule_all SUBSET_THM >>
              rw[FDOM_FLOOKUP]) >>
          disj1_tac >>
          simp[compile_fix_closure_endpoint_rel_def] >>
          Cases_on ‘dn = dn'’ >-
           (rveq >>
            qexists_tac ‘T’ >> simp[] >>
            fs[letrec_endpoint_def] >>
            fs[consistent_arities_def] >>
            fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
               always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
            fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
            fs[closure_args_def] >>
            rpt strip_tac >>
            IF_CASES_TAC >-
              (fs[closure_args_def,closure_var_env_def] >> rveq >>
               conj_asm1_tac >-
                (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule_all_then strip_assume_tac MEM_arities_saturates >>
                 qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
                 strip_tac >> rveq >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[]) >>
               simp[compile_fix_closure_rel_def] >>
               rpt strip_tac >>
               first_x_assum drule_all >>
               strip_tac >>
               rpt(goal_assum drule) >>
               simp[] >>
               conj_tac >-
                (qpat_x_assum ‘saturates _ _ e1’ assume_tac >>
                 drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[ALOOKUP_MAP]) >>
               last_x_assum(drule_then match_mp_tac) >>
               simp[ALOOKUP_MAP,closure_args_def]) >>
            simp[] >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rpt(goal_assum drule) >>
            simp[] >>
            qpat_x_assum ‘saturates _ _ e2’ assume_tac >>
            drule_then (fs o single) saturates_free_fun_names_endpoint >>
            drule arsof_lemma >>
            disch_then drule >>
            simp[ALOOKUP_MAP]) >>
          qexists_tac ‘T’ >> simp[] >>
          fs[letrec_endpoint_def] >>
          fs[consistent_arities_def] >>
          fs[written_var_names_endpoint_before_def,written_var_names_endpoint_def,
             always_same_args_def,bound_fun_names_endpoint_def,good_letrecs_def] >>
          fs[arities_def,MEM_FILTER,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          fs[closure_args_def] >>
          rpt strip_tac >>
          IF_CASES_TAC >-
           (fs[closure_args_def,closure_var_env_def] >> rveq >>
            conj_asm1_tac >-
             (drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule_all_then strip_assume_tac MEM_arities_saturates >>
              qpat_x_assum ‘∀n. MEM _ (arities _) ⇒ _ = _’ drule >>
              strip_tac >> rveq >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[]) >>
            simp[compile_fix_closure_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            rpt strip_tac >>
            first_x_assum drule_all >>
            strip_tac >>
            rpt(goal_assum drule) >>
            simp[] >>
            conj_tac >-
             (qpat_x_assum ‘saturates _ _ e1’ assume_tac >>
              drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[ALOOKUP_MAP]) >>
            last_x_assum(drule_then match_mp_tac) >>
            simp[ALOOKUP_MAP,closure_args_def]) >>
          simp[] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          rpt(goal_assum drule) >>
          simp[] >>
          qpat_x_assum ‘saturates _ _ e2’ assume_tac >>
          drule_then (fs o single) saturates_free_fun_names_endpoint >>
          drule arsof_lemma >>
          disch_then drule >>
          simp[ALOOKUP_MAP])
      >- ((* trans_call *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
            (Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
             fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
             rfs[] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_call) >>
             fs[arities_def,free_fun_names_endpoint_def] >> rfs[] >>
             fs[always_same_args_def,ALOOKUP_MAP] >> rveq >>
             Cases_on ‘cl1’ >> rveq >> fs[closure_args_def] >>
             fs[written_var_names_endpoint_before_def] >>
             rename1 ‘pair = (_,_)’ >> Cases_on ‘pair’ >> fs[] >>
             conj_tac
             >- (rw[EVERY_MEM,IS_SOME_EXISTS] >>
                 fs[written_var_names_endpoint_def] >>
                 imp_res_tac SUBSET_THM >>
                 fs[FDOM_FLOOKUP]) >>
             rveq >> fs[written_var_names_endpoint_def,bound_fun_names_endpoint_def,free_fun_names_endpoint_def,
                        closure_args_def,closure_var_env_def,always_same_args_def,ALOOKUP_MAP] >>
             rveq >> fs[] >>
             disj1_tac >>
             qhdtm_x_assum ‘compile_fix_closure_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_rel_def]) >>
             rveq >> fs[] >>
             reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
              (simp[compile_fix_closure_endpoint_rel_def] >>
               qexists_tac ‘F’ >>
               simp[GSYM PULL_EXISTS] >>
               conj_asm1_tac >-
                 (simp[fmap_eq_flookup] >>
                  rw[flookup_fupdate_list] >>
                  TOP_CASE_TAC >-
                   (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                    rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                    fs[ALOOKUP_ZIP_MAP_SND,closure_args_def] >>
                    rveq >>
                    fs[ALOOKUP_ZIP_SELF] >> rveq >>
                    rw[] >>
                    qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s.bindings _’ mp_tac >>
                    rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                    pop_assum(qspec_then ‘x’ mp_tac) >>
                    rw[] >>
                    drule_all_then strip_assume_tac SUBSET_THM >>
                    drule_all_then strip_assume_tac SUBSET_THM >>
                    rfs[FDOM_FLOOKUP] >>
                    metis_tac[THE_DEF,FDOM_FLOOKUP,SUBSET_THM]) >>
                  rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                  fs[ALOOKUP_ZIP_MAP_SND,closure_args_def] >>
                  rveq >>
                  fs[ALOOKUP_ZIP_SELF] >> rveq >>
                  drule_all_then strip_assume_tac SUBSET_THM >>
                  simp[]) >>
               goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
               imp_res_tac letrec_endpoint_fsubst' >>
               simp[closure_args_def] >>
               simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
               simp[GSYM PULL_EXISTS] >>
               conj_tac >- fs[SUBSET_DEF] >>
               conj_tac >- rfs[] >>
               conj_tac >-
                (rw[] >> fs[] >> rfs[] >> fs[closure_args_def] >>
                 rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                 rw[] >>
                 rw[flookup_fupdate_list] >>
                 TOP_CASE_TAC >>
                 rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                 fs[ALOOKUP_ZIP_MAP_SND] >>
                 rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                 metis_tac[SUBSET_DEF]) >>
               simp[PULL_EXISTS] >>
               rw[closure_var_env_def,closure_args_def] >> rfs[]
               >- (rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                   rw[] >>
                   rw[flookup_fupdate_list] >>
                   simp[closure_args_def] >>
                   TOP_CASE_TAC >>
                   rfs[closure_args_def] >>
                   rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                   fs[ALOOKUP_ZIP_MAP_SND] >>
                   rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                   drule_all_then strip_assume_tac SUBSET_THM >>
                   drule_all_then strip_assume_tac SUBSET_THM >>
                   fs[FDOM_FLOOKUP] >>
                   qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _’ mp_tac >>
                   rw[fmap_eq_flookup] >>
                   pop_assum(qspec_then ‘x’ mp_tac) >>
                   rw[FLOOKUP_DRESTRICT] >>
                   metis_tac[THE_DEF])
               >- (match_mp_tac arsof_lemma >>
                   goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                   simp[] >>
                   metis_tac[saturates_free_fun_names_endpoint])
               >- (rw[compile_fix_closure_rel_def] >>
                   qexists_tac ‘F’ >> simp[] >>
                   goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                   simp[] >>
                   rpt strip_tac >>
                   metis_tac[])
               >- (first_x_assum(drule_all_then strip_assume_tac) >>
                   rpt(goal_assum drule) >>
                   simp[] >>
                   rfs[] >>
                   qpat_x_assum ‘bindings |++ _ = bindings |++ _’ (fn thm => SUBST_ALL_TAC(GSYM thm) >> assume_tac(GSYM thm)) >>
                   rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                   rw[] >>
                   rw[flookup_fupdate_list] >>
                   TOP_CASE_TAC >>
                   rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                   fs[ALOOKUP_ZIP_MAP_SND] >>
                   rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                   drule_then drule written_var_names_endpoint_lemma >>
                   simp[ALOOKUP_MAP] >>
                   strip_tac >>
                   metis_tac[SUBSET_THM])) >>
            rfs[closure_args_def] >> rveq >> fs[] >>
            simp[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            conj_asm1_tac >-
             (simp[fmap_eq_flookup] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >-
               (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >>
                fs[ALOOKUP_ZIP_SELF] >> rveq >>
                rw[] >>
                qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[] >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                rfs[FDOM_FLOOKUP]) >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              simp[]) >>
            simp[closure_args_def] >>
            simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
            simp[GSYM PULL_EXISTS] >>
            conj_tac >- fs[SUBSET_DEF] >>
            rpt strip_tac >>
            IF_CASES_TAC >-
              (fs[closure_var_env_def,closure_args_def] >> rveq >>
               conj_asm1_tac >-
                 (qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _ ’ (assume_tac o GSYM) >>
                  simp[] >>
                  qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
                  rw[] >> fs[] >> rfs[] >>
                  rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                  rw[] >>
                  rw[flookup_fupdate_list] >>
                  TOP_CASE_TAC >>
                  rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                  fs[ALOOKUP_ZIP_MAP_SND] >>
                  rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq) >>
               conj_asm1_tac >-
                (drule_then (fs o single) saturates_free_fun_names_endpoint >>
                 drule_all_then strip_assume_tac MEM_arities_saturates >>
                 drule arsof_lemma >>
                 disch_then drule >>
                 simp[]) >>
               simp[compile_fix_closure_rel_def] >>
               qexists_tac ‘T’ >> simp[] >>
               rpt strip_tac >>
               first_x_assum drule_all >>
               strip_tac >>
               rpt(goal_assum drule) >>
               simp[]) >>
            simp[] >>
            first_x_assum(drule_all_then strip_assume_tac) >>
            rfs[] >>
            qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
            rw[] >> fs[] >> rfs[] >>
            rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
            rw[] >>
            rw[flookup_fupdate_list] >>
            TOP_CASE_TAC >>
            rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
            fs[ALOOKUP_ZIP_MAP_SND] >>
            rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
            metis_tac[SUBSET_DEF]) >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          fs[always_same_args_def,ALOOKUP_MAP] >>
          rfs[closure_args_def] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_call) >>
          fs[arities_def,free_fun_names_endpoint_def] >>
          Cases_on ‘cl1’ >> rveq >> fs[closure_args_def] >>
          fs[written_var_names_endpoint_before_def] >>
          rename1 ‘pair = (_,_)’ >> Cases_on ‘pair’ >> fs[] >>
          rveq >> fs[] >>
          conj_tac
          >- (rw[EVERY_MEM,IS_SOME_EXISTS] >>
              fs[written_var_names_endpoint_def] >>
              imp_res_tac SUBSET_THM >>
              fs[FDOM_FLOOKUP]) >>
          rveq >> fs[written_var_names_endpoint_def,bound_fun_names_endpoint_def,free_fun_names_endpoint_def,
                       closure_args_def,closure_var_env_def,always_same_args_def,ALOOKUP_MAP] >>
          rveq >> fs[] >>
          disj1_tac >>
          qhdtm_x_assum ‘compile_fix_closure_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_rel_def]) >>
          rveq >> fs[] >>
          reverse(Cases_on ‘shadow’) >> fs[] >> rveq >> fs[] >-
           (simp[compile_fix_closure_endpoint_rel_def] >>
            qexists_tac ‘F’ >>
            simp[GSYM PULL_EXISTS] >>
            conj_asm1_tac >-
             (simp[fmap_eq_flookup] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >-
               (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >>
                fs[ALOOKUP_ZIP_SELF] >> rveq >>
                rw[] >>
                qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[] >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                rfs[FDOM_FLOOKUP]) >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              simp[]) >>
            goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
            imp_res_tac letrec_endpoint_fsubst' >>
            simp[closure_args_def] >>
            simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
            simp[GSYM PULL_EXISTS] >>
            conj_tac >- fs[SUBSET_DEF] >>
            conj_tac >- rfs[] >>
            conj_tac >-
             (rw[] >> fs[] >> rfs[] >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              rw[] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
              metis_tac[SUBSET_DEF]) >>
            simp[PULL_EXISTS] >>
            rw[closure_var_env_def,closure_args_def] >> rfs[]
            >- (rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                rw[] >>
                rw[flookup_fupdate_list] >>
                TOP_CASE_TAC >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                drule_all_then strip_assume_tac SUBSET_THM >>
                fs[FDOM_FLOOKUP] >>
                qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _’ mp_tac >>
                rw[fmap_eq_flookup] >>
                pop_assum(qspec_then ‘x’ mp_tac) >>
                rw[FLOOKUP_DRESTRICT] >>
                metis_tac[THE_DEF])
            >- (match_mp_tac arsof_lemma >>
                goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                simp[] >>
                metis_tac[saturates_free_fun_names_endpoint])
            >- (rw[compile_fix_closure_rel_def] >>
                qexists_tac ‘F’ >> simp[] >>
                goal_assum(drule_at (Pat ‘always_same_args _ _’)) >>
                simp[] >>
                rpt strip_tac >>
                metis_tac[])
            >- (first_x_assum(drule_all_then strip_assume_tac) >>
                rpt(goal_assum drule) >>
                simp[] >>
                rfs[] >>
                qpat_x_assum ‘bindings |++ _ = bindings |++ _’ (fn thm => SUBST_ALL_TAC(GSYM thm) >> assume_tac(GSYM thm)) >>
                rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
                rw[] >>
                rw[flookup_fupdate_list] >>
                TOP_CASE_TAC >>
                rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
                fs[ALOOKUP_ZIP_MAP_SND] >>
                rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
                drule_then drule written_var_names_endpoint_lemma >>
                simp[ALOOKUP_MAP] >>
                strip_tac >>
                metis_tac[SUBSET_THM])) >>
          simp[compile_fix_closure_endpoint_rel_def] >>
          qexists_tac ‘T’ >> simp[] >>
          conj_asm1_tac >-
           (simp[fmap_eq_flookup] >>
            rw[flookup_fupdate_list] >>
            TOP_CASE_TAC >-
             (fs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >>
              fs[ALOOKUP_ZIP_SELF] >> rveq >>
              rw[] >>
              qpat_x_assum ‘DRESTRICT bindings _ = DRESTRICT s2.bindings _’ mp_tac >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              pop_assum(qspec_then ‘x’ mp_tac) >>
              rw[] >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              drule_all_then strip_assume_tac SUBSET_THM >>
              rfs[FDOM_FLOOKUP]) >>
            rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
            fs[ALOOKUP_ZIP_MAP_SND] >>
            rveq >>
            fs[ALOOKUP_ZIP_SELF] >> rveq >>
            drule_all_then strip_assume_tac SUBSET_THM >>
            simp[]) >>
          simp[closure_args_def] >>
          simp[FDOM_FUPDATE_LIST,MAP_ZIP] >>
          simp[GSYM PULL_EXISTS] >>
          conj_tac >- fs[SUBSET_DEF] >>
          rpt strip_tac >>
          IF_CASES_TAC >-
           (fs[closure_var_env_def,closure_args_def] >> rveq >>
            conj_asm1_tac >-
             (qpat_x_assum ‘DRESTRICT _ _ = DRESTRICT _ _ ’ (assume_tac o GSYM) >>
              simp[] >>
              qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
              rw[] >> fs[] >> rfs[] >>
              rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
              rw[] >>
              rw[flookup_fupdate_list] >>
              TOP_CASE_TAC >>
              rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
              fs[ALOOKUP_ZIP_MAP_SND] >>
              rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq) >>
            conj_asm1_tac >-
             (drule_then (fs o single) saturates_free_fun_names_endpoint >>
              drule_all_then strip_assume_tac MEM_arities_saturates >>
              drule arsof_lemma >>
              disch_then drule >>
              simp[]) >>
            simp[compile_fix_closure_rel_def] >>
            qexists_tac ‘T’ >> simp[] >>
            rpt strip_tac >>
            first_x_assum drule_all >>
            strip_tac >>
            rpt(goal_assum drule) >>
            simp[]) >>
          simp[] >>
          first_x_assum(drule_all_then strip_assume_tac) >>
          rfs[] >>
          qpat_x_assum ‘_ |++ _ = _ |++ _’ (assume_tac o GSYM) >>
          rw[] >> fs[] >> rfs[] >>
          rw[fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
          rw[] >>
          rw[flookup_fupdate_list] >>
          TOP_CASE_TAC >>
          rfs[ALOOKUP_REVERSE_ALL_DISTINCT,MAP_ZIP] >>
          fs[ALOOKUP_ZIP_MAP_SND] >>
          rveq >> fs[ALOOKUP_ZIP_SELF] >> rveq >>
          metis_tac[SUBSET_DEF])
  )
QED

Definition free_fix_names_closure_def:
  free_fix_names_closure (Closure vars (fs,bds) e) =
  free_fix_names_endpoint e ++
  FLAT(MAP (λ(n,cl). FILTER ($≠ n) (free_fix_names_closure cl)) fs)
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  rw[] >>
  imp_res_tac closure_size_MEM >>
  DECIDE_TAC
End

Definition free_fun_names_closure_def:
  free_fun_names_closure (Closure vars (fs,bds) e) =
  free_fun_names_endpoint e ++
  FLAT(MAP (λ(n,cl). FILTER ($≠ n) (free_fun_names_closure cl)) fs)
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  rw[] >>
  imp_res_tac closure_size_MEM >>
  DECIDE_TAC
End

Theorem compile_network_preservation_trans_alt:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ reduction conf p1 p2
    ⇒ ∃p3. reduction conf (compile_network_alt p1) p3 ∧
           compile_rel conf p3 (compile_network_alt p2)
Proof
  rpt strip_tac
  >> qhdtm_x_assum ‘reduction’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac  thm)
  >> fs[payloadSemTheory.reduction_def]
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> pop_assum mp_tac
  >> MAP_EVERY qid_spec_tac [`p2`,`alpha`,`p1`,‘conf’]
  >> ho_match_mp_tac payloadSemTheory.trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- ((* trans_com_l *)
      fs[no_undefined_writes_NPar]
      >> MAP_EVERY (drule_all_then strip_assume_tac)
                   [compile_network_preservation_send,
                    compile_network_preservation_receive]
      >> simp[compile_network_alt_def]
      >> drule_all_then strip_assume_tac trans_com_l
      >> fs[GSYM reduction_def]
      >> goal_assum drule
      >> metis_tac[compile_rel_refl,fix_network_NPar,letrec_network_compile_network_alt,
                   letrec_network_trans_pres,letrec_network_NPar])
  >- ((* trans_com_r *)
      fs[no_undefined_writes_NPar]
      >> MAP_EVERY (drule_all_then strip_assume_tac)
                   [compile_network_preservation_send,
                    compile_network_preservation_receive]
      >> simp[compile_network_alt_def]
      >> drule_all_then strip_assume_tac trans_com_r
      >> fs[GSYM reduction_def]
      >> goal_assum drule
      >> metis_tac[compile_rel_refl,fix_network_NPar,letrec_network_compile_network_alt,
                   letrec_network_trans_pres,letrec_network_NPar])
  >- ((* trans_dequeue_last_payload *)
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[letrec_network_def,letrec_endpoint_def,fix_network_def,fix_endpoint_def,endpoints_def,
         letrec_endpoint_compile_endpoint] >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def]
      )
  >- ((* trans_dequeue_intermediate_payload *)
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[letrec_network_def,letrec_endpoint_def,fix_network_def,fix_endpoint_def,endpoints_def,
         letrec_endpoint_compile_endpoint] >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def])
  >- ((* trans_if_true *)
      ‘v ∈ FDOM s.bindings’ by simp[FDOM_FLOOKUP] >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      disj1_tac >>
      simp[flookup_fupdate_list] >>
      reverse TOP_CASE_TAC
      >- (imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,MEM_FILTER,MEM_nub',written_var_names_endpoint_def,PULL_EXISTS]) >>
      pop_assum kall_tac >>
      fs[written_var_names_endpoint_def] >>
      fs[compile_rel_def,letrec_network_def,endpoints_def,fix_network_def,letrec_endpoint_compile_endpoint] >>
      simp[nub'_APPEND,FILTER_APPEND,FUPDATE_LIST_APPEND] >>
      match_mp_tac junkcong_bisim >>
      goal_assum(resolve_then (Pos hd) mp_tac junkcong_sym) >>
      goal_assum(resolve_then (Pos hd) mp_tac junkcong_add_junk_list') >>
      rw[MEM_MAP,MEM_FILTER,MEM_nub'] >>
      qexists_tac ‘𝕌(varN)’ >>
      rw[] >>
      fs[free_fix_names_network_def,free_fix_names_endpoint_def] >>
      spose_not_then strip_assume_tac >>
      drule_all free_var_names_endpoint_compile_endpoint_NIL >>
      fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def,SUBSET_DEF] >>
      metis_tac[])
  >- ((* trans_if_false *)
      ‘v ∈ FDOM s.bindings’ by simp[FDOM_FLOOKUP] >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      disj2_tac >>
      simp[flookup_fupdate_list] >>
      reverse TOP_CASE_TAC
      >- (imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,MEM_FILTER,MEM_nub',written_var_names_endpoint_def,PULL_EXISTS]) >>
      pop_assum kall_tac >>
      fs[written_var_names_endpoint_def] >>
      fs[compile_rel_def,letrec_network_def,endpoints_def,fix_network_def,letrec_endpoint_compile_endpoint] >>
      simp[nub'_APPEND,FILTER_APPEND,FUPDATE_LIST_APPEND] >>
      match_mp_tac junkcong_bisim >>
      goal_assum(resolve_then (Pos hd) mp_tac junkcong_sym) >>
      (* TODO: something less atrocious *)
      ‘s.bindings |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (nub' (written_var_names_endpoint e1)))
                  |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (FILTER (λy. ~MEM y (written_var_names_endpoint e1)) (nub' (written_var_names_endpoint e2)))) =
       s.bindings |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (nub' (written_var_names_endpoint e2)))
                  |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (FILTER (λy. ~MEM y (written_var_names_endpoint e2))  (nub' (written_var_names_endpoint e1))))’
        by(rw[fmap_eq_flookup,flookup_fupdate_list] >>
           every_case_tac >>
           imp_res_tac ALOOKUP_MEM >>
           fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS]) >>
      pop_assum SUBST_ALL_TAC >>
      goal_assum(resolve_then (Pos hd) mp_tac junkcong_add_junk_list') >>
      rw[MEM_MAP,MEM_FILTER,MEM_nub'] >>
      qexists_tac ‘𝕌(varN)’ >>
      rw[] >>
      fs[free_fix_names_network_def,free_fix_names_endpoint_def] >>
      spose_not_then strip_assume_tac >>
      drule_all free_var_names_endpoint_compile_endpoint_NIL >>
      fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def,SUBSET_DEF] >>
      metis_tac[])
  >- ((* trans_let *)
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[letrec_network_def,endpoints_def,letrec_endpoint_def,letrec_endpoint_compile_endpoint,
         fix_network_def] >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def] >>
      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS,flookup_update_list_some,
         MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,alookup_distinct_reverse,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub',EXISTS_OR_THM] >>
      conj_tac >- metis_tac[] >>
      AP_TERM_TAC >>
      rw[MAP_EQ_f] >> rw[] >>
      res_tac >>
      fs[FDOM_FLOOKUP])
  >- ((* trans_par_l *)
      fs[compile_network_alt_def,fix_network_NPar,free_fix_names_network_def,no_undefined_vars_network_NPar] >>
      drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) trans_par_l >>
      fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
      drule_then MATCH_ACCEPT_TAC bisim_par_left)
  >- ((* trans_par_r *)
      fs[compile_network_alt_def,fix_network_NPar,free_fix_names_network_def,no_undefined_vars_network_NPar] >>
      drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) trans_par_r >>
      fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
      drule_then MATCH_ACCEPT_TAC bisim_par_right)
  >- ((* trans_fix *)
      rename1 ‘Fix dn e’ >>
      simp[reduction_def,compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases] >>
      conj_asm1_tac >-
        (rw[EVERY_MEM,IS_SOME_EXISTS,flookup_update_list_some,
            MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,alookup_distinct_reverse,
            FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub',EXISTS_OR_THM,
            written_var_names_endpoint_def] >>
         metis_tac[FDOM_FLOOKUP,MEM_written_var_names_endpoint_until_IMP]) >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      fs[free_fix_names_network_def] >>
      drule compile_endpoint_dsubst >>
      disch_then(resolve_then (Pos hd) mp_tac SUBSET_REFL) >>
      fs[fix_network_def,endpoints_def,fix_endpoint_def] >>
      disch_then(qspec_then ‘[]’ mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      simp[] >>
      simp[compile_rel_def] >>
      fs[letrec_network_def,letrec_endpoint_def,endpoints_def,letrec_endpoint_compile_endpoint,
         letrec_closure_def] >>
      conj_tac >- metis_tac[letrec_endpoint_compile_endpoint] >>
      simp[written_var_names_endpoint_def] >>
      simp[compile_endpoint_def] >>
      qmatch_goalsub_abbrev_tac ‘BISIM_REL _ (NEndpoint _ (_ with <|bindings := b1; funs := _|>) _)
                                             (NEndpoint _ (_ with bindings := b2) _)’ >>
      ‘b1 = b2’
        by(unabbrev_all_tac >>
           rw[fmap_eq_flookup,flookup_fupdate_list] >>
           every_case_tac >>
           imp_res_tac ALOOKUP_MEM >>
           fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,MEM_ZIP,fmap_eq_flookup,flookup_fupdate_list,
              MEM_ZIP,EL_MAP,FDOM_FLOOKUP] >>
           imp_res_tac written_var_names_endpoint_dsubst >>
           fs[written_var_names_endpoint_def] >>
           rveq >>
           TRY(PURE_TOP_CASE_TAC >> fs[] >>
               rveq >>
               imp_res_tac ALOOKUP_MEM >>
               fs[] >>
               fs[MEM_MAP,MEM_FILTER,MEM_nub'] >>
               fs[ALOOKUP_NONE] >>
               fs[MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS] >>
               metis_tac[MEM_EL,MEM_written_var_names_endpoint_until_IMP,MEM_nub']) >>
           imp_res_tac written_var_names_endpoint_dsubst' >>
           fs[] >>
           rveq >>
           metis_tac[MEM_EL,MEM_written_var_names_endpoint_until_IMP,MEM_nub']) >>
      pop_assum SUBST_ALL_TAC >>
      simp[Abbr ‘b2’] >>
      pop_assum kall_tac >>
      qmatch_goalsub_abbrev_tac ‘s with bindings := a1’ >>
      qmatch_goalsub_abbrev_tac ‘Closure _ ([],a2)’ >>
      ‘a1 = a2’
        by(unabbrev_all_tac >>
           rw[fmap_eq_flookup,flookup_fupdate_list] >>
           every_case_tac >>
           imp_res_tac ALOOKUP_MEM >>
           fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,MEM_ZIP,fmap_eq_flookup,flookup_fupdate_list,
              MEM_ZIP,EL_MAP,FDOM_FLOOKUP] >>
           imp_res_tac written_var_names_endpoint_dsubst >>
           fs[written_var_names_endpoint_def] >>
           rveq >>
           imp_res_tac written_var_names_endpoint_dsubst' >>
           fs[]) >>
      pop_assum SUBST_ALL_TAC >>
      pop_assum kall_tac >>
      simp[Abbr ‘a2’] >>
      match_mp_tac bisim_defer_fundef >>
      simp[compile_fix_closure_endpoint_rel_def,letrec_endpoint_compile_endpoint,all_distinct_nub',
           set_nub'] >>
      CONV_TAC(RESORT_EXISTS_CONV (fn l => List.nth(l,3)::List.take(l,3) @ [last l])) (* TODO: make less hacky *) >>
      qexists_tac ‘F’ >> simp[letrec_endpoint_compile_endpoint,all_distinct_nub',set_nub'] >>
      simp[saturates_nub'] >>
      goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      simp[FDOM_FUPDATE_LIST,MAP_MAP_o,LIST_TO_SET_MAP] >>
      simp[good_letrecs_def,closure_args_def,good_letrecs_compile_endpoint,set_nub',
           arities_compile_endpoint_eq,compile_endpoint_consistent_arities,
           compile_endpoint_always_same_args,arsof_compile_endpoint_SUBSET,
           SUBSET_REFL] >>
      conj_tac >-
        (drule_then match_mp_tac saturates_mono >>
         match_mp_tac SUBSET_TRANS >>
         goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET) >>
         simp[] >>
         goal_assum(resolve_then (Pos hd) mp_tac SUBSET_REFL)) >>
      conj_tac >-
       (metis_tac[letrec_endpoint_fsubst',letrec_endpoint_compile_endpoint]) >>
      conj_tac >-
       (‘consistent_arities (fsubst e'' dn (compile_endpoint [] (Fix dn e)))’
          by(metis_tac[compile_endpoint_consistent_arities]) >>
        drule_then match_mp_tac fsubst_consistent_arities_nofrees >>
        simp[] >>
        goal_assum drule) >>
      conj_tac >-
       (rw[SET_EQ_SUBSET]
        >- metis_tac[written_var_names_endpoint_compile_endpoint_SUBSET]
        >- (match_mp_tac SUBSET_TRANS >>
            goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET') >>
            simp[set_nub'])) >>
      conj_tac >-
       (match_mp_tac SUBSET_TRANS >>
        goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET') >>
        simp[set_nub'] >>
        simp[IMAGE_IMAGE,o_DEF,LIST_TO_SET_FILTER,set_nub'] >>
        rw[SUBSET_DEF,UNION_DEF,INTER_DEF]) >>
      conj_tac >-
       (rw[SUBSET_DEF] >>
        drule written_var_names_endpoint_before_compile_endpoint >>
        rw[set_nub']) >>
      conj_tac >-
       (rw[SUBSET_DEF] >> drule free_fun_names_endpoint_compile_endpoint >> rw[]) >>
      conj_tac >-
       (drule saturates_written_var_names_endpoint' >>
        strip_tac >>
        dxrule_then match_mp_tac SUBSET_TRANS >>
        simp[] >>
        match_mp_tac written_var_names_endpoint_compile_endpoint_SUBSET >> simp[]) >>
      match_mp_tac always_same_args_fsubst_lemma >>
      simp[] >>
      metis_tac[compile_endpoint_always_same_args])
  >- ((* trans_Letrec *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
  >- ((* trans_call *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
QED

Theorem no_undefined_writes_compile_network_alt:
  ∀n1.
    no_undefined_writes n1 ⇒
    compile_network_alt n1 = compile_network n1
Proof
  Induct >> rw[compile_network_alt_def,compile_network_def,no_undefined_writes_NPar] >>
  fs[no_undefined_writes_def,endpoints_def] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[FILTER_EQ_NIL |> SPEC_ALL |> REWRITE_RULE[EQ_IMP_THM] |> CONJUNCT2 |> GEN_ALL] >>
  simp[state_component_equality,FUPDATE_LIST_THM] >>
  fs[EVERY_MEM,MEM_nub',SUBSET_DEF]
QED

Theorem compile_network_reduction_alt:
  ∀conf n1. (reduction conf)^* (compile_network n1) (compile_network_alt n1)
Proof
  strip_tac >> Induct >>
  rw[compile_network_def,compile_network_alt_def]
  >- (metis_tac [RTC_RTC,reduction_par_l,reduction_par_r])
  >- (qmatch_goalsub_abbrev_tac ‘FOLDL _ _ l’ >>
      Q.SUBGOAL_THEN ‘ALL_DISTINCT l’ mp_tac >- rw[Abbr ‘l’,FILTER_ALL_DISTINCT,all_distinct_nub'] >>
      pop_assum kall_tac >>
      rename1 ‘NEndpoint p st’ >>
      qid_spec_tac ‘st’ >>
      qid_spec_tac ‘l’ >>
      ho_match_mp_tac SNOC_INDUCT >>
      rw[FUPDATE_LIST_THM,ALL_DISTINCT_SNOC]
      >- (Q.SUBGOAL_THEN ‘st with bindings := st.bindings = st’ (rw o single) >>
          rw[state_component_equality]) >>
      simp[FOLDL_SNOC,MAP_SNOC,FUPDATE_LIST_SNOC] >>
      match_mp_tac RTC_TRANS >>
      simp[reduction_def,Once trans_cases,endpoint_to_choiceTheory.K0_def] >>
      match_mp_tac (MP_CANON RTC_RTC) >>
      first_x_assum(fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) >>
      simp[] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [FUPDATE_FUPDATE_LIST_COMMUTES] >>
      simp[] >>
      spose_not_then strip_assume_tac >>
      fs[MEM_MAP] >> rveq >> fs[])
QED

Theorem compile_rel_trans:
  compile_rel conf p1 p2 ∧ compile_rel conf p2 p3 ⇒
  compile_rel conf p1 p3
Proof
  rw[compile_rel_def] >> metis_tac[bisim_trans]
QED

(* TODO: having compile_network instead of compile_network_alt in the conclusion would be
         nicer, but that requires using a different notion of bismulation in the theorem statement *)
Theorem compile_network_preservation_trans:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ reduction conf p1 p2
    ⇒ ∃p3. (reduction conf)^* (compile_network p1) p3 ∧
           compile_rel conf p3 (compile_network_alt p2)
Proof
  rpt strip_tac >>
  drule_all_then strip_assume_tac compile_network_preservation_trans_alt >>
  goal_assum(resolve_then (Pos hd) mp_tac RTC_RTC) >>
  goal_assum(resolve_then (Pos hd) mp_tac compile_network_reduction_alt) >>
  goal_assum(resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
  goal_assum drule >>
  simp[]
QED

Theorem bisim_reductionE:
  ∀conf p2 p3 p1.
  (reduction conf)^* p2 p3 ∧
  BISIM_REL (trans conf) p1 p2 ⇒
  ∃p4. (reduction conf)^* p1 p4 ∧ BISIM_REL (trans conf) p4 p3
Proof
  strip_tac >>
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> rw[]
  >- metis_tac[RTC_REFL,bisim_refl]
  >- (qhdtm_x_assum ‘BISIM_REL’ (strip_assume_tac o REWRITE_RULE[Once bisimulationTheory.BISIM_REL_cases]) >>
      fs[reduction_def] >>
      res_tac >> fs[] >>
      last_x_assum drule >> rw[] >>
      goal_assum(drule_at (Pos last)) >>
      metis_tac[RTC_TRANS,reduction_def])
QED

Theorem tausim_reductionE:
  ∀conf p2 p3 p1.
  (reduction conf)^* p2 p3 ∧
  tausim conf p1 p2 ⇒
  ∃p4. (reduction conf)^* p1 p4 ∧ tausim conf p4 p3
Proof
  strip_tac >>
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> rw[]
  >- metis_tac[RTC_REFL,tausim_refl]
  >- (qhdtm_x_assum ‘tausim’ (strip_assume_tac o REWRITE_RULE[Once tausim_cases]) >>
      fs[reduction_def] >>
      res_tac >> fs[] >>
      last_x_assum drule >> rw[] >>
      goal_assum(drule_at (Pos last)) >>
      drule_at_then (Pos last) match_mp_tac RTC_RTC >>
      drule_then MATCH_ACCEPT_TAC RC_RTC)
QED

Theorem tausim_reductionE2:
  ∀conf p2 p3 p1.
  reduction conf p1 p3 ∧
  tausim conf p1 p2 ⇒
  ∃p4. (reduction conf)^+ p2 p4 ∧ tausim conf p3 p4
Proof
  strip_tac >>
  rw[Once tausim_cases,reduction_def]
QED

Theorem compile_network_preservation_alt:
  ∀conf p1 p2.
    (reduction conf)^* p1 p2
    ∧ conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ⇒ ∃p3. (reduction conf)^* (compile_network_alt p1) p3 ∧
           compile_rel conf p3 (compile_network_alt p2)
Proof
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >-
    (goal_assum(resolve_then (Pos hd) mp_tac RTC_REFL) >>
     match_mp_tac compile_rel_refl >>
     simp[letrec_network_compile_network_alt]) >>
  fs[] >>
  ‘fix_network p1'’ by metis_tac[fix_network_trans_pres,reduction_def] >>
  first_x_assum drule >>
  impl_tac
  >- (drule_all free_fix_names_network_reduction_pres >>
      rw[] >>
      imp_res_tac no_undefined_vars_network_reduction_pres) >>
  strip_tac >>
  drule_all compile_network_preservation_trans_alt >>
  strip_tac >>
  qhdtm_assum ‘compile_rel’ (strip_assume_tac o REWRITE_RULE[compile_rel_def]) >>
  drule_all bisim_reductionE >>
  strip_tac >>
  goal_assum(resolve_then (Pos hd) mp_tac RTC_TRANS) >>
  goal_assum drule >>
  goal_assum drule >>
  fs[compile_rel_def] >>
  conj_tac
  >- (drule_then match_mp_tac letrec_network_weak_reduction_pres >>
      simp[]) >>
  metis_tac[bisim_trans]
QED

Theorem compile_network_reflection_single:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ (reduction conf) (compile_network_alt p1) p2
    ⇒ ∃p3 p4. reduction conf p1 p3 ∧
              compile_rel conf p2 (compile_network_alt p3)
Proof
  rpt GEN_TAC >>
  qid_spec_tac ‘p2’ >>
  Induct_on ‘p1’
  >-  ((* Nil *)
       rw[reduction_def,compile_network_alt_def,Once trans_cases])
  >-  ((* NPar *)
       rw[fix_network_NPar,free_fix_names_network_def,no_undefined_vars_network_NPar,
          reduction_def,compile_network_alt_def] >>
       qhdtm_x_assum ‘trans’ (strip_assume_tac o PURE_REWRITE_RULE[Once trans_cases]) >>
       fs[] >> rveq
       >- ((* trans_com_l *)
           drule_all compile_network_reflection_receive >> strip_tac >> rveq >>
           drule_all compile_network_reflection_send >> strip_tac >> rveq >>
           goal_assum(resolve_then (Pos hd) mp_tac trans_com_l) >>
           rpt(goal_assum drule) >>
           simp[compile_network_alt_def] >>
           match_mp_tac compile_rel_refl >>
           simp[letrec_network_NPar] >>
           conj_tac >> match_mp_tac letrec_network_compile_network_alt >>
           drule_then match_mp_tac fix_network_trans_pres >> simp[])
       >- ((* trans_com_l *)
           drule_all compile_network_reflection_receive >> strip_tac >> rveq >>
           drule_all compile_network_reflection_send >> strip_tac >> rveq >>
           goal_assum(resolve_then (Pos hd) mp_tac trans_com_r) >>
           rpt(goal_assum drule) >>
           simp[compile_network_alt_def] >>
           match_mp_tac compile_rel_refl >>
           simp[letrec_network_NPar] >>
           conj_tac >> match_mp_tac letrec_network_compile_network_alt >>
           drule_then match_mp_tac fix_network_trans_pres >> simp[])
       >- ((* trans_par_l *)
           fs[reduction_def] >>
           first_x_assum drule_all >> strip_tac >>
           goal_assum(resolve_then (Pos hd) mp_tac trans_par_l) >>
           goal_assum drule >>
           simp[compile_network_alt_def] >>
           fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
           drule_then MATCH_ACCEPT_TAC bisim_par_left)
       >- ((* trans_par_r *)
           fs[reduction_def] >>
           first_x_assum drule_all >> strip_tac >>
           goal_assum(resolve_then (Pos hd) mp_tac trans_par_r) >>
           goal_assum drule >>
           simp[compile_network_alt_def] >>
           fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
           drule_then MATCH_ACCEPT_TAC bisim_par_right))
  >-  ((* NEndpoint *)
       rw[fix_network_def,free_fix_names_network_def,no_undefined_vars_network_def,endpoints_def,
          reduction_def,compile_network_alt_def] >>
       Cases_on ‘e’ >> fs[compile_endpoint_def] >>
       qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
       fs[] >> rveq >> fs[]
       >- ((* trans_dequeue_last_payload *)
           goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
           simp[compile_network_alt_def,written_var_names_endpoint_def] >>
           match_mp_tac compile_rel_reflI >>
           conj_tac >- fs[letrec_network_def,endpoints_def,letrec_endpoint_compile_endpoint] >>
           simp[state_component_equality] >>
           simp[fmap_eq_flookup,FLOOKUP_UPDATE,flookup_fupdate_list] >>
           rw[] >> TOP_CASE_TAC >>
           imp_res_tac ALOOKUP_MEM >>
           fs[MEM_MAP,MEM_FILTER] >>
           TOP_CASE_TAC >> fs[] >>
           imp_res_tac ALOOKUP_MEM >>
           fs[MEM_MAP,MEM_FILTER] >>
           fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub'] >>
           metis_tac[FST,SND,PAIR])
       >- ((* trans_dequeue_intermediate_payload *)
           goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
           simp[compile_network_alt_def,written_var_names_endpoint_def,compile_endpoint_def] >>
           match_mp_tac compile_rel_reflI >>
           conj_tac >- fs[letrec_network_def,endpoints_def,letrec_endpoint_compile_endpoint,letrec_endpoint_def] >>
           simp[state_component_equality] >>
           simp[fmap_eq_flookup,FLOOKUP_UPDATE,flookup_fupdate_list] >>
           rw[] >> TOP_CASE_TAC >>
           imp_res_tac ALOOKUP_MEM >>
           fs[MEM_MAP,MEM_FILTER] >>
           TOP_CASE_TAC >> fs[] >>
           imp_res_tac ALOOKUP_MEM >>
           fs[MEM_MAP,MEM_FILTER] >>
           fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub'] >>
           metis_tac[FST,SND,PAIR])
       >- ((* trans_if_true *)
           goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
           conj_tac
           >- (fs[flookup_fupdate_list,CaseEq "option"] >>
               imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP]) >>
           simp[compile_network_alt_def] >>
           fs[written_var_names_endpoint_def,nub'_APPEND,FILTER_APPEND] >>
           fs[compile_rel_def,letrec_network_def,endpoints_def,fix_network_def,letrec_endpoint_compile_endpoint] >>
           fs[FUPDATE_LIST_APPEND] >>
           match_mp_tac junkcong_bisim >>
           goal_assum(resolve_then (Pos hd) mp_tac junkcong_sym) >>
           goal_assum(resolve_then (Pos hd) mp_tac junkcong_add_junk_list') >>
           rw[MEM_MAP,MEM_FILTER,MEM_nub'] >>
           qexists_tac ‘𝕌(varN)’ >>
           rw[] >>
           fs[free_fix_names_network_def,free_fix_names_endpoint_def] >>
           spose_not_then strip_assume_tac >>
           drule_all free_var_names_endpoint_compile_endpoint_NIL >>
           fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def,SUBSET_DEF] >>
           metis_tac[])
       >- ((* trans_if_false *)
           goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
           goal_assum(drule_at (Pat ‘_ ≠ _’)) >>
           conj_tac
           >- (fs[flookup_fupdate_list,CaseEq "option"] >>
               imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,MEM_FILTER,free_var_names_endpoint_def]) >>
           simp[compile_network_alt_def,written_var_names_endpoint_def] >>
           fs[compile_rel_def,letrec_network_def,endpoints_def,fix_network_def,letrec_endpoint_compile_endpoint] >>
           simp[nub'_APPEND,FILTER_APPEND,FUPDATE_LIST_APPEND] >>
           match_mp_tac junkcong_bisim >>
           goal_assum(resolve_then (Pos hd) mp_tac junkcong_sym) >>
           rename1 ‘s.bindings’ >>
           rename1 ‘IfThen _ e1 e2’ >>
           ‘s.bindings |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (nub' (written_var_names_endpoint e1)))
                  |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (FILTER (λy. ~MEM y (written_var_names_endpoint e1)) (nub' (written_var_names_endpoint e2)))) =
            s.bindings |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (nub' (written_var_names_endpoint e2)))
                  |++ MAP (λx. (x,[0w]))
                       (FILTER (λx. x ∉ FDOM s.bindings)
                        (FILTER (λy. ~MEM y (written_var_names_endpoint e2))  (nub' (written_var_names_endpoint e1))))’
             by(rw[fmap_eq_flookup,flookup_fupdate_list] >>
                every_case_tac >>
                imp_res_tac ALOOKUP_MEM >>
                fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS]) >>
           pop_assum SUBST_ALL_TAC >>
           goal_assum(resolve_then (Pos hd) mp_tac junkcong_add_junk_list') >>
           rw[MEM_MAP,MEM_FILTER,MEM_nub'] >>
           qexists_tac ‘𝕌(varN)’ >>
           rw[] >>
           fs[free_fix_names_network_def,free_fix_names_endpoint_def] >>
           spose_not_then strip_assume_tac >>
           drule_all free_var_names_endpoint_compile_endpoint_NIL >>
           fs[no_undefined_vars_network_def,endpoints_def,free_var_names_endpoint_def,SUBSET_DEF] >>
           metis_tac[])
       >- ((* trans_let *)
           goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
           fs[free_fix_names_endpoint_def,free_var_names_endpoint_def] >>
           simp[compile_network_alt_def,compile_endpoint_def] >>
           conj_tac >-
             (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
              rpt strip_tac >>
              res_tac >>
              fs[IS_SOME_EXISTS,flookup_fupdate_list,CaseEq "option"] >>
              imp_res_tac ALOOKUP_MEM >>
              fs[MEM_MAP,MEM_FILTER,MEM_nub',written_var_names_endpoint_def] >>
              metis_tac[SUBSET_THM]) >>
           match_mp_tac compile_rel_reflI >>
           simp[letrec_network_def,endpoints_def,letrec_endpoint_compile_endpoint] >>
           fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
              flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
              FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
           csimp[CaseEq "bool",written_var_names_endpoint_def] >>
           fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS,flookup_update_list_some,
              MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,alookup_distinct_reverse,
              FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub',EXISTS_OR_THM] >>
           AP_TERM_TAC >>
           rw[MAP_EQ_f] >> rw[] >>
           res_tac >>
           fs[FDOM_FLOOKUP] >>
           imp_res_tac SUBSET_THM >>
           fs[FDOM_FLOOKUP] >> fs[])
       >- ((* trans_fix *)
           rename1 ‘Fix dn e’ >>
           simp[reduction_def,compile_network_alt_def,compile_endpoint_def] >>
           simp[Once trans_cases] >>
           simp[compile_network_alt_def,compile_endpoint_def] >>
           fs[free_fix_names_network_def] >>
           drule compile_endpoint_dsubst >>
           disch_then(resolve_then (Pos hd) mp_tac SUBSET_REFL) >>
           fs[fix_network_def,endpoints_def,fix_endpoint_def] >>
           disch_then(qspec_then ‘[]’ mp_tac) >>
           impl_tac >- simp[] >>
           strip_tac >>
           simp[] >>
           simp[compile_rel_def] >>
           fs[letrec_network_def,letrec_endpoint_def,endpoints_def,letrec_endpoint_compile_endpoint,
              letrec_closure_def] >>
           conj_tac >- metis_tac[letrec_endpoint_compile_endpoint] >>
           simp[written_var_names_endpoint_def] >>
           simp[compile_endpoint_def] >>
           qmatch_goalsub_abbrev_tac ‘BISIM_REL _ (NEndpoint _ (_ with <|bindings := b1; funs := _|>) _)
                                                  (NEndpoint _ (_ with bindings := b2) _)’ >>
           ‘b1 = b2’
             by(unabbrev_all_tac >>
                rw[fmap_eq_flookup,flookup_fupdate_list] >>
                every_case_tac >>
                imp_res_tac ALOOKUP_MEM >>
                fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,MEM_ZIP,fmap_eq_flookup,flookup_fupdate_list,
                   MEM_ZIP,EL_MAP,FDOM_FLOOKUP] >>
                imp_res_tac written_var_names_endpoint_dsubst >>
                fs[written_var_names_endpoint_def] >>
                rveq >>
                TRY(PURE_TOP_CASE_TAC >> fs[] >>
                    rveq >>
                    imp_res_tac ALOOKUP_MEM >>
                    fs[] >>
                    fs[MEM_MAP,MEM_FILTER,MEM_nub'] >>
                    fs[ALOOKUP_NONE] >>
                    fs[MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS] >>
                    metis_tac[MEM_EL,MEM_written_var_names_endpoint_until_IMP,MEM_nub']) >>
                imp_res_tac written_var_names_endpoint_dsubst' >>
                fs[] >>
                rveq >>
                metis_tac[MEM_EL,MEM_written_var_names_endpoint_until_IMP,MEM_nub']) >>
           pop_assum SUBST_ALL_TAC >>
           simp[Abbr ‘b2’] >>
           pop_assum kall_tac >>
           rename1 ‘s.bindings’ >>
           qmatch_goalsub_abbrev_tac ‘s with bindings := a1’ >>
           qmatch_goalsub_abbrev_tac ‘Closure _ ([],a2)’ >>
           ‘a1 = a2’
             by(unabbrev_all_tac >>
                rw[fmap_eq_flookup,flookup_fupdate_list] >>
                every_case_tac >>
                imp_res_tac ALOOKUP_MEM >>
                fs[ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,MEM_ZIP,fmap_eq_flookup,flookup_fupdate_list,
                   MEM_ZIP,EL_MAP,FDOM_FLOOKUP] >>
                imp_res_tac written_var_names_endpoint_dsubst >>
                fs[written_var_names_endpoint_def] >>
                rveq >>
                imp_res_tac written_var_names_endpoint_dsubst' >>
                fs[]) >>
           pop_assum SUBST_ALL_TAC >>
           pop_assum kall_tac >>
           simp[Abbr ‘a2’] >>
           match_mp_tac bisim_defer_fundef >>
           simp[compile_fix_closure_endpoint_rel_def,letrec_endpoint_compile_endpoint,all_distinct_nub',
                set_nub'] >>
           CONV_TAC(RESORT_EXISTS_CONV (fn l => List.nth(l,3)::List.take(l,3) @ [last l])) (* TODO: make less hacky *) >>
           qexists_tac ‘F’ >> simp[letrec_endpoint_compile_endpoint,all_distinct_nub',set_nub'] >>
           simp[saturates_nub'] >>
           goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
           simp[FDOM_FUPDATE_LIST,MAP_MAP_o,LIST_TO_SET_MAP] >>
           simp[good_letrecs_def,closure_args_def,good_letrecs_compile_endpoint,set_nub',
                arities_compile_endpoint_eq,compile_endpoint_consistent_arities,
                compile_endpoint_always_same_args,arsof_compile_endpoint_SUBSET,
                SUBSET_REFL] >>
           conj_tac >-
            (drule_then match_mp_tac saturates_mono >>
             match_mp_tac SUBSET_TRANS >>
             goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET) >>
             simp[] >>
             goal_assum(resolve_then (Pos hd) mp_tac SUBSET_REFL)) >>
           conj_tac >-
            (metis_tac[letrec_endpoint_fsubst',letrec_endpoint_compile_endpoint]) >>
           conj_tac >-
            (‘consistent_arities (fsubst e'' dn (compile_endpoint [] (Fix dn e)))’
               by(metis_tac[compile_endpoint_consistent_arities]) >>
             drule_then match_mp_tac fsubst_consistent_arities_nofrees >>
             simp[] >>
             goal_assum drule) >>
           conj_tac >-
            (rw[SET_EQ_SUBSET]
             >- metis_tac[written_var_names_endpoint_compile_endpoint_SUBSET]
             >- (match_mp_tac SUBSET_TRANS >>
                 goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET') >>
                 simp[set_nub'])) >>
           conj_tac >-
            (match_mp_tac SUBSET_TRANS >>
             goal_assum(resolve_then (Pos hd) mp_tac written_var_names_endpoint_compile_endpoint_SUBSET') >>
             simp[set_nub'] >>
             simp[IMAGE_IMAGE,o_DEF,LIST_TO_SET_FILTER,set_nub'] >>
             rw[SUBSET_DEF,UNION_DEF,INTER_DEF]) >>
           conj_tac >-
            (rw[SUBSET_DEF] >>
             drule written_var_names_endpoint_before_compile_endpoint >>
             rw[set_nub']) >>
           conj_tac >-
            (rw[SUBSET_DEF] >> drule free_fun_names_endpoint_compile_endpoint >> rw[]) >>
           conj_tac >-
            (drule saturates_written_var_names_endpoint' >>
             strip_tac >>
             dxrule_then match_mp_tac SUBSET_TRANS >>
             simp[] >>
             match_mp_tac written_var_names_endpoint_compile_endpoint_SUBSET >> simp[]) >>
           match_mp_tac always_same_args_fsubst_lemma >>
           simp[] >>
           metis_tac[compile_endpoint_always_same_args]))
QED

Theorem compile_network_endpoints:
  ∀p1.
    MAP FST(endpoints(compile_network p1)) = MAP FST (endpoints p1)
Proof
  Induct >> rw[compile_network_def,endpoints_def]
QED

Theorem compile_rel_trans_pres:
  ∀conf n1 α n2 n1'.
    compile_rel conf n1 n2 ∧ trans conf n1 α n1' ⇒
    ∃n2'. trans conf n2 α n2' ∧ compile_rel conf n1' n2'
Proof
  rpt strip_tac >>
  fs[compile_rel_def] >>
  qhdtm_x_assum ‘BISIM_REL’ (strip_assume_tac o REWRITE_RULE[Once bisimulationTheory.BISIM_REL_cases]) >>
  fs[FORALL_AND_THM] >>
  res_tac >>
  goal_assum drule >>
  simp[] >>
  imp_res_tac letrec_network_trans_pres >> simp[]
QED

Theorem list_trans_compile_rel:
  ∀conf p1 l p1' p2.
  list_trans conf p1 l p1' ∧
  compile_rel conf p1 p2 ⇒
  ∃p2'. list_trans conf p2 l p2' ∧ compile_rel conf p1' p2'
Proof
  strip_tac >> Induct_on ‘l’ >>
  rw[list_trans_def] >- goal_assum drule >>
  drule_all compile_rel_trans_pres >> strip_tac >>
  metis_tac[]
QED

Theorem compile_network_reflection_alt:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ (reduction conf)^* (compile_network_alt p1) p2
    ⇒ ∃p3. (reduction conf)^* p1 p3 ∧
           compile_rel conf p2 (compile_network_alt p3)
Proof
  simp[reduction_list_trans,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases
  >- (rw[list_trans_def] >>
      CONV_TAC(RESORT_EXISTS_CONV rev) >>
      qexists_tac ‘0’ >> rw[list_trans_def] >>
      metis_tac[RTC_REFL,compile_rel_refl,letrec_network_compile_network_alt])
  >- (rw[list_trans_def,GSYM reduction_def] >>
      CONV_TAC(RESORT_EXISTS_CONV rev) >>
      Q.REFINE_EXISTS_TAC ‘SUC _’ >>
      simp[list_trans_def,PULL_EXISTS,GSYM reduction_def] >>
      drule_all(compile_network_reflection_single
                |> REWRITE_RULE[PULL_EXISTS,reduction_list_trans]) >>
      strip_tac >>
      goal_assum drule >>
      PRED_ASSUM is_forall (resolve_then (Pos hd) mp_tac prim_recTheory.LESS_SUC_REFL) >>
      disch_then drule >>
      drule_all list_trans_compile_rel >>
      strip_tac >>
      disch_then(drule_at (Pos last)) >>
      impl_tac
      >- (conj_tac >- metis_tac[fix_network_trans_pres,reduction_def] >>
          conj_tac >- (fs[reduction_def] >> imp_res_tac free_fix_names_network_trans_pres >>
                       rfs[]) >>
          metis_tac[endpoint_names_trans,reduction_def,no_undefined_vars_network_trans_pres,
                    compile_network_endpoints]) >>
      strip_tac >>
      rpt(goal_assum drule) >>
      metis_tac[compile_rel_trans])
QED

Theorem compile_network_reflection:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ ALL_DISTINCT (MAP FST (endpoints p1))
    ∧ (reduction conf)^* (compile_network p1) p2
    ⇒ ∃p3 p4.
           (reduction conf)^* p1 p3 ∧
           (reduction conf)^* p2 p4 ∧
           compile_rel conf p4 (compile_network_alt p3)
Proof
  rpt strip_tac >>
  qspecl_then [‘conf’,‘p1’] assume_tac compile_network_reduction_alt >>
  drule payload_confluence >>
  disch_then(qspec_then ‘p2’ mp_tac) >> simp[compile_network_endpoints] >>
  strip_tac >>
  drule_all compile_network_reflection_alt >>
  strip_tac >>
  rpt(goal_assum drule)
QED

Theorem compile_network_alt_fully_abstract:
  ∀conf p1 p2.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ fix_network p2
    ∧ free_fix_names_network p2 = []
    ∧ no_undefined_vars_network p2
    ∧ BISIM_REL (trans conf) p1 p2 ⇒
    BISIM_REL (trans conf) (compile_network_alt p1) (compile_network_alt p2)
Proof
  rpt strip_tac >>
  qpat_abbrev_tac ‘q1 = compile_network_alt p1’ >>
  qpat_abbrev_tac ‘q2 = compile_network_alt p2’ >>
  ntac 2 (pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def])) >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘p1’,‘p2’,‘q2’,‘q1’] >>
  Ho_Rewrite.PURE_REWRITE_TAC[AND_IMP_INTRO,LEFT_FORALL_IMP_THM,GSYM PULL_FORALL] >>
  ho_match_mp_tac BISIM_REL_trans_sym_coind >>
  rw[]
  >- metis_tac[bisim_sym] >>
  rename1 ‘trans _ _ α’ >>
  Cases_on ‘α’
  >- (drule_all_then strip_assume_tac compile_network_reflection_send >>
      rveq >>
      qhdtm_assum ‘BISIM_REL’ (strip_assume_tac o SIMP_RULE std_ss [FORALL_AND_THM,Once bisimulationTheory.BISIM_REL_cases]) >>
      first_x_assum drule >>
      strip_tac >>
      drule_all compile_network_preservation_send >>
      strip_tac >>
      goal_assum drule >>
      irule_at (Pos hd) bisim_refl >>
      irule_at (Pos last) bisim_refl >>
      simp[] >>
      irule_at (Pos last) EQ_REFL >>
      irule_at (Pos last) EQ_REFL >>
      simp[] >>
      imp_res_tac fix_network_trans_pres >>
      imp_res_tac no_undefined_vars_network_trans_pres >>
      simp[] >>
      imp_res_tac free_fix_names_network_trans_pres >>
      gvs[])
  >- (drule_all_then strip_assume_tac compile_network_reflection_receive >>
      rveq >>
      qhdtm_assum ‘BISIM_REL’ (strip_assume_tac o SIMP_RULE std_ss [FORALL_AND_THM,Once bisimulationTheory.BISIM_REL_cases]) >>
      first_x_assum drule >>
      strip_tac >>
      drule_all compile_network_preservation_receive >>
      strip_tac >>
      goal_assum drule >>
      irule_at (Pos hd) bisim_refl >>
      irule_at (Pos last) bisim_refl >>
      simp[] >>
      irule_at (Pos last) EQ_REFL >>
      irule_at (Pos last) EQ_REFL >>
      simp[] >>
      imp_res_tac fix_network_trans_pres >>
      imp_res_tac no_undefined_vars_network_trans_pres >>
      simp[] >>
      imp_res_tac free_fix_names_network_trans_pres >>
      gvs[])
  >- (gvs[GSYM reduction_def] >>
      drule_all_then strip_assume_tac compile_network_reflection_single >>
      qhdtm_assum ‘BISIM_REL’ (strip_assume_tac o SIMP_RULE std_ss [FORALL_AND_THM,Once bisimulationTheory.BISIM_REL_cases]) >>
      gvs[reduction_def] >>
      first_x_assum drule >>
      strip_tac >>
      gvs[GSYM reduction_def] >>
      drule_all compile_network_preservation_trans_alt >>
      strip_tac >>
      goal_assum drule >>
      gvs[compile_rel_def] >>
      goal_assum drule >>
      irule_at (Pos last) bisim_sym >>
      goal_assum drule >>
      irule_at (Pos last) EQ_REFL >>
      irule_at (Pos last) EQ_REFL >>
      simp[] >>
      gvs[reduction_def] >>
      imp_res_tac fix_network_trans_pres >>
      imp_res_tac no_undefined_vars_network_trans_pres >>
      simp[] >>
      imp_res_tac free_fix_names_network_trans_pres >>
      gvs[])
QED

val _ = export_theory ();

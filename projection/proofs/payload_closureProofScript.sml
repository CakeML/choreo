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
∧ fsubst (Letrec fn' vars e1 e2) fn e' =
   (if fn = fn' then
     Letrec fn' vars e1 e2
    else
     Letrec fn' vars (fsubst e1 fn e') (fsubst e2 fn e')
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

Theorem fix_network_NPar:
  fix_network (NPar n1 n2) = (fix_network n1 ∧ fix_network n2)
Proof
  rw[fix_network_def,endpoints_def]
QED

Theorem letrec_network_NPar:
  letrec_network (NPar n1 n2) = (letrec_network n1 ∧ letrec_network n2)
Proof
  rw[letrec_network_def,endpoints_def]
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
  >- (imp_res_tac MEM_written_var_names_endpoint_until_IMP >> simp[])
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
  (∀vars e1 e2 e3 e4 dn vars' vars''.
     saturates vars e1 e2 ∧
     saturates vars e3 e4 ∧
     ALL_DISTINCT vars' ∧
     ALL_DISTINCT vars'' ∧
     set vars' ⊆ set vars ∪ set vars'' ⇒
     saturates vars (Letrec dn vars' e1 e3) (Letrec dn vars'' e2 e4)) ∧
  (∀vars dn vars' vars''.
     ALL_DISTINCT vars' ∧
     ALL_DISTINCT vars'' ∧
     set vars' ⊆ set vars ∪ set vars'' ⇒
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
    (conj_tac >- (first_x_assum match_mp_tac >> rw[] >> fs[all_distinct_nub'] >> res_tac) >>
     simp[Once saturates_cases,all_distinct_nub']) >>
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
  LIST_REL (λ(s,vs) (s',vs'). s = s' ∧ set vs ⊆ set vs' ∪ set vars) ar ar'
  ⇒
  saturates vars (compile_endpoint ar e) (compile_endpoint ar' e)
Proof
  Induct_on ‘e’ >> rw[compile_endpoint_def] >>
  simp[Once saturates_cases] >>
  TRY(res_tac >> NO_TAC)
  >- metis_tac[]
  >- (simp[all_distinct_nub'] >>
      reverse conj_tac >- (simp[Once saturates_cases,all_distinct_nub']) >>
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
  (arities (Letrec dn vars e1 e2) =
   FILTER ($≠ dn o FST) (arities e1 ++ arities e2)) ∧
  (arities (FCall dn vars) = [(dn,LENGTH vars)]) ∧
  (arities (Fix dn e) = arities e) ∧
  (arities (Call dn) = [])
End

Definition consistent_arities_def:
  (consistent_arities payloadLang$Nil = T) ∧
  (consistent_arities (Send p v n e) = consistent_arities e) ∧
  (consistent_arities (Receive p v l e) = consistent_arities e) ∧
  (consistent_arities (IfThen v e1 e2) =
   (consistent_arities e1 ∧ consistent_arities e2)) ∧
  (consistent_arities (Let v f vl e) =
   consistent_arities e) ∧
  (consistent_arities (Letrec dn vars e1 e2) =
   (consistent_arities e1 ∧ consistent_arities e2 ∧
    (∀dn n n'. MEM (dn,n) (arities e1) ∧ MEM (dn,n') (arities e2) ⇒ n = n'))) ∧
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
              (compile_endpoint ((dn,nub'(written_var_names_endpoint_until e))::ar) e')
              e''
Proof
  strip_tac >> Induct >> rpt strip_tac
  >- ((* Nil *)
      fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def,Once saturates_cases])
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
        reverse conj_tac
        >- (simp[Once saturates_cases,all_distinct_nub']) >>
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
                     metis_tac[SUBSET_TRANS,set_written_var_names_endpoint_until,SUBSET_UNION]) >>
        match_mp_tac EVERY2_refl >>
        rw[] >>
        pairarg_tac >> rveq >> fs[]) >>
     fs[written_var_names_endpoint_def] >>
     metis_tac[SUBSET_TRANS,set_written_var_names_endpoint_until,SUBSET_UNION]
     )
  >- (fs[dsubst_def,fix_endpoint_def,fsubst_def,compile_endpoint_def] >>
      reverse(rw[] >> fs[compile_endpoint_def,fsubst_def]) >-
       (TOP_CASE_TAC >> rw[] >>
        simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
        res_tac) >>
      fs[free_fix_names_endpoint_def] >>
      simp[Once saturates_cases,PULL_EXISTS,fsubst_def] >>
      goal_assum(resolve_then (Pos hd) mp_tac compile_endpoint_ALOOKUP_eq_strong) >>
      fs[FILTER_EQ_NIL,EVERY_MEM] >>
      metis_tac[SUBSET_UNION,all_distinct_nub'])
  >- (fs[fix_endpoint_def])
  >- (fs[fix_endpoint_def])
QED

Definition compile_rel_def:
  compile_rel conf n1 n2 =
  (letrec_network n1 ∧ letrec_network n2 ∧
   tausim conf n1 n2
  )
End

Theorem compile_rel_refl:
  letrec_network x ⇒ compile_rel conf x x
Proof
  rw[compile_rel_def,tausim_refl]
QED

Theorem compile_rel_reflI:
  ∀conf x y. letrec_network x ∧ x = y ⇒ compile_rel conf x y
Proof
  simp[compile_rel_refl]
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

Definition arsof_def:
  arsof dn e = set(MAP SND (FILTER ($= dn o FST) (arities e)))
End

Definition closure_args_def:
  closure_args (Closure vars1 env e) = vars1
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

Theorem MEM_arities_arsof:
  ∀dn n vars e.
    MEM (dn,n) (arities e) ⇒
    n ∈ arsof dn e
Proof
  rw[arsof_def,MEM_MAP,MEM_FILTER] >>
  metis_tac[FST,SND]
QED

Definition compile_fix_closure_rel_def:
  compile_fix_closure_rel dn e vars (Closure vars1 (fs1,bds1) e1) (Closure vars2 (fs2,bds2) e2) ⇔
  ∃e'.
    bds1 = bds2 ∧
    letrec_endpoint e ∧ letrec_endpoint e1 ∧ letrec_endpoint e2 ∧
    consistent_arities e ∧ consistent_arities e1 ∧ consistent_arities e2 ∧
    set(written_var_names_endpoint e) DIFF set vars ⊆ FDOM bds1 ∧
    set(written_var_names_endpoint_before dn e1) ⊆ set vars ∧
    set(written_var_names_endpoint e1) ⊆ set(written_var_names_endpoint e) ∧
    ALL_DISTINCT vars ∧
    saturates vars e1 e' ∧
    set(free_fun_names_endpoint e) ⊆ {dn} ∧
    e2 = fsubst e' dn
                (Letrec dn vars e (FCall dn vars)) ∧
    ALL_DISTINCT vars1 ∧ ALL_DISTINCT vars2 ∧
    set vars1 ⊆ set(written_var_names_endpoint e) ∪ set vars2 ∧
    (∃fs3 bds3.
        ALOOKUP fs1 dn = SOME(Closure vars (fs3,bds3) e) ∧
        (MEM dn (free_fun_names_endpoint e1) ⇒
         DRESTRICT bds3 (λk. ~MEM k vars) =
         DRESTRICT bds1 (λk. ~MEM k vars))
    ) ∧
    (∀dn' ar1.
      dn ≠ dn' ∧ MEM (dn',ar1) (arities e1) ⇒
      ∃cl1 cl2. ALOOKUP fs1 dn' = SOME cl1 ∧ ALOOKUP fs2 dn' = SOME cl2 ∧
                arsof dn' e' = {LENGTH(closure_args cl2)} ∧
                (ALOOKUP fs1 dn' = SOME cl1 ∧ ALOOKUP fs2 dn' = SOME cl2 ⇒
                 compile_fix_closure_rel dn e vars cl1 cl2))
Termination
  WF_REL_TAC ‘inv_image $< (closure_size o FST o SND o SND o SND)’ >>
  rw[closure_size_def] >> imp_res_tac ALOOKUP_MEM >>
  imp_res_tac closure_size_MEM >>
  DECIDE_TAC
End

Definition compile_fix_closure_endpoint_rel_def:
  compile_fix_closure_endpoint_rel vars dn e n1 n2 ⇔
  ∃p s1 s2 e1 e'.
    s1.queues = s2.queues ∧
    s1.bindings = s2.bindings ∧
    n1 = NEndpoint p s1 e1 ∧
    n2 = NEndpoint p s2 (fsubst e' dn
                         (Letrec dn vars e (FCall dn vars))) ∧
    saturates (written_var_names_endpoint e) e1 e' ∧
    letrec_endpoint e ∧ letrec_endpoint e1 ∧ letrec_endpoint e' ∧
    consistent_arities e ∧ consistent_arities e1 ∧ consistent_arities e' ∧
    set vars ⊆ set(written_var_names_endpoint e) ∧
    set(written_var_names_endpoint e) DIFF set vars ⊆ FDOM s2.bindings ∧
    set(written_var_names_endpoint_before dn e1) ⊆ set vars ∧
    set(free_fun_names_endpoint e) ⊆ {dn} ∧
    set(written_var_names_endpoint e1) ⊆ set(written_var_names_endpoint e) ∧
    ALL_DISTINCT vars ∧
    (∃fs3 bds3.
        ALOOKUP s1.funs dn = SOME(Closure vars (fs3,bds3) e) ∧
        (MEM dn (free_fun_names_endpoint e1) ⇒
         DRESTRICT bds3 (λk. ~MEM k vars) =
         DRESTRICT s1.bindings (λk. ~MEM k vars))
    ) ∧
    (∀dn' ar1.
      dn ≠ dn' ∧ MEM (dn',ar1) (arities e1) ⇒
      ∃cl1 cl2. ALOOKUP s1.funs dn' = SOME cl1 ∧ ALOOKUP s2.funs dn' = SOME cl2 ∧
                arsof dn' e' = {LENGTH(closure_args cl2)} ∧
                compile_fix_closure_rel dn e vars cl1 cl2)
End

Theorem arsof_simps[simp]:
  arsof dn (Send p v n e) = arsof dn e ∧
  arsof dn (Receive p v d e) = arsof dn e ∧
  arsof dn (Let v f vl e) = arsof dn e ∧
  arsof dn (IfThen v e1 e2) = arsof dn e1 ∪ arsof dn e2
Proof
  rw[arsof_def,arities_def,FILTER_APPEND]
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

Theorem tausim_defer_fundef:
  ∀conf dn e vars n1 n2.
    compile_fix_closure_endpoint_rel vars dn e n1 n2 ⇒
    tausim conf n1 n2
Proof
  ntac 4 strip_tac >>
  ho_match_mp_tac tausim_strong_coind >> rw[]
  >- ((* Non-tau, LHS leads *)
      qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[Once trans_cases]) >>
      fs[] >> rveq
      >- ((* trans_send_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,written_var_names_endpoint_def] >>
          metis_tac[])
      >- ((* trans_send_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          rw[Once saturates_cases,PULL_EXISTS] >>
          rw[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,free_fun_names_endpoint_def,
             written_var_names_endpoint_before_def,written_var_names_endpoint_def] >>
          metis_tac[])
      >- ((* trans_enqueue *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_enqueue) >>
          simp[] >>
          disj1_tac >> fs[compile_fix_closure_endpoint_rel_def] >>
          metis_tac[])
      >- ((* trans_par_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_par_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def]))
  >- ((* Non-tau, RHS leads *)
      qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[Once trans_cases]) >>
      fs[] >> rveq
      >- ((* trans_send_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[CaseEq "bool"] >> rveq >> fs[] >>
          Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
              written_var_names_endpoint_def,free_fun_names_endpoint_def] >>
          metis_tac[])
      >- ((* trans_send_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[CaseEq "bool"] >> rveq >> fs[] >>
          Cases_on ‘e''’ >> fs[fsubst_def,CaseEq "bool"] >> rveq >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_send_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          rw[Once saturates_cases,PULL_EXISTS] >>
          rw[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_before_def,
             written_var_names_endpoint_def,free_fun_names_endpoint_def] >>
          metis_tac[])
      >- ((* trans_enqueue *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_enqueue) >>
          simp[] >>
          disj1_tac >> fs[compile_fix_closure_endpoint_rel_def] >>
          metis_tac[])
      >- ((* trans_par_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_par_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def]))
  >- ((* Tau, LHS leads *)
      qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[Once trans_cases]) >>
      fs[] >> rveq
      >- ((* trans_com_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_com_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_dequeue_last_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_last_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def]
          >- (fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
                 written_var_names_endpoint_before_def] >>
              PURE_FULL_CASE_TAC >> fs[] >>
              conj_tac >- (fs[SUBSET_DEF]) >>
              conj_tac >- (fs[written_var_names_endpoint_before_fresh_eq_NIL]) >>
              metis_tac[]) >>
          fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
                 written_var_names_endpoint_before_def] >>
          PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> metis_tac[])
      >- ((* trans_dequeue_intermediate_payload *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_dequeue_intermediate_payload) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
          simp[Once saturates_cases] >>
          simp[PULL_EXISTS,fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          metis_tac[])
      >- ((* trans_if_true *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_true) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rw[] >>
          res_tac >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_if_true *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_if_false) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def,written_var_names_endpoint_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def] >>
          fs[free_fun_names_endpoint_def,written_var_names_endpoint_before_def] >>
          fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
          rw[] >>
          res_tac >>
          drule_all_then strip_assume_tac MEM_arities_saturates >>
          imp_res_tac MEM_arities_arsof >>
          fs[] >>
          fs[SET_EQ_SUBSET,SUBSET_DEF] >>
          metis_tac[])
      >- ((* trans_let *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac trans_let) >>
          fs[] >>
          disj1_tac >>
          rw[compile_fix_closure_endpoint_rel_def] >>
          goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          fs[letrec_endpoint_def,consistent_arities_def,arities_def]
          >- (fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
                 written_var_names_endpoint_before_def] >>
              PURE_FULL_CASE_TAC >> fs[] >>
              conj_tac >- (fs[SUBSET_DEF]) >>
              conj_tac >- (fs[written_var_names_endpoint_before_fresh_eq_NIL]) >>
              metis_tac[]) >>
          fs[written_var_names_endpoint_def,free_fun_names_endpoint_def,
                 written_var_names_endpoint_before_def] >>
          PURE_FULL_CASE_TAC >> fs[written_var_names_endpoint_before_fresh_eq_NIL] >> metis_tac[])
      >- ((* trans_par_l (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_par_r (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def])
      >- ((* trans_fix (impossible) *)
          fs[compile_fix_closure_endpoint_rel_def,letrec_endpoint_def])
      >- ((* trans_letrec *)
          qhdtm_x_assum ‘compile_fix_closure_endpoint_rel’ (strip_assume_tac o REWRITE_RULE[compile_fix_closure_endpoint_rel_def]) >> fs[] >> rveq >> fs[] >>
          fs[Once saturates_cases] >> rveq >> fs[fsubst_def] >>
          IF_CASES_TAC >-
            (rveq >>
             fs[free_fun_names_endpoint_def,MEM_FILTER] >>
             goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
             simp[reduction_def] >>
             goal_assum(resolve_then (Pos hd) mp_tac trans_letrec) >>
             cheat (* not at all obvious. change candidate relation? alpha-convert? *)
            ) >>
          cheat
         )
      >> cheat
     )
  >- ((* Tau, RHS leads *)
      cheat
     )
QED

Theorem compile_network_preservation_trans:
  ∀p1 p2 conf.
    conf.payload_size > 0
    ∧ fix_network p1
    ∧ free_fix_names_network p1 = []
    ∧ no_undefined_vars_network p1
    ∧ reduction conf p1 p2
    ⇒ ∃p3. (reduction conf)^* (compile_network_alt p1) p3 ∧
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
      >> drule_then strip_assume_tac RTC_SUBSET
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
      >> drule_then strip_assume_tac RTC_SUBSET
      >> goal_assum drule
      >> metis_tac[compile_rel_refl,fix_network_NPar,letrec_network_compile_network_alt,
                   letrec_network_trans_pres,letrec_network_NPar])
  >- ((* trans_dequeue_last_payload *)
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      match_mp_tac bisim_IMP_tausim >>
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
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      match_mp_tac bisim_IMP_tausim >>
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
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) payloadPropsTheory.reduction_par_l >>
      fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
      drule_then MATCH_ACCEPT_TAC tausim_par_left)
  >- ((* trans_par_r *)
      fs[compile_network_alt_def,fix_network_NPar,free_fix_names_network_def,no_undefined_vars_network_NPar] >>
      drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) payloadPropsTheory.reduction_par_r >>
      fs[compile_rel_def,letrec_network_NPar,letrec_network_compile_network_alt] >>
      drule_then MATCH_ACCEPT_TAC tausim_par_right)
  >- ((* trans_fix *)
      goal_assum (resolve_then (Pos hd) mp_tac RTC_TRANS) >>
      simp[reduction_def,compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases] >>
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
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
      qmatch_goalsub_abbrev_tac ‘tausim _ (NEndpoint _ (_ with <|bindings := b1; funs := _|>) _)
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
      simp[Abbr ‘a2’] >>
      pop_assum kall_tac >>
      match_mp_tac tausim_defer_fundef >>
      simp[compile_fix_closure_endpoint_rel_def,letrec_endpoint_compile_endpoint,all_distinct_nub',
           set_nub'] >>
      simp[saturates_nub'] >>
      goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      simp[FDOM_FUPDATE_LIST,MAP_MAP_o,LIST_TO_SET_MAP] >>
      cheat)
  >- ((* trans_Letrec *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
  >- ((* trans_call *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
QED

(*
Theorem compile_network_preservation:
  ∀conf p1 p2.
    conf.payload_size > 0
    ∧ reduction^* p1 p2 ∧ choice_free_network p1
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
Proof
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
  >> rpt(disch_then drule) >> strip_tac >> metis_tac[RTC_RTC]
QED
*)

val _ = export_theory ();

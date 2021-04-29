open preamble choreoUtilsTheory
              endpointLangTheory chor_to_endpointTheory
              endpointSemTheory endpointPropsTheory
              endpointCongTheory chorSemTheory chorPropsTheory
              endpointConfluenceTheory chorConfluenceTheory
              chorSyncPropsTheory;

val _ = new_theory "chor_to_endpointProof";

val _ = set_grammar_ancestry
  ["endpointProps","endpointLang","endpointConfluence","chor_to_endpoint","chorProps","chorSyncProps",
   "chor_to_endpointProof","chorSem","chorLang"];

Theorem split_sel_dvars:
  ∀proc p c b r.
  split_sel proc p c = SOME (b,r) ⇒
  dvarsOf c = dvarsOf r
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[split_sel_def,dvarsOf_def] >>
  rw[nub'_dvarsOf]
QED

Theorem split_sel_procsOf:
  ∀proc p c b r.
  split_sel proc p c = SOME (b,r) ⇒
  set(procsOf r) ⊆ set(procsOf c)
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[split_sel_def,procsOf_def,set_nub'] >>
  rw[SUBSET_DEF] >>
  res_tac >>
  gs[SUBSET_DEF]
QED

Theorem split_sel_size:
  ∀proc p c b r.
  split_sel proc p c = SOME (b,r) ⇒
  chor_to_endpoint$chor_size r ≤ chor_to_endpoint$chor_size c
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[split_sel_def,chor_to_endpointTheory.chor_size_def] >>
  res_tac >>
  DECIDE_TAC
QED

Theorem split_sel_procsOf:
  ∀proc p c b r.
  split_sel proc p c = SOME (b,r) ⇒
  set(procsOf r) ⊆ set(procsOf c)
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[split_sel_def,procsOf_def,set_nub'] >>
  rw[SUBSET_DEF] >>
  res_tac >>
  gs[SUBSET_DEF]
QED

Theorem project_ALOOKUP_EQ:
  ∀proc dvars c dvars'.
    (∀dn. MEM dn (dvarsOf c) ⇒
       ALOOKUP dvars dn = ALOOKUP dvars' dn)
    ⇒
    project proc dvars c = project proc dvars' c
Proof
  ho_match_mp_tac project_ind >>
  rw[project_def,dprocsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
  TRY(conj_tac
      >- (‘dprocsOf ((dn,[])::dvars) c = dprocsOf ((dn,[])::dvars') c’ suffices_by metis_tac[] >>
          match_mp_tac dprocsOf_ALOOKUP_EQ >>
          rw[]) >>
      ‘dprocsOf ((dn,[])::dvars') c = dprocsOf ((dn,[])::dvars) c’
        by(match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]) >>
      simp[] >>
      last_x_assum(qspec_then ‘(dn,dprocsOf ((dn,[])::dvars) c)::dvars'’ mp_tac) >>
      impl_tac >- rw[] >>
      simp[] >> NO_TAC) >>
  TRY(‘dprocsOf ((dn,[])::dvars') c = dprocsOf ((dn,[])::dvars) c’
        by(match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]) >>
      simp[] >> NO_TAC) >>
  metis_tac[split_sel_dvars,FST,SND]
QED

Theorem project_ALOOKUP_EQ_strong:
  ∀proc dvars c dvars'.
    (∀dn. MEM dn (dvarsOf c) ⇒
       OPTION_REL (λx y. set x = set y) (ALOOKUP dvars dn) (ALOOKUP dvars' dn))
    ⇒
    project proc dvars c = project proc dvars' c
Proof
  ho_match_mp_tac project_ind >>
  rw[project_def,dprocsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS,libTheory.the_def] >>
  res_tac >> gs[CaseEq "bool"] >>
  rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
  gs[libTheory.the_def] >>
  TRY(conj_tac
      >- (‘set(dprocsOf ((dn,[])::dvars) c) = set(dprocsOf ((dn,[])::dvars') c)’ suffices_by metis_tac[] >>
          match_mp_tac dprocsOf_ALOOKUP_EQ_set_opt >>
          rw[]) >>
      last_x_assum(qspec_then ‘(dn,dprocsOf ((dn,[])::dvars') c)::dvars'’ mp_tac) >>
      impl_tac >-
       (rw[libTheory.the_def] >>
        match_mp_tac dprocsOf_ALOOKUP_EQ_set_opt >>
        rw[]) >>
      simp[] >> NO_TAC) >>
  TRY(‘set(dprocsOf ((dn,[])::dvars') c) = set(dprocsOf ((dn,[])::dvars) c)’
        by(CONV_TAC SYM_CONV >>
           match_mp_tac dprocsOf_ALOOKUP_EQ_set_opt >> rw[] >>
           first_x_assum match_mp_tac) >>
      simp[] >> NO_TAC) >>
  metis_tac[split_sel_dvars,FST,SND]
QED

Theorem project_init_dup:
  project proc ((dn,dvs)::(dn,dvs')::dvars) c = project proc ((dn,dvs)::dvars) c
Proof
  match_mp_tac project_ALOOKUP_EQ >> rw[]
QED

Theorem project_dvarsOf_empty:
  dvarsOf c = [] ⇒
  project proc dvars c = project proc [] c
Proof
  strip_tac >>
  match_mp_tac project_ALOOKUP_EQ >>
  rw[]
QED

Theorem project_dvarsOf_empty_Fix:
  dvarsOf (Fix dn c) = [] ⇒
  project proc ((dn,procs)::dvars) c = project proc [(dn,procs)] c
Proof
  rw[dvarsOf_def,FILTER_EQ_NIL,EVERY_MEM,MEM_nub'] >>
  match_mp_tac project_ALOOKUP_EQ >>
  rw[]
QED

Theorem split_sel_dsubst_NONE:
  split_sel proc p c = NONE ⇒
  split_sel proc p (dsubst c dn (Fix dn c')) = NONE
Proof
  Induct_on ‘c’ >> rw[chorLangTheory.dsubst_def,split_sel_def]
QED

Theorem split_sel_dsubst_SOME:
  split_sel proc p c = SOME(b,c'') ⇒
  split_sel proc p (dsubst c dn (Fix dn c')) = SOME(b,dsubst c'' dn (Fix dn c'))
Proof
  MAP_EVERY qid_spec_tac [‘b’,‘c''’] >>
  Induct_on ‘c’ >> rw[chorLangTheory.dsubst_def,split_sel_def]
QED

Theorem split_sel_dsubst_eq:
  split_sel proc p (dsubst c dn (Fix dn c')) =
  OPTION_MAP (λ(b,c''). (b,dsubst c'' dn (Fix dn c'))) (split_sel proc p c)
Proof
  Cases_on ‘split_sel proc p c’ >- simp[split_sel_dsubst_NONE] >>
  simp[] >>
  pairarg_tac >> gs[split_sel_dsubst_SOME]
QED

Theorem split_sel_nonproc_NONE:
  ∀p p1 c.
  ~MEM p (procsOf c) ⇒ split_sel p p1 c = NONE
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[procsOf_def,MEM_nub'] >>
  fs[split_sel_def]
QED

Theorem split_sel_nondproc_NONE:
  ∀p dvars p1 c.
  ~MEM p (dprocsOf dvars c) ⇒ split_sel p p1 c = NONE
Proof
  metis_tac[split_sel_nonproc_NONE,dprocsOf_MEM_eq]
QED

Theorem project_nonmember_nil_lemma:
  ∀proc dvars c.
  ~MEM proc (dprocsOf dvars c) ∧
  set(dvarsOf c) ⊆ set(MAP FST dvars)
  ⇒
  project proc dvars c = (T,Nil)
Proof
  ho_match_mp_tac project_ind >>
  rw[project_def,procsOf_def,dprocsOf_def,MEM_nub',dvarsOf_def,set_nub'] >>
  fs[AllCaseEqs()] >>
  imp_res_tac split_sel_nondproc_NONE >>
  fs[] >>
  PURE_FULL_CASE_TAC >> fs[] >>
  fs[ALOOKUP_NONE]
QED

Theorem project_nonmember_nil_lemma':
  ∀proc dvars c.
  ~MEM proc (dprocsOf dvars c)
  ⇒
  ∃b. project proc dvars c = (b,Nil)
Proof
  ho_match_mp_tac project_ind >>
  rw[project_def,procsOf_def,dprocsOf_def,MEM_nub',dvarsOf_def,set_nub'] >>
  fs[AllCaseEqs()] >>
  imp_res_tac split_sel_nondproc_NONE >>
  fs[] >>
  PURE_FULL_CASE_TAC >> fs[] >>
  fs[ALOOKUP_NONE]
QED

Theorem split_sel_project_ok:
  !h p c b r. h <> p /\ split_sel h p c = SOME (b,r)
   /\ project_ok h dvars r
   ==> project_ok h dvars c
Proof
  Induct_on `c` >> rw[project_def,split_sel_def]
  >> metis_tac[]
QED

Theorem split_sel_project_ok2:
  !h p c b r. h <> p /\ split_sel h p c = SOME (b,r)
   /\ project_ok h dvars c
   ==> project_ok h dvars r
Proof
  Induct_on `c` >> rw[project_def,split_sel_def]
  >> metis_tac[]
QED

Theorem project'_dsubst_commute:
  ∀dn c proc c' dvars.
  dvarsOf(Fix dn c) = [] ∧
  project_ok proc dvars (Fix dn c) ∧
  project_ok proc ((dn,dprocsOf ((dn,[])::dvars) c)::dvars) c' ∧
  (∀dn procs. ALOOKUP dvars dn = SOME procs ⇒ set procs ⊆ set(procsOf c)) ∧
  set(procsOf c') ⊆ set(procsOf c)
  ⇒
  (project' proc dvars (dsubst c' dn (Fix dn c)) =
   dsubst (project' proc ((dn,dprocsOf ((dn,[])::dvars) c)::dvars) c') dn (project' proc dvars (Fix dn c)) ∧
   project_ok proc dvars (dsubst c' dn (Fix dn c)))
Proof
  ntac 3 strip_tac >>
  completeInduct_on ‘chor_to_endpoint$chor_size c'’ >>
  Cases >> rpt conj_tac
  >- (rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,SUBSET_DEF])
  >- (rename [‘IfThen v p c1 c2’] >>
      strip_tac >> fs[chor_size_def] >> rveq >>
      rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,set_nub',SUBSET_DEF,chor_size_def] >> fs[]
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          simp[project_def] >>
          impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
          simp[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              simp[project_def] >>
              impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
              simp[]) >>
          pairarg_tac >> fs[] >> rveq >>
          rw[] >> fs[] >>
          pairarg_tac >> fs[] >> rveq >>
          rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          conj_tac >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_x_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              simp[project_def] >>
              impl_tac >- (rw[SUBSET_DEF] >> metis_tac[]) >>
              simp[]) >>
          pairarg_tac >> fs[] >> rveq >>
          rw[] >> fs[] >>
          pairarg_tac >> fs[] >> rveq >>
          rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (spose_not_then kall_tac >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              qpat_x_assum ‘_ ≠ _’ mp_tac >>
              simp[PAIR_FST_SND_EQ]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok]) >>
          strip_tac >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST]) >>
          strip_tac >>
          qpat_x_assum ‘_ ≠ _’ mp_tac >>
          simp[PAIR_FST_SND_EQ])
      >- (spose_not_then kall_tac >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              qpat_x_assum ‘_ ≠ _’ mp_tac >>
              simp[PAIR_FST_SND_EQ]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok]) >>
          strip_tac >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST]) >>
          strip_tac >>
          qpat_x_assum ‘_ ≠ _’ mp_tac >>
          simp[PAIR_FST_SND_EQ])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          fs[endpointLangTheory.dsubst_def] >>
          conj_tac >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          fs[endpointLangTheory.dsubst_def] >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          conj_tac >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (gs[dprocsOf_MEM_eq])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >> simp[project_def]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          rename1 ‘split_sel proc p c1 = SOME(_,c1')’ >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1'’ mp_tac) >>
          impl_tac >- (imp_res_tac split_sel_size >> DECIDE_TAC) >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,split_sel_procsOf]) >>
          strip_tac >>
          rename1 ‘split_sel proc p c2 = SOME(_,c2')’ >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2'’ mp_tac) >>
          impl_tac >- (imp_res_tac split_sel_size >> DECIDE_TAC) >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST,split_sel_procsOf]) >>
          strip_tac >>
          simp[dsubst_def,project_def])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >> simp[project_def]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          rename1 ‘split_sel proc p c1 = SOME(_,c1')’ >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1'’ mp_tac) >>
          impl_tac >- (imp_res_tac split_sel_size >> DECIDE_TAC) >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,split_sel_procsOf]) >>
          strip_tac >>
          rename1 ‘split_sel proc p c2 = SOME(_,c2')’ >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2'’ mp_tac) >>
          impl_tac >- (imp_res_tac split_sel_size >> DECIDE_TAC) >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST,split_sel_procsOf]) >>
          strip_tac >>
          simp[dsubst_def,project_def])
      >- (spose_not_then kall_tac >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              qpat_x_assum ‘_ ≠ _’ mp_tac >>
              simp[PAIR_FST_SND_EQ]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok]) >>
          strip_tac >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST]) >>
          strip_tac >>
          qpat_x_assum ‘_ ≠ _’ mp_tac >>
          simp[PAIR_FST_SND_EQ])
      >- (spose_not_then kall_tac >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[]
          >- (last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
              impl_tac >- simp[] >>
              disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
              disch_then(qspec_then ‘dvars’ mp_tac) >>
              impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF]) >>
              strip_tac >>
              qpat_x_assum ‘_ ≠ _’ mp_tac >>
              simp[PAIR_FST_SND_EQ]) >>
          rpt(PURE_FULL_CASE_TAC >> gs[] >> rveq) >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c1’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok]) >>
          strip_tac >>
          last_assum(qspec_then ‘chor_to_endpoint$chor_size c2’ mp_tac) >>
          impl_tac >- simp[] >>
          disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
          disch_then(qspec_then ‘dvars’ mp_tac) >>
          impl_tac >- (simp[project_def] >> metis_tac[SUBSET_DEF,split_sel_project_ok,FST]) >>
          strip_tac >>
          qpat_x_assum ‘_ ≠ _’ mp_tac >>
          simp[PAIR_FST_SND_EQ])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          fs[endpointLangTheory.dsubst_def] >>
          conj_tac >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          fs[endpointLangTheory.dsubst_def] >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          conj_tac >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[])
      >- (fs[split_sel_dsubst_eq] >>
          Cases_on ‘split_sel proc p c1’ >> gs[] >>
          Cases_on ‘split_sel proc p c2’ >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          pairarg_tac >> gs[] >> rveq >> rw[] >> fs[] >>
          simp[endpointLangTheory.dsubst_def] >>
          fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
          rfs[FORALL_AND_THM] >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          last_x_assum (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          simp[project_def] >>
          imp_res_tac split_sel_procsOf >>
          imp_res_tac split_sel_size >>
          gs[SUBSET_DEF] >>
          metis_tac[]))
  >- (rename1 ‘Com _ _ _ _ c'’ >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c'’ assume_tac) >>
      strip_tac >> fs[chor_size_def] >>
      PRED_ASSUM is_forall (resolve_then (Pos hd) assume_tac EQ_REFL) >>
      strip_tac >>
      first_x_assum(qspec_then ‘dvars’ mp_tac) >>
      rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,set_nub',SUBSET_DEF,chor_size_def] >> fs[] >> metis_tac[])
  >- (rename1 ‘Let _ _ _ _ c'’ >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c'’ assume_tac) >>
      strip_tac >> fs[chor_size_def] >>
      PRED_ASSUM is_forall (resolve_then (Pos hd) assume_tac EQ_REFL) >>
      strip_tac >>
      first_x_assum(qspec_then ‘dvars’ mp_tac) >>
      rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,set_nub',SUBSET_DEF,chor_size_def] >> fs[] >> metis_tac[])
  >- (rename1 ‘Sel _ _ _ c'’ >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c'’ assume_tac) >>
      strip_tac >> fs[chor_size_def] >>
      PRED_ASSUM is_forall (resolve_then (Pos hd) assume_tac EQ_REFL) >>
      strip_tac >>
      first_x_assum(qspec_then ‘dvars’ mp_tac) >>
      rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,set_nub',SUBSET_DEF,chor_size_def] >> fs[] >> metis_tac[])
  >- (rename1 ‘chor_size(Fix dn' c')’ >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c'’ assume_tac) >>
      strip_tac >> fs[chor_size_def] >>
      PRED_ASSUM is_forall (resolve_then (Pos hd) assume_tac EQ_REFL) >>
      rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def,procsOf_def,set_nub'] >> fs[] >>
      fs[dprocsOf_init_dup,project_init_dup] >>
      gs[dprocsOf_dvarsOf_empty_cons,dprocsOf_empty]
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub']
          >- (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              qpat_x_assum ‘∀dvars. _ ⇒ project' _ _ _ = _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
              conj_asm1_tac
              >- (gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
                  fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                  qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
                  qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
                  ‘project proc adv1 c = project proc adv2 c’
                    by(unabbrev_all_tac >>
                       match_mp_tac project_ALOOKUP_EQ_strong >>
                       rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                          CaseEq "bool"] >>
                       fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                       res_tac >>
                       imp_res_tac SUBSET_THM >>
                       PURE_FULL_CASE_TAC >> fs[] >>
                       rveq >> fs[] >>
                       metis_tac[SUBSET_THM]) >>
                  fs[] >>
                  unabbrev_all_tac >>
                  conj_tac >-
                    (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                     qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                     ‘project proc adv1 c' = project proc adv2 c'’
                       by(unabbrev_all_tac >>
                          match_mp_tac project_ALOOKUP_EQ_strong >>
                          rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                             CaseEq "bool"] >>
                          gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                          res_tac >>
                          imp_res_tac SUBSET_THM >> fs[] >>
                          TRY PURE_FULL_CASE_TAC >> fs[] >>
                          rveq >> fs[] >>
                          metis_tac[SUBSET_THM]) >>
                     fs[]) >>
                  rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
                  gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
                  res_tac >>
                  imp_res_tac SUBSET_THM >> fs[] >>
                  TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
                  rveq >> fs[] >>
                  metis_tac[SUBSET_THM]) >>
              simp[project_def] >>
              gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              fs[set_dvarsOf_dsubst_eq] >>
              fs[project_dvarsOf_empty_Fix] >>
              qmatch_goalsub_abbrev_tac ‘dsubst _ _ (Fix _ (project' proc adv1 c)) = dsubst _ _ (Fix _ (project' proc adv2 c))’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >> fs[] >>
                   TRY PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              AP_THM_TAC >>
              AP_THM_TAC >>
              AP_TERM_TAC >>
              AP_TERM_TAC >>
              match_mp_tac project_ALOOKUP_EQ_strong >>
              rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                 CaseEq "bool"] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]) >>
          gs[CaseEq "bool"] >> rveq >> gs[]
          >- (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              qpat_x_assum ‘∀dvars. _ ⇒ project' _ _ _ = _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
              conj_asm1_tac
              >- (gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
                  fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                  qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
                  qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
                  ‘project proc adv1 c = project proc adv2 c’
                    by(unabbrev_all_tac >>
                       match_mp_tac project_ALOOKUP_EQ_strong >>
                       rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                          CaseEq "bool"] >>
                       fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                       res_tac >>
                       imp_res_tac SUBSET_THM >>
                       PURE_FULL_CASE_TAC >> fs[] >>
                       rveq >> fs[] >>
                       metis_tac[SUBSET_THM]) >>
                  fs[] >>
                  unabbrev_all_tac >>
                  conj_tac >-
                    (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                     qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                     ‘project proc adv1 c' = project proc adv2 c'’
                       by(unabbrev_all_tac >>
                          match_mp_tac project_ALOOKUP_EQ_strong >>
                          rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                             CaseEq "bool"] >>
                          gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                          res_tac >>
                          imp_res_tac SUBSET_THM >> fs[] >>
                          TRY PURE_FULL_CASE_TAC >> fs[] >>
                          rveq >> fs[] >>
                          metis_tac[SUBSET_THM]) >>
                     fs[]) >>
                  rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
                  gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
                  res_tac >>
                  imp_res_tac SUBSET_THM >> fs[] >>
                  TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
                  rveq >> fs[] >>
                  metis_tac[SUBSET_THM]) >>
              simp[project_def] >>
              gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              fs[set_dvarsOf_dsubst_eq] >>
              fs[project_dvarsOf_empty_Fix] >>
              qmatch_goalsub_abbrev_tac ‘dsubst _ _ (Fix _ (project' proc adv1 c)) = dsubst _ _ (Fix _ (project' proc adv2 c))’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >> fs[] >>
                   TRY PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              AP_THM_TAC >>
              AP_THM_TAC >>
              AP_TERM_TAC >>
              AP_TERM_TAC >>
              match_mp_tac project_ALOOKUP_EQ_strong >>
              rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                 CaseEq "bool"] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]) >>
          reverse IF_CASES_TAC
          >- (fs[] >> first_x_assum(qspecl_then [‘dn''’,‘procs’] mp_tac) >> simp[] >>
              fs[set_dvarsOf_dsubst_eq]) >>
          gs[]
          >> (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              qpat_x_assum ‘∀dvars. _ ⇒ project' _ _ _ = _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
              conj_asm1_tac
              >- (gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
                  fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                  qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
                  qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
                  ‘project proc adv1 c = project proc adv2 c’
                    by(unabbrev_all_tac >>
                       match_mp_tac project_ALOOKUP_EQ_strong >>
                       rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                          CaseEq "bool"] >>
                       fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                       res_tac >>
                       imp_res_tac SUBSET_THM >>
                       PURE_FULL_CASE_TAC >> fs[] >>
                       rveq >> fs[] >>
                       metis_tac[SUBSET_THM]) >>
                  fs[] >>
                  unabbrev_all_tac >>
                  conj_tac >-
                    (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                     qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                     ‘project proc adv1 c' = project proc adv2 c'’
                       by(unabbrev_all_tac >>
                          match_mp_tac project_ALOOKUP_EQ_strong >>
                          rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                             CaseEq "bool"] >>
                          gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                          res_tac >>
                          imp_res_tac SUBSET_THM >> fs[] >>
                          TRY PURE_FULL_CASE_TAC >> fs[] >>
                          rveq >> fs[] >>
                          metis_tac[SUBSET_THM]) >>
                     fs[]) >>
                  rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
                  gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
                  res_tac >>
                  imp_res_tac SUBSET_THM >> fs[] >>
                  TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
                  rveq >> fs[] >>
                  metis_tac[SUBSET_THM]) >>
              simp[project_def] >>
              gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              fs[set_dvarsOf_dsubst_eq] >>
              fs[project_dvarsOf_empty_Fix] >>
              qmatch_goalsub_abbrev_tac ‘dsubst _ _ (Fix _ (project' proc adv1 c)) = dsubst _ _ (Fix _ (project' proc adv2 c))’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >> fs[] >>
                   TRY PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              AP_THM_TAC >>
              AP_THM_TAC >>
              AP_TERM_TAC >>
              AP_TERM_TAC >>
              match_mp_tac project_ALOOKUP_EQ_strong >>
              rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                 CaseEq "bool"] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]))
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub']
          >- (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              first_x_assum match_mp_tac >>
              gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
              fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
              qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >>
                   PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              conj_tac >-
               (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                ‘project proc adv1 c' = project proc adv2 c'’
                  by(unabbrev_all_tac >>
                     match_mp_tac project_ALOOKUP_EQ_strong >>
                     rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                        CaseEq "bool"] >>
                     gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                     res_tac >>
                     imp_res_tac SUBSET_THM >> fs[] >>
                     TRY PURE_FULL_CASE_TAC >> fs[] >>
                     rveq >> fs[] >>
                     metis_tac[SUBSET_THM]) >>
                fs[]) >>
              rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]) >>
          gs[CaseEq "bool"] >> rveq >> gs[]
          >- (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              first_x_assum match_mp_tac >>
              gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
              fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
              qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >>
                   PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              conj_tac >-
               (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                ‘project proc adv1 c' = project proc adv2 c'’
                  by(unabbrev_all_tac >>
                     match_mp_tac project_ALOOKUP_EQ_strong >>
                     rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                        CaseEq "bool"] >>
                     gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                     res_tac >>
                     imp_res_tac SUBSET_THM >> fs[] >>
                     TRY PURE_FULL_CASE_TAC >> fs[] >>
                     rveq >> fs[] >>
                     metis_tac[SUBSET_THM]) >>
                fs[]) >>
              rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]) >>
          reverse IF_CASES_TAC
          >- (fs[] >> first_x_assum(qspecl_then [‘dn''’,‘procs’] mp_tac) >> simp[] >>
              fs[set_dvarsOf_dsubst_eq]) >>
          gs[]
          >> (fs[PULL_FORALL,AND_IMP_INTRO,IMP_CONJ_THM] >>
              rfs[FORALL_AND_THM] >>
              first_x_assum match_mp_tac >>
              gs[project_dvarsOf_empty,project_dvarsOf_empty_Fix,project_def] >>
              fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
              qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c’ >>
              qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c’ >>
              ‘project proc adv1 c = project proc adv2 c’
                by(unabbrev_all_tac >>
                   match_mp_tac project_ALOOKUP_EQ_strong >>
                   rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                      CaseEq "bool"] >>
                   fs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                   res_tac >>
                   imp_res_tac SUBSET_THM >>
                   PURE_FULL_CASE_TAC >> fs[] >>
                   rveq >> fs[] >>
                   metis_tac[SUBSET_THM]) >>
              fs[] >>
              unabbrev_all_tac >>
              conj_tac >-
               (qmatch_asmsub_abbrev_tac ‘project_ok proc adv1 c'’ >>
                qmatch_goalsub_abbrev_tac ‘project_ok proc adv2 c'’ >>
                ‘project proc adv1 c' = project proc adv2 c'’
                  by(unabbrev_all_tac >>
                     match_mp_tac project_ALOOKUP_EQ_strong >>
                     rw[SUBSET_DEF,SET_EQ_SUBSET,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',
                        CaseEq "bool"] >>
                     gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
                     res_tac >>
                     imp_res_tac SUBSET_THM >> fs[] >>
                     TRY PURE_FULL_CASE_TAC >> fs[] >>
                     rveq >> fs[] >>
                     metis_tac[SUBSET_THM]) >>
                fs[]) >>
              rw[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub',SUBSET_DEF] >>
              gs[set_dvarsOf_dsubst_eq,dprocsOf_MEM_eq,set_procsOf_dsubst_eq] >>
              res_tac >>
              imp_res_tac SUBSET_THM >> fs[] >>
              TRY PURE_FULL_CASE_TAC >> fs[procsOf_def,MEM_nub'] >>
              rveq >> fs[] >>
              metis_tac[SUBSET_THM]))
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          IF_CASES_TAC >> gs[] >>
          PURE_FULL_CASE_TAC >> fs[] >>
          metis_tac[])
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          IF_CASES_TAC >> gs[] >>
          PURE_FULL_CASE_TAC >> fs[] >>
          metis_tac[])
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          TRY(drule_all_then strip_assume_tac SUBSET_THM >> fs[]) >>
          fs[CaseEq "bool"] >> rveq >> fs[] >>
          res_tac >>
          drule_all_then strip_assume_tac SUBSET_THM >> fs[])
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          TRY(drule_all_then strip_assume_tac SUBSET_THM >> fs[]) >>
          fs[CaseEq "bool"] >> rveq >> fs[] >>
          res_tac >>
          drule_all_then strip_assume_tac SUBSET_THM >> fs[])
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          IF_CASES_TAC >> fs[] >>
          FULL_CASE_TAC >> fs[] >>
          rveq >> fs[] >>
          res_tac >>
          metis_tac[SUBSET_THM])
      >- (gs[dprocsOf_MEM_eq,set_procsOf_dsubst_eq,procsOf_def,set_nub'] >>
          fs[set_dvarsOf_dsubst_eq] >>
          IF_CASES_TAC >> fs[] >>
          FULL_CASE_TAC >> fs[] >>
          rveq >> fs[] >>
          res_tac >>
          metis_tac[SUBSET_THM]))
  >- (rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def,project_def] >>
      fs[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def] >>
      TOP_CASE_TAC >> fs[] >> rw[endpointLangTheory.dsubst_def,chorLangTheory.dsubst_def])
QED

Theorem project'_dsubst_commute_nil:
  ∀dn c proc c'.
    dvarsOf(Fix dn c) = [] ∧
    project_ok proc [] (Fix dn c)
    ⇒
    project' proc [] (dsubst c dn (Fix dn c)) =
    dsubst (project' proc [(dn,dprocsOf [(dn,[])] c)] c) dn (project' proc [] (Fix dn c))
Proof
  rpt strip_tac >>
  drule_then drule project'_dsubst_commute >>
  disch_then(qspec_then ‘c’ mp_tac) >>
  impl_tac
  >- (rw[] >>
      fs[project_def] >>
      every_case_tac >> fs[] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC[project_nonmember_nil_lemma] >>
      fs[dvarsOf_def,dprocsOf_MEM_eq,FILTER_EQ_NIL,EVERY_MEM,MEM_nub',SUBSET_DEF]) >>
  rw[]
QED

val trans_dequeue_gen = Q.store_thm("trans_dequeue_gen",
  `∀d s s' v p1 p2 e q1 q2.
    s.queue = q1 ⧺ [(p1,d)] ⧺ q2
    ∧ p1 ≠ p2 ∧ EVERY (λ(p,_). p ≠ p1) q1
    ∧ s' = s with <|queue := q1 ⧺ q2; bindings := s.bindings |+ (v,d)|>
    ⇒ trans (NEndpoint p2 s (Receive p1 v e))
            LTau
            (NEndpoint p2 s' e)`,
  rw [] >> drule trans_dequeue >> rw []
);

val trans_enqueue_choice_gen = Q.store_thm("trans_enqueue_choice_gen",
  `∀s p1 p2 e s' b.
    p1 ≠ p2
    ∧ s' = s with queue := SNOC (p1,if b then [1w] else [0w]) s.queue
    ⇒ trans (NEndpoint p2 s e)
            (LExtChoice p1 b p2)
            (NEndpoint p2 s' e)`,
  rw []
  >- (drule trans_enqueue_choice_l >> rw [])
  >- (drule trans_enqueue_choice_r >> rw [])
);

val trans_ext_choice_l_gen = Q.store_thm("trans_ext_choice_l_gen",
  `∀s s' p1 p2 e1 e2 q1 q2.
    s' = s with queue := q1 ++ q2
    ∧ s.queue = q1 ++ [(p1,[1w])] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 s' e1)`,
  rw [trans_ext_choice_l]
);

val trans_ext_choice_r_gen = Q.store_thm("trans_ext_choice_r_gen",
  `∀s s' d p1 p2 e1 e2 q1 q2.
    s' = s with queue := q1 ++ q2
    ∧ s.queue = q1 ++ [(p1,d)] ++ q2
    ∧ d ≠ [1w]
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 s' e2)`,
  rw [trans_ext_choice_r]
);

val trans_let_gen = Q.store_thm("trans_let_gen",
  `∀s s' v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ∧ s' = (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
    ⇒ trans (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p s' e)`,
  rw [endpointSemTheory.trans_let]
);

val cut_sel_upto_def = Define`
  cut_sel_upto p (Sel p1 b p2 c) =
    (if p = p1 then
       cut_sel_upto p c
     else
       Sel p1 b p2 c)
∧ cut_sel_upto p c = c
`;

Theorem dvarsOf_cut_sel_upto:
  ∀p c. dvarsOf(cut_sel_upto p c) = dvarsOf c
Proof
  strip_tac >> Induct >> rw[dvarsOf_def,cut_sel_upto_def,nub'_dvarsOf] >> simp[]
QED

Theorem free_variables_cut_sel_upto:
  ∀p c. free_variables(cut_sel_upto p c) = free_variables c
Proof
  strip_tac >> Induct >> rw[free_variables_def,cut_sel_upto_def] >> simp[]
QED

(* TODO: move *)
Theorem dvarsOf_nil_trans:
  ∀s c α l s' c'.
  trans (s,c) (α,l) (s',c') ∧ dvarsOf c = [] ⇒
  dvarsOf c' = []
Proof
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_pairind >>
  rw[dvarsOf_def,nub'_nil] >>
  fs[FILTER_EQ_NIL,EVERY_MEM,MEM_nub'] >>
  ‘∀x. MEM x (dvarsOf (dsubst c dn (Fix dn c))) ⇒ F’
    by(dep_rewrite.DEP_ONCE_REWRITE_TAC[set_dvarsOf_dsubst_eq] >>
       fs[dvarsOf_def,nub'_nil,FILTER_EQ_NIL,EVERY_MEM,MEM_nub'] >>
       metis_tac[]) >>
  spose_not_then strip_assume_tac >>
  Cases_on ‘dvarsOf (dsubst c dn (Fix dn c))’ >> fs[FORALL_AND_THM]
QED

Theorem dvarsOf_nil_trans_s:
  ∀sc sc'.
    trans_s sc sc'  ∧ dvarsOf(SND sc) = [] ⇒
    dvarsOf(SND sc') = []
Proof
  simp[trans_s_def,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >>
  Cases_on ‘sc’ >> Cases_on ‘sc'’ >> rename1 ‘trans _ α _’ >>
  Cases_on ‘α’ >> fs[] >>
  imp_res_tac dvarsOf_nil_trans >>
  fs[]
QED

val compile_network_eq_all_project = Q.store_thm("compile_network_eq_all_project",
  `∀c c' s l. compile_network_ok s c l
    ∧ (∀p. MEM p l ⇒ project' p [] c = project' p [] c')
    ⇒ compile_network s c l = compile_network s c' l`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
);

val compile_network_ok_project_ok = Q.store_thm("compile_network_ok_project_ok",
  `∀s c l p.
    compile_network_ok s c l
    ∧ MEM p l
    ⇒ project_ok p [] c`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
);

val compile_network_ok_dest_sel = Q.store_thm("compile_network_ok_dest_sel",
  `∀s c l p b q.
    compile_network_ok s (Sel p b q c) l
    ⇒ compile_network_ok s c l`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
);

Theorem compile_network_ok_dest_sel':
  ∀s c l p b q.
    compile_network_ok s (Sel p b q c) l
    ⇒ (p <> q \/ (~MEM p l /\ ~MEM q l))
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

Theorem compile_network_ok_selI:
  ∀s c l p b q.
    compile_network_ok s c l /\ (p <> q \/ (~MEM p l /\ ~MEM q l))
    ⇒ compile_network_ok s (Sel p b q c) l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac[]
QED

Theorem compile_network_ok_dest_com:
  ∀s p1 v1 p2 v2 c l.
    compile_network_ok s (Com p1 v1 p2 v2 c) l
    ⇒ compile_network_ok (s |+ ((v2,p2),d)) c l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

Theorem compile_network_ok_dest_com_asynch:
  ∀s p1 v1 p2 v2 c l.
    compile_network_ok s (Com p1 v1 p2 v2 c) l
    ⇒ compile_network_ok s c l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

val project_if_l_eq = Q.store_thm("project_if_l_eq",
  `∀v p q dvars c1 c2.
    project_ok q dvars (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c1 ≠ Sel p b t c')
    ⇒ project' q dvars (IfThen v p c1 c2) = project' q dvars c1`,
  Cases_on `c1`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []);

val project_if_r_eq = Q.store_thm("project_if_r_eq",
  `∀v p dvars q c1 c2.
    project_ok q dvars (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c2 ≠ Sel p b t c')
    ⇒ project' q dvars (IfThen v p c1 c2) = project' q dvars c2`,
  Cases_on `c2`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []
);

val compile_network_if_l_eq = Q.store_thm("compile_network_if_l_eq",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b q c'. c1 ≠ Sel p b q c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c1 l`,
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_l_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
);

val compile_network_if_l = Q.store_thm("compile_network_if_l",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c1 l`,
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]);

val compile_network_if_r = Q.store_thm("compile_network_if_r",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c2 l`,
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]);

val compile_network_if_r_eq = Q.store_thm("compile_network_if_r_eq",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b p2 c'. c2 ≠ Sel p b p2 c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c2 l`,
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_r_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
);

val FST_endpoints_compile_network = Q.store_thm("FST_endpoints_compile_network",
  `∀s c l. MAP FST (endpoints (compile_network s c l)) = l`,
  Induct_on `l`
  \\ rw [endpoints_def,compile_network_gen_def]
);

val preSel_def = Define`
  preSel p (Sel p1 b p2 c) =
    (if p1 = p
     then (b,p2)::preSel p c
     else [])
∧ preSel _ _ = []
`;

val projPre_def = Define`
  projPre p ((b,q)::l) ep = IntChoice b q (projPre p l ep)
∧ projPre p [] ep = ep
`

val prefix_project_eq = Q.store_thm("prefix_project_eq",
  `∀p dvars c. project_ok p dvars c
    ⇒ project' p dvars c = projPre p (preSel p c) (project' p dvars (cut_sel_upto p c))`,
  Induct_on `c`
  \\ rw []
  \\ TRY (Cases_on `p = s0`)
  \\ rw [project_def,preSel_def,cut_sel_upto_def,projPre_def]
  \\ fs [project_def]
);

val list_trans_projpre = Q.store_thm("list_trans_projpre",
  `!p sq c' e.
     ~MEM p (MAP SND (preSel p c'))
     ==>
     list_trans (NEndpoint p sq (projPre p (preSel p c') e))
                      (MAP (λ(b,q). LIntChoice p b q) (preSel p c'))
                      (NEndpoint p sq e)`,
  Induct_on `c'`
  >> TRY(rw[preSel_def,projPre_def,list_trans_def] \\ NO_TAC)
  >> rpt strip_tac
  >> simp[preSel_def]
  >> reverse IF_CASES_TAC
  >- rw[preSel_def,projPre_def,list_trans_def]
  >> rveq >> rename1 `NEndpoint p`
  >> simp[list_trans_def,PULL_EXISTS,projPre_def]
  >> qmatch_goalsub_abbrev_tac `IntChoice _ _ a1`
  >> qexists_tac `NEndpoint p sq a1`
  >> qunabbrev_tac `a1`
  >> qpat_x_assum `¬ _` mp_tac
  >> simp[preSel_def] >> strip_tac
  >> simp[trans_int_choice]);

(* TODO: move to endpointProps? *)
val list_trans_com_choice_l = Q.store_thm("list_trans_com_choice_l",
 `!icl ecl n1 n2 n1' n2'.
  EVERY2 (\ic ec. ?p b q. ic = LIntChoice p b q /\ ec = LExtChoice p b q) icl ecl
  /\ list_trans n1 icl n1' /\ list_trans n2 ecl n2'
  ==>
  reduction^* (NPar n1 n2) (NPar n1' n2')`,
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac LIST_REL_ind >> rpt strip_tac
  >> fs[list_trans_def]
  >> rveq
  >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
  >> imp_res_tac sender_receiver_distinct_choice
  >> imp_res_tac trans_com_choice_l
  >> simp[reduction_def]
  >> asm_exists_tac >> simp[]);

val list_trans_com_choice_l' = Q.store_thm("list_trans_com_choice_l'",
 `!icl ecl n1 n2 n1' n2' n2''.
  EVERY2 (\ic ec. ?p b q. ic = LIntChoice p b q /\ ec = LExtChoice p b q) icl ecl
  /\ list_trans n1 icl n1' /\ list_trans n2 ecl n2'
  /\ reduction^* n2' n2''
  ==>
  reduction^* (NPar n1 n2) (NPar n1' n2'')`,
  metis_tac[reduction_par_r,RTC_RTC,list_trans_com_choice_l]);

val trans_fold_par = Q.store_thm("trans_fold_par",
  `!n1 e1 e2 n2 alpha. trans e1 alpha e2
   ==> trans (FOLDR NPar NNil (n1 ++ e1::n2)) alpha (FOLDR NPar NNil (n1 ++ e2::n2))`,
  Induct >> rw[] >> metis_tac[trans_par_l,trans_par_r]);

val trans_fold_par' = Q.store_thm("trans_fold_par'",
  `!n1 n1' e1 e2 n2 n2' alpha. trans e1 alpha e2 /\ n1 = n1' /\ n2 = n2'
   ==> trans (FOLDR NPar NNil (n1 ++ e1::n2)) alpha (FOLDR NPar NNil (n1' ++ e2::n2'))`,
  metis_tac[trans_fold_par]);

val preSel_to_queue_def = Define
  `preSel_to_queue proc1 proc2 l =
    MAP (λ(b,p). (proc2,if b then [1w] else [0w])) (FILTER ($= proc1 o SND) l)`

val compile_network_ok_if_eq = Q.store_thm("compile_network_ok_if_eq",
  `!s v p c' c2 l.
   compile_network_ok s (IfThen v p c' c2) l /\
   ~MEM p l ==>
   compile_network s (IfThen v p c' c2) l =
   FOLDR NPar NNil
   (MAP (\proc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (project' proc [] (IfThen v p c' c2))) l)`,
   Induct_on `l`
   >- rw[compile_network_gen_def]
   >> rpt strip_tac
   >> fs[compile_network_gen_def]
   >> fs[project_def]);

val cut_ext_choice_upto_presel_def = Define `
   (cut_ext_choice_upto_presel p1 p2 presel Nil = Nil)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Send p v e) = Send p v e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Receive p v e) = Receive p v e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (IfThen b e1 e2) = IfThen b e1 e2)
/\ (cut_ext_choice_upto_presel p1 p2 presel (IntChoice p b' e) = IntChoice p b' e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Let s f l c) = Let s f l c)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Fix s c) = Fix s c)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Call s) = Call s)
/\ (cut_ext_choice_upto_presel p1 p2 presel (ExtChoice p e1 e2) =
    (if p = p1 then
      (case SPLITP ($= p2 o SND) presel of
       (_,[]) => ExtChoice p e1 e2
     | (_,(T,_)::presel) => cut_ext_choice_upto_presel p1 p2 presel e1
     | (_,(F,_)::presel) => cut_ext_choice_upto_presel p1 p2 presel e2)
     else ExtChoice p e1 e2))`

val cut_ext_choice_upto_presel_nil = Q.store_thm("cut_ext_choice_upto_presel_nil",
  `cut_ext_choice_upto_presel p1 p2 [] c = c`,
  Induct_on `c` >> rw[cut_ext_choice_upto_presel_def,SPLITP]
                                                );

val cut_ext_choice_upto_presel_cons = Q.store_thm("cut_ext_choice_upto_presel_cons",
  `p2 <> p3
   ==>
   cut_ext_choice_upto_presel p1 p2 ((b,p3)::l) c =
   cut_ext_choice_upto_presel p1 p2 l c`,
  Induct_on `c` >> rw[cut_ext_choice_upto_presel_def,SPLITP]
  >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq));

val project_cut_sel_eq = Q.store_thm("project_cut_sel_eq",
  `!h p dvars c1.
   p ≠ h /\ project_ok h dvars c1 ==>
   project' h dvars (cut_sel_upto p c1) =
   cut_ext_choice_upto_presel p h (preSel p c1) (project' h dvars c1)`,
  Induct_on `c1`
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >> rw[cut_sel_upto_def]
  >> simp[preSel_def] >> rw[cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_nil]
  >> rw[project_def,cut_ext_choice_upto_presel_def,SPLITP]
  >> simp[cut_ext_choice_upto_presel_cons]
  >> first_x_assum match_mp_tac >> fs[project_def] >> every_case_tac >> fs[]);

val FILTER_nub = Q.store_thm("FILTER_nub",
  `!P l. FILTER P (nub' l) = nub' (FILTER P l)`,
  Induct_on `l` >> rpt strip_tac
  >> fs[nub'_def] >> rw[nub'_def]
  >> first_assum(qspec_then `P`  (assume_tac o GSYM))
  >> first_x_assum(qspec_then `(λy. h ≠ y)` (assume_tac o GSYM))
  >> simp[FILTER_FILTER] >> simp[Once CONJ_SYM]
  >> rw[FILTER_EQ,EQ_IMP_THM] >> CCONTR_TAC >> fs[]);

val compile_network_cut_sel_upto = Q.store_thm("compile_network_cut_sel_upto",
  `!s v p c1 l.
  compile_network_ok s c1 l /\
  ~MEM p l ==>
  compile_network s (cut_sel_upto p c1) l =
  FOLDR NPar NNil
   (MAP (\proc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (cut_ext_choice_upto_presel p proc (preSel p c1) (project' proc [] c1))) l)`,
  Induct_on `l`
  >- (rw[compile_network_gen_def])
  >> rpt strip_tac
  >> fs[compile_network_gen_def,project_def,
        split_sel_def,cut_sel_upto_def,cut_ext_choice_upto_presel_def]
  >> fs[project_cut_sel_eq]);

val MEM_presel_MEM_procsOf = Q.store_thm("MEM_presel_MEM_procsOf",
  `!c dvars p. project_ok p dvars c  /\ MEM p (MAP SND (preSel p c))
   ==> F`,
  Induct
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >> rpt strip_tac
  >> fs[project_def,preSel_def]
  >> rpt(PURE_FULL_CASE_TAC >> fs[]) >> metis_tac[]);

val network_consume_LExtChoice = Q.store_thm("network_consume_LExtChoice",
  `∀psl qf s c l p dvars.
       ¬MEM p l ∧ ¬MEM p (MAP SND psl) ∧ ALL_DISTINCT l ∧
       (∀x. MEM x (MAP SND psl) ⇒ MEM x l) ⇒
       list_trans
         (FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s; queue := qf proc|>
                      (project' proc dvars c)) l))
         (MAP (λ(b,q). LExtChoice p b q) psl)
         (FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s;
                      queue := qf proc ⧺ preSel_to_queue proc p psl|>
                      (project' proc dvars c)) l))`,
  Induct
  >- (rw[list_trans_def,preSel_to_queue_def])
  \\ rw[list_trans_def]
  \\ rw[preSel_to_queue_def]
  \\ `MEM (SND h) l` by simp[]
  \\ Cases_on `h` >> simp[]
  \\ rename1 `LExtChoice p1 b p2`
  \\ qexists_tac
       `FOLDR NPar NNil
              (MAP
                (λproc.
                  NEndpoint proc
                    <|bindings := projectS proc s; queue :=
                      qf proc ++ if proc = p2 then [(p1, if b then [1w] else [0w])] else [] |>
                    (project' proc dvars c)) l)`
  \\ conj_tac
  >- (pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT])
      \\ simp[] \\ match_mp_tac trans_fold_par'
      \\ conj_tac
      >- (match_mp_tac trans_enqueue_choice_gen >> fs[])
      \\ fs[]
      \\ rw[MAP_EQ_f]
      \\ rw[] \\ fs[ALL_DISTINCT_APPEND] \\ metis_tac[])
  \\ fs[]
  \\ first_x_assum(qspec_then `\proc. qf proc ⧺
                   if proc = p2 then [(p1,if b then [1w] else [0w])] else []` mp_tac)
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspecl_then [‘dvars’,`p1`,`l`] mp_tac)
  \\ rpt(disch_then drule)
  \\ Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_FORALL]
  \\ impl_tac >- rw[]
  \\ disch_then(qspecl_then [`c`,`s`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac `list_trans (FOLDR _ _ a1) _ (FOLDR _ _ a2)
                                 ==> list_trans (FOLDR _ _ a3) _ (FOLDR _ _ a4)`
  \\ `a1 = a3 /\ a2 = a4` suffices_by simp[]
  \\ unabbrev_all_tac
  \\ rw[MAP_EQ_f] \\ rw[preSel_to_queue_def]
);

val epn_conf_def = Define`
  epn_conf p q = ∃p' q'. reduction^* p p' ∧ reduction^* q q' ∧ qcong p' q'
`
val _ = Parse.add_infix("≅<",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅<",``epn_conf``);

Theorem conf_refl:
  ∀epn. epn ≅< epn
Proof
  rw [epn_conf_def]
  \\ map_every qexists_tac [`epn`,`epn`]
  \\ rw [reduction_def,qcong_refl]
QED

Theorem conf_sym:
  ∀epn epn'. epn ≅< epn' ⇒ epn' ≅< epn
Proof
  metis_tac [epn_conf_def,qcong_sym]
QED

Theorem conf_distinct:
  ∀epn epn'.
   epn ≅< epn' ∧
   ALL_DISTINCT (MAP FST (endpoints epn))
   ⇒ ALL_DISTINCT (MAP FST (endpoints epn'))
Proof
  metis_tac[ qcong_endpoints
           , endpoint_names_reduction
           , epn_conf_def]
QED

Theorem projectS_fupdate_fresh:
  p <> p' ==>
  projectS p (s |+ ((v,p'),d)) = projectS p s
Proof
  rw[projectS_def]
QED

Theorem trans_not_eq:
  ∀s c τ l s' c'. trans (s,c) (τ,l) (s',c') ∧ τ ≠ LFix ⇒ c ≠ c'
Proof
  ONCE_REWRITE_TAC [GSYM AND_IMP_INTRO]
  \\ ho_match_mp_tac trans_pairind \\ rw []
  \\ disch_then (mp_tac o AP_TERM “chor_size”) \\ EVAL_TAC \\ fs []
QED

Definition catchup_of_def:
  (catchup_of (LTau p ps) c = cut_sel_upto p c) ∧
  catchup_of _ c = c
End

Theorem compile_network_ok_subset:
  ∀s c ps qs.
  compile_network_ok s c qs ∧ set ps ⊆ set qs ⇒
  compile_network_ok s c ps
Proof
  Induct_on ‘ps’ >>
  rw[compile_network_gen_def] >- imp_res_tac compile_network_ok_project_ok >>
  res_tac
QED

Theorem trans_ln_catchup_of:
  ∀p τ.
  no_self_comunication (SND p) ⇒
  trans_ln p (FST p,catchup_of τ (SND p))
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def,trans_ln_refl] >>
  PairCases >> Induct_on ‘p1’ >>
  fs[cut_sel_upto_def,trans_ln_refl,no_self_comunication_def] >>
  rw[trans_ln_refl] >>
  match_mp_tac trans_ln_step >>
  rw[chor_tl_def] >>
  metis_tac[trans_sel]
QED

Theorem trans_ln_catchup_of_pair =
  Q.SPEC ‘(s,c)’ trans_ln_catchup_of  |> SIMP_RULE std_ss []  |> GEN_ALL

Theorem trans_ln_cut_sel_upto:
  ∀s c p.
  no_self_comunication c ⇒
  trans_ln (s,c) (s,cut_sel_upto p c)
Proof
  rw[] >>
  qspecl_then [‘(s,c)’,‘LTau p ARB’] assume_tac trans_ln_catchup_of >>
  fs[catchup_of_def]
QED

Theorem compile_network_ok_no_self_comunication:
  ∀s c.
  compile_network_ok s c (procsOf c) ⇒
  no_self_comunication c
Proof
  rw[] >>
  dxrule compile_network_ok_project_ok >>
  simp[Once MONO_NOT_EQ] >>
  ‘∃dvars. dvars:((string # string list) list) = []’ by simp[] >>
  pop_assum(SUBST_ALL_TAC o GSYM) >>
  qid_spec_tac ‘dvars’ >>
  Induct_on ‘c’ >>
  rw[project_def,no_self_comunication_def,procsOf_def,nub'_def,procsOf_all_distinct] >>
  res_tac >> fs[] >>
  rw[MEM_FILTER,MEM_nub'] >>
  rw[RIGHT_AND_OVER_OR,EXISTS_OR_THM] >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s = p’ >> simp[] >>
     disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]) >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s = p’ >> simp[] >>
     disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]) >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s2 = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (rpt(first_x_assum(qspec_then ‘dvars’ strip_assume_tac)) >>
     Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (first_x_assum (qspec_then ‘(s,dprocsOf ((s,[])::dvars) c)::dvars’ strip_assume_tac) >>
     asm_exists_tac \\ rw [] \\
     fs[dprocsOf_MEM_eq])
QED

Triviality dsubst_subset_procsOf:
  ∀c dn c'.
    set (procsOf (dsubst c dn c')) ⊆ set (procsOf c) ∪ set (procsOf c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [procsOf_def,chorLangTheory.dsubst_def,set_nub']
  \\ irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
  \\ fs [SUBSET_DEF]
QED

Triviality procsOf_subset_dsubst:
  ∀c dn c'.
    set (procsOf c) ⊆ set (procsOf (dsubst c dn c'))
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [procsOf_def,chorLangTheory.dsubst_def,set_nub']
  \\ fs [SUBSET_DEF]
QED

Theorem dsubst_procsOf_set_eq:
  ∀c dn. set (procsOf c) = set (procsOf (dsubst c dn c))
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [procsOf_subset_dsubst,
                dsubst_subset_procsOf,
                UNION_IDEMPOT]
QED

Theorem dsubst_procsOf_set_eq_Fix:
  ∀c x y. set (procsOf c) = set (procsOf (dsubst c x (Fix y c)))
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [procsOf_subset_dsubst,
                dsubst_subset_procsOf,
                procsOf_def,
                set_nub',
                UNION_IDEMPOT]
QED

Theorem procsOf_dsubst_MEM_eq:
  ∀c p x y. MEM p (procsOf c) ⇔ MEM p (procsOf (dsubst c x (Fix y c)))
Proof
  rw []
  \\ qspecl_then [‘c’,‘x’,‘y’] (assume_tac) dsubst_procsOf_set_eq_Fix
  \\ pop_assum (assume_tac o Q.AP_TERM ‘(λx. p IN x)’) \\ fs []
QED

Theorem procsOf_dsubst_MEM =
  SPEC_ALL procsOf_dsubst_MEM_eq
  |> EQ_IMP_RULE
  |> fst
  |> GEN_ALL

Theorem dsubst_procsOf_MEM =
  SPEC_ALL procsOf_dsubst_MEM_eq
  |> EQ_IMP_RULE
  |> snd
  |> GEN_ALL

Theorem procsOf_dsubst_not_MEM_eq =
  “¬MEM p (procsOf (c : chorLang$chor))”
  |> ONCE_REWRITE_CONV [procsOf_dsubst_MEM_eq]
  |> GEN_ALL

Theorem procsOf_dsubst_not_MEM =
  SPEC_ALL procsOf_dsubst_not_MEM_eq
  |> EQ_IMP_RULE
  |> fst
  |> GEN_ALL

Theorem dsubst_procsOf_not_MEM =
  SPEC_ALL procsOf_dsubst_not_MEM_eq
  |> EQ_IMP_RULE
  |> snd
  |> GEN_ALL

Theorem project_nonmember_nil:
  ∀p c.
  ~MEM p (procsOf c) ⇒ project' p [] c = Nil
Proof
  rpt strip_tac >>
  qspecl_then [‘p’,‘[]’,‘c’] assume_tac project_nonmember_nil_lemma' >>
  gs[dprocsOf_MEM_eq]
QED

Theorem project_pair_nonmember_nil:
  ∀p c.
  ~MEM p (procsOf c) ⇒ ∃ok. (project p [] c = (ok,Nil))
Proof
  rw[quantHeuristicsTheory.PAIR_EQ_EXPAND] >>
  imp_res_tac project_nonmember_nil
QED

Theorem split_sel_dsubst:
  ∀c p q c' x y.
    IS_SOME (split_sel p q (dsubst c x (Fix y c'))) = IS_SOME (split_sel p q c)
Proof
  Induct \\ rw [split_sel_def,chorLangTheory.dsubst_def]
QED

Theorem procsOf_dsubst_any_not_MEM:
  ∀p c c' dn.
    ¬MEM p (procsOf c) ∧ ¬MEM p (procsOf c') ⇒ ¬MEM p (procsOf (dsubst c dn c'))
Proof
  rw []
 \\ qspecl_then [‘c’,‘dn’,‘c'’] assume_tac dsubst_subset_procsOf
 \\ CCONTR_TAC \\ fs [SUBSET_DEF]
 \\ first_x_assum drule \\  rw[]
QED

Theorem not_trans_LFix_if_l:
  ∀c s s' v p c'.
    ¬ trans (s,IfThen v p c c') (LFix,[]) (s',c)
Proof
  Induct \\ rw []
  \\ ONCE_REWRITE_TAC [trans_cases] \\ rw []
  \\ pop_assum (assume_tac o Q.AP_TERM ‘chorLang$chor_size’)
  \\ fs [chorLangTheory.chor_size_def]
QED

Theorem not_trans_LFix_if_r:
  ∀c s s' v p c'.
    ¬ trans (s,IfThen v p c' c) (LFix,[]) (s',c)
Proof
  Induct \\ rw []
  \\ ONCE_REWRITE_TAC [trans_cases] \\ rw []
  >- (CCONTR_TAC \\ fs []
     \\ drule trans_LFix_async \\ strip_tac
      \\ rveq \\ gs [])
  \\ pop_assum (assume_tac o Q.AP_TERM ‘chorLang$chor_size’)
  \\ fs [chorLangTheory.chor_size_def]
QED

Theorem reduction_if_false:
  ∀v p s c1 c2 w.
  FLOOKUP s (v,p) = SOME w ∧
  w ≠ [1w] ∧
  compile_network_ok s (IfThen v p c1 c2) (procsOf (IfThen v p c1 c2)) ∧
  no_self_comunication (IfThen v p c1 c2)
  ⇒ reduction꙳ (compile_network s (IfThen v p c1 c2)  (procsOf (IfThen v p c1 c2)))
               (compile_network s (cut_sel_upto p c2) (procsOf (IfThen v p c1 c2)))
Proof
  rw [compile_network_gen_def,project_def,procsOf_def,nub'_def]
  \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c1 ⧺ procsOf c2))`
                            , `sq = <|bindings := projectS p s; queue := []|>`
                            ]
  \\ ho_match_mp_tac RTC_TRANS
  \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p [] c2)))
                        (compile_network s (IfThen v p c1 c2) l)`
  \\ rw [reduction_def]
  >- (ho_match_mp_tac trans_par_l
     \\ ho_match_mp_tac endpointSemTheory.trans_if_false
     \\ rw [Abbr `sq`,lookup_projectS]
     \\ METIS_TAC [lookup_projectS])
  \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
  \\ rw [prefix_project_eq]
  \\ match_mp_tac list_trans_com_choice_l'
  \\ Q.ISPECL_THEN [`p`,`sq`,`c2`,`project' p [] (cut_sel_upto p c2)`]
                 mp_tac list_trans_projpre
  \\ impl_tac
  >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf)
  \\ strip_tac
  \\ MAP_EVERY qexists_tac
               [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c2))`,
                `(MAP (λ(b,q). LExtChoice p b q) (preSel p c2))`]
  \\ simp[GSYM PULL_EXISTS]
  \\ conj_tac
  >- (simp[EVERY2_MAP,ELIM_UNCURRY]
      \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
  \\ simp[compile_network_ok_if_eq]
  \\ qexists_tac
       `FOLDR NPar NNil
         (MAP
            (λproc.
                 NEndpoint proc
                   <|bindings := projectS proc s;
                     queue := preSel_to_queue proc p (preSel p c2)|>
                   (project' proc [] (IfThen v p c1 c2))) l)`
  \\ imp_res_tac compile_network_if_r
  \\ simp[compile_network_cut_sel_upto]
  \\ `ALL_DISTINCT l`
       by(qunabbrev_tac `l`
          \\ match_mp_tac FILTER_ALL_DISTINCT
          \\ MATCH_ACCEPT_TAC all_distinct_nub')
  \\ `~MEM p (MAP SND (preSel p c2))`
       by(qhdtm_x_assum `list_trans` mp_tac
          \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
          \\ rpt(pop_assum kall_tac)
          \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c2`]
          \\ Induct \\ rw[preSel_def,list_trans_def]
          \\ imp_res_tac sender_receiver_distinct_choice
          \\ metis_tac[])
  \\ `!x. MEM x (MAP SND(preSel p c2)) ==> MEM x l`
    by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
       \\ unabbrev_all_tac \\ rpt(pop_assum kall_tac)
          \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c2`
          \\ rw[preSel_def]
          \\ rw[procsOf_def,nub'_def]
          \\ rw[FILTER_FILTER,FILTER_APPEND_DISTRIB]
          \\ fs[set_nub',MEM_FILTER,MEM_MAP,PULL_EXISTS]
          \\ rveq \\ fs[]
          \\ fs[]
          \\ metis_tac[])
  \\ conj_tac
  >- (`?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
      \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                    = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
          by(rw[])
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
      \\ simp[]
      \\ pop_assum mp_tac
      \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
      \\ rpt(qpat_x_assum `¬_` mp_tac) \\ rpt(pop_assum kall_tac)
      \\ rename1 `MAP SND psl`
      \\ rw [network_consume_LExtChoice])
  \\ `?pn. pn = LENGTH(preSel p c2)` by simp[]
  \\ `!proc. MEM proc l ==> project_ok proc [] (if K T proc then IfThen v p c1 c2 else c2)`
     by(rw[] >> imp_res_tac compile_network_ok_project_ok)
  \\ ntac 5 (pop_assum mp_tac)
  \\ qpat_x_assum `compile_network_ok _ (IfThen _ _ _ _) _` kall_tac
  \\ qhdtm_x_assum `list_trans` kall_tac
  \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
  \\ rpt(pop_assum mp_tac)
  \\ `!proc. project' proc [] (IfThen v p c1 c2) = project' proc [] (if K T proc then IfThen v p c1 c2 else c2)`
     by(rw[])
  \\ qabbrev_tac `iffy = (K T):proc -> bool`
  \\ pop_assum kall_tac
  \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`w`,`s`,`v`,`p`,`c1`,`l`,`c2`,`iffy`,`pn`]
  \\ Induct
  >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def]
      >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
      >> `a1 = a2` suffices_by simp[]
      >> unabbrev_all_tac
      >> rw[MAP_EQ_f] >> rw[]
      >> match_mp_tac project_if_r_eq
      >> conj_tac
      >- (first_x_assum drule >> fs[])
      >> conj_tac
      >- (CCONTR_TAC >> fs[])
      >> CCONTR_TAC
      >> fs[] >> rveq >> fs[preSel_def])
  \\ rpt strip_tac
  \\ `?b q c2'. c2 = Sel p b q c2'`
     by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c2` >> rw[preSel_def])
  \\ rveq
  \\ `MEM q l` by(fs[preSel_def])
  \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  \\ `p <> q` by(CCONTR_TAC >> fs[])
  \\ `project_ok q [] c2'`
     by(imp_res_tac compile_network_ok_project_ok
        \\ rfs[project_def,split_sel_def]
        \\ Cases_on `b` \\ fs[])
  \\ first_assum drule
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
  \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                           queue := preSel_to_queue q p (preSel p c2')|> (project' q [] c2'))`
  \\ `trans (af q) (LTau) (ag q)`
     by(unabbrev_all_tac >> Cases_on `iffy q`
        >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
              split_sel_def,compile_network_gen_def,preSel_to_queue_def]
        >> rfs[]
        >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
        >> simp[cut_ext_choice_upto_presel_def,SPLITP]
        >> TRY(match_mp_tac trans_ext_choice_l_gen
               >> fs[] >> qexists_tac `[]` >> fs[])
        >> TRY(match_mp_tac trans_ext_choice_r_gen
               >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
  \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
            LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
       by(simp[trans_fold_par])
  \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
  \\ qabbrev_tac `ah = (λproc.
              NEndpoint proc
                <|bindings := projectS proc s;
                queue := preSel_to_queue proc p (preSel p c2')|>
                (project' proc [] (if iffy' proc then IfThen v p c1 c2' else c2')))`
  \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
  \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
  \\ conj_tac
  >- (simp[reduction_def]
      \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
          suffices_by metis_tac[]
      \\ unabbrev_all_tac
      \\ rw[MAP_EQ_f]
      \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
      \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
      \\ `proc <> p` by(CCONTR_TAC >> fs[])
      \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
      \\ rw[] \\ fs[project_def,split_sel_def])
  \\ first_x_assum (qspecl_then [`iffy'`,`c2'`,`l`,`c1`,`p`,`v`,`s`,`w`] mp_tac)
  \\ `project_ok p [] c2'` by(fs[project_def])
  \\ `compile_network_ok s c2' l` by(imp_res_tac compile_network_ok_dest_sel)
  \\ rpt(disch_then drule)
  \\ impl_tac
  >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
      >> fs[preSel_def] >> unabbrev_all_tac >> fs[no_self_comunication_def]
      >> rw[] >> rpt(first_x_assum drule) >> simp[]
      >> `proc <> p` by(CCONTR_TAC >> fs[])
      >> fs[project_def,split_sel_def]
      >> rw[])
  \\ qmatch_goalsub_abbrev_tac
       `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
  \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
  \\ unabbrev_all_tac
  \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
  \\ `proc <> p` by(CCONTR_TAC >> fs[])
  >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
      \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
  >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
      >> rw[cut_ext_choice_upto_presel_def,SPLITP])
  >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
      \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
QED

Theorem reduction_if_true:
  ∀v p s c1 c2.
  FLOOKUP s (v,p) = SOME [1w] ∧
  compile_network_ok s (IfThen v p c1 c2) (procsOf (IfThen v p c1 c2)) ∧
  no_self_comunication (IfThen v p c1 c2)
  ⇒ reduction꙳ (compile_network s (IfThen v p c1 c2)  (procsOf (IfThen v p c1 c2)))
               (compile_network s (cut_sel_upto p c1) (procsOf (IfThen v p c1 c2)))
Proof
  rw [compile_network_gen_def,project_def,procsOf_def,nub'_def]
  \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c1 ⧺ procsOf c2))`
                            , `sq = <|bindings := projectS p s; queue := []|>`
                            ]
  \\ ho_match_mp_tac RTC_TRANS
  \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p [] c1)))
                        (compile_network s (IfThen v p c1 c2) l)`
  \\ rw [reduction_def]
  >- (ho_match_mp_tac trans_par_l
      \\ ho_match_mp_tac endpointSemTheory.trans_if_true
      \\ rw [Abbr `sq`,lookup_projectS])
  \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
  \\ rw [prefix_project_eq]
  \\ match_mp_tac list_trans_com_choice_l'
  \\ Q.ISPECL_THEN [`p`,`sq`,`c1`,`project' p [] (cut_sel_upto p c1)`]
                   mp_tac list_trans_projpre
  \\ impl_tac
  >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf)
  \\ strip_tac
  \\ MAP_EVERY qexists_tac
               [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c1))`,
                `(MAP (λ(b,q). LExtChoice p b q) (preSel p c1))`]
  \\ simp[GSYM PULL_EXISTS]
  \\ conj_tac
  >- (simp[EVERY2_MAP,ELIM_UNCURRY]
      \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
  \\ simp[compile_network_ok_if_eq]
  \\ qexists_tac
       `FOLDR NPar NNil
         (MAP
            (λproc.
                 NEndpoint proc
                   <|bindings := projectS proc s;
                     queue := preSel_to_queue proc p (preSel p c1)|>
                   (project' proc [] (IfThen v p c1 c2))) l)`
  \\ imp_res_tac compile_network_if_l
  \\ simp[compile_network_cut_sel_upto]
  \\ `ALL_DISTINCT l`
       by(qunabbrev_tac `l`
          \\ match_mp_tac FILTER_ALL_DISTINCT
          \\ MATCH_ACCEPT_TAC all_distinct_nub')
  \\ `~MEM p (MAP SND (preSel p c1))`
       by(qhdtm_x_assum `list_trans` mp_tac
          \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
          \\ rpt(pop_assum kall_tac)
          \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c1`]
          \\ Induct \\ rw[preSel_def,list_trans_def]
          \\ imp_res_tac sender_receiver_distinct_choice
          \\ metis_tac[])
  \\ `!x. MEM x (MAP SND(preSel p c1)) ==> MEM x l`
       by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
          \\ unabbrev_all_tac \\ rpt(pop_assum kall_tac)
          \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c1`
          \\ rw[preSel_def]
          \\ rw[procsOf_def,nub'_def]
          \\ rw[FILTER_FILTER,FILTER_APPEND_DISTRIB]
          \\ fs[set_nub',MEM_FILTER,MEM_MAP,PULL_EXISTS]
          \\ rveq \\ fs[]
          \\ fs[]
          \\ metis_tac[])
  \\ conj_tac
  >- (`?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
      \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                   = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
         by(rw[])
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
      \\ simp[]
      \\ pop_assum mp_tac
      \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
      \\ rpt(qpat_x_assum `¬_` mp_tac) \\ rpt(pop_assum kall_tac)
      \\ rename1 `MAP SND psl`
      \\ rw [network_consume_LExtChoice])
  \\ `?pn. pn = LENGTH(preSel p c1)` by simp[]
  \\ `!proc. MEM proc l ==> project_ok proc [] (if K T proc then IfThen v p c1 c2 else c1)`
     by(rw[] >> imp_res_tac compile_network_ok_project_ok)
  \\ ntac 5 (pop_assum mp_tac)
  \\ qpat_x_assum `compile_network_ok _ (IfThen _ _ _ _) _` kall_tac
  \\ qhdtm_x_assum `list_trans` kall_tac
  \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
  \\ rpt(pop_assum mp_tac)
  \\ `!proc. project' proc [] (IfThen v p c1 c2) = project' proc [] (if K T proc then IfThen v p c1 c2 else c1)`
     by(rw[])
  \\ qabbrev_tac `iffy = (K T):proc -> bool`
  \\ pop_assum kall_tac
  \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`s`,`v`,`p`,`c2`,`l`,`c1`,`iffy`,`pn`]
  \\ Induct
  >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def]
      >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
      >> `a1 = a2` suffices_by simp[]
      >> unabbrev_all_tac
      >> rw[MAP_EQ_f] >> rw[]
      >> match_mp_tac project_if_l_eq
      >> conj_tac
      >- (first_x_assum drule >> fs[])
      >> conj_tac
      >- (CCONTR_TAC >> fs[])
      >> CCONTR_TAC
      >> fs[] >> rveq >> fs[preSel_def])
  \\ rpt strip_tac
  \\ `?b q c1'. c1 = Sel p b q c1'`
        by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c1` >> rw[preSel_def])
  \\ rveq
  \\ `MEM q l` by(fs[preSel_def])
  \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  \\ `p <> q` by(CCONTR_TAC >> fs[])
  \\ `project_ok q [] c1'`
      by(imp_res_tac compile_network_ok_project_ok
         \\ rfs[project_def,split_sel_def]
         \\ Cases_on `b` \\ fs[])
  \\ first_assum drule
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
  \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                                          queue := preSel_to_queue q p (preSel p c1')|> (project' q [] c1'))`
  \\ `trans (af q) (LTau) (ag q)`
     by(unabbrev_all_tac >> Cases_on `iffy q`
        >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
              split_sel_def,compile_network_gen_def,preSel_to_queue_def]
        >> rfs[]
        >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
        >> simp[cut_ext_choice_upto_presel_def,SPLITP]
        >> TRY(match_mp_tac trans_ext_choice_l_gen
               >> fs[] >> qexists_tac `[]` >> fs[])
        >> TRY(match_mp_tac trans_ext_choice_r_gen
               >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
  \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
            LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
       by(simp[trans_fold_par])
  \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
  \\ qabbrev_tac `ah = (λproc.
              NEndpoint proc
                <|bindings := projectS proc s;
                queue := preSel_to_queue proc p (preSel p c1')|>
                (project' proc [] (if iffy' proc then IfThen v p c1' c2 else c1')))`
  \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
  \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
  \\ conj_tac
  >- (simp[reduction_def]
      \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
          suffices_by metis_tac[]
      \\ unabbrev_all_tac
      \\ rw[MAP_EQ_f]
      \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
      \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
      \\ `proc <> p` by(CCONTR_TAC >> fs[])
      \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
      \\ rw[] \\ fs[project_def,split_sel_def])
  \\ first_x_assum (qspecl_then [`iffy'`,`c1'`,`l`,`c2`,`p`,`v`,`s`] mp_tac)
  \\ `project_ok p [] c1'` by(fs[project_def])
  \\ `compile_network_ok s c1' l` by(imp_res_tac compile_network_ok_dest_sel)
  \\ rpt(disch_then drule)
  \\ impl_tac
  >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
      >> fs[preSel_def] >> unabbrev_all_tac
      >> fs[no_self_comunication_def,no_undefined_vars_def,free_variables_def]
      >> rw[] >> rpt(first_x_assum drule) >> simp[]
      >> `proc <> p` by(CCONTR_TAC >> fs[])
      >> fs[project_def,split_sel_def]
      >> rw[])
  \\ qmatch_goalsub_abbrev_tac
       `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
  \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
  \\ unabbrev_all_tac
  \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
  \\ `proc <> p` by(CCONTR_TAC >> fs[])
  >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
      \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
  >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
      >> rw[cut_ext_choice_upto_presel_def,SPLITP])
  >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
      \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
QED

Theorem compile_network_preservation_ln:
   ∀s c α s' c' . compile_network_ok s c (procsOf c)
    ∧ trans (s,c) (α,[]) (s',c') ∧ chor_tl s c = (s',c') ∧ dvarsOf c = []
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s  c  (procsOf c))
                      (compile_network s' (catchup_of α c') (procsOf c))
Proof
    `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ (compile_network_ok s c (procsOf c) ∧ τ = [] ∧ chor_tl s c = (s',c') ∧ dvarsOf c = [] ∧
        no_self_comunication c
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'  (catchup_of α c') (procsOf c)))`
  suffices_by metis_tac [compile_network_ok_no_self_comunication]
  \\ ho_match_mp_tac trans_pairind
  \\ rw [ compile_network_gen_def
        , dvarsOf_def
        , procsOf_def
        , procsOf_all_distinct
        , nub'_def
        , reduction_def
        , project_def
        , FILTER_FILTER
        , FOLDL
        , chor_tl_def
        , fupdate_projectS
        , catchup_of_def
        , trans_ln_refl
        , no_self_comunication_def
        , trans_ln_cut_sel_upto
        , dsubst_def]
  (* Com *)
  >- (IMP_RES_TAC lookup_projectS
     \\ rw [trans_ln_def,fupdate_projectS]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                               , `s'   = s |+ ((v2,p2),d)`
                               , `s1   = projectS p1 s`
                               , `s2   = projectS p2 s`
                               , `s2'  = projectS p2 s'`
                               , `cp1  = SND (project p1 [] c')`
                               , `cp2  = SND (project p2 [] c')`
                               , `ns   = compile_network s' c' l`
                               , `s1q  = <|bindings := s1; queue := []|>`
                               , `s2q  = <|bindings := s2; queue := []|>`
                               ]
     \\ `compile_network s (Com p1 v1 p2 v2 c') l = ns`
        by (rw [Abbr `l`, Abbr `ns`, Abbr `s'`
               , MEM_FILTER, cn_ignore_com, cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC
        `NPar  (NEndpoint p1 s1q cp1)
        (NPar  (NEndpoint p2 (s2q with queue := SNOC (p1,d) s2q.queue)
                             (Receive p1 v2 cp2)) ns)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_com_l
        \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`d`]
        \\ rw []
        >- (ho_match_mp_tac trans_send
           \\ rw [Abbr `s1q`])
        >- (ho_match_mp_tac trans_par_l
           \\ ho_match_mp_tac trans_enqueue
           \\ rw []))
     >- (ho_match_mp_tac RTC_SINGLE
        \\ rw [reduction_def]
        \\ ho_match_mp_tac trans_par_r
        \\ ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac trans_dequeue_gen
        \\ MAP_EVERY Q.EXISTS_TAC [`d`,`[]`,`[]`]
        \\ rw [Abbr `s2q`, Abbr `s2`,Abbr `s'`,Abbr `s2'`,projectS_fupdate]))
  (* Sel-T *)
  >- (rw [trans_ln_def]
      \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                                , `s1   = <| bindings := projectS p1 s;
                                             queue := [] |>`
                                , `s2   = <| bindings := projectS p2 s;
                                             queue := [] |>`
                                , `cp1  = SND (project p1 [] c')`
                                , `cp2  = SND (project p2 [] c')`
                                , `ns   = compile_network s c' l`
                                ]
      \\ `compile_network s (Sel p1 T p2 c') l = ns`
         by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_sel])
      \\ ASM_REWRITE_TAC []
      \\ pop_assum (K ALL_TAC)
      \\ ho_match_mp_tac RTC_TRANS
      \\ Q.EXISTS_TAC `NPar (NEndpoint p1 s1 cp1)
                            (NPar (NEndpoint p2 (s2 with <|queue := [(p1,[1w])]|>)
                                             (ExtChoice p1 cp2 Nil))
                                  ns)`
      \\ rw []
      >- (rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_com_choice_l
         \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`T`]
         \\ rw []
         >- (ho_match_mp_tac trans_int_choice >> rw [])
         >- (ho_match_mp_tac trans_par_l
            \\ ho_match_mp_tac trans_enqueue_choice_gen
            \\ rw []))
      >- (ho_match_mp_tac RTC_SINGLE
         \\ rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_par_r
         \\ ho_match_mp_tac trans_par_l
         \\ ho_match_mp_tac trans_ext_choice_l_gen
         \\ rw []))
  (* Sel-F *)
  >- (rw [trans_ln_def]
      \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                                , `s1   = <| bindings := projectS p1 s;
                                             queue := [] |>`
                                , `s2   = <| bindings := projectS p2 s;
                                             queue := [] |>`
                                , `cp1  = SND (project p1 [] c')`
                                , `cp2  = SND (project p2 [] c')`
                                , `ns   = compile_network s c' l`
                                ]
      \\ `compile_network s (Sel p1 F p2 c') l = ns`
         by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_sel])
      \\ ASM_REWRITE_TAC []
      \\ pop_assum (K ALL_TAC)
      \\ ho_match_mp_tac RTC_TRANS
      \\ Q.EXISTS_TAC `NPar (NEndpoint p1 s1 cp1)
                            (NPar (NEndpoint p2 (s2 with <|queue := [(p1,[0w])]|>)
                                             (ExtChoice p1 Nil cp2))
                                  ns)`
      \\ rw []
      >- (rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_com_choice_l
         \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`F`]
         \\ rw []
         >- (ho_match_mp_tac trans_int_choice >> rw [])
         >- (ho_match_mp_tac trans_par_l
            \\ ho_match_mp_tac trans_enqueue_choice_gen
            \\ rw []))
      >- (ho_match_mp_tac RTC_SINGLE
         \\ rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_par_r
         \\ ho_match_mp_tac trans_par_l
         \\ ho_match_mp_tac trans_ext_choice_r_gen
         \\ rw []))
  (* Let *)
  >- (rw [trans_ln_def]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p ≠ y) (nub' (procsOf c'))`
                               , `s' = s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))`
                               , `s1   = projectS p s`
                               , `s1'  = projectS p s'`
                               , `cp1  = project p [] c'`
                               , `cp2  = project p [] c'`
                               , `ns   = compile_network s' c' l`
                               , `sq  = <|bindings := s1; queue := []|>`
                               , `sq'  = <|bindings := s1'; queue := []|>`
                               ]
     \\ `compile_network s (Let v p f vl c') l = ns`
        by (rw [ Abbr `l`, Abbr `ns`, Abbr `s'`, MEM_FILTER
               , cn_ignore_let , cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ qpat_x_assum ‘no_self_comunication _’ kall_tac
     \\ ho_match_mp_tac RTC_SINGLE
     \\ rw [reduction_def]
     \\ ho_match_mp_tac trans_par_l
     \\ ho_match_mp_tac trans_let_gen
     \\ UNABBREV_ALL_TAC
     \\ pop_assum (K ALL_TAC)
     \\ pop_assum (K ALL_TAC)
     \\ rw []
     >- (Induct_on `vl` \\ rw [lookup_projectS'])
     >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
        \\ Induct_on `vl` >> rw [lookup_projectS']))
  (* If true *)
  >- (drule reduction_if_true \\ disch_then (qspecl_then [‘c'’,‘c2’] mp_tac)
      \\ rw [compile_network_gen_def,project_def,procsOf_def,nub'_def]
      \\ pop_assum irule \\ simp [] \\ gs [no_self_comunication_def])
  (* If false *)
  >- (drule reduction_if_false \\ disch_then (qspecl_then [‘c1’,‘c'’] mp_tac)
      \\ rw [compile_network_gen_def,project_def,procsOf_def,nub'_def]
      \\ pop_assum irule \\ simp [] \\ gs [no_self_comunication_def])
  \\ TRY (simp [trans_ln_catchup_of_pair,no_self_comunication_def] \\ NO_TAC)
  >- (CCONTR_TAC
      \\ qpat_x_assum ‘p ∉ _’ mp_tac
      \\ qpat_x_assum ‘trans _ (α,[]) _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘s’,‘v’,‘p’,‘c'''’,‘α’]
      \\ Induct_on ‘c''’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      >- metis_tac []
      >- (first_x_assum drule \\ simp [freeprocs_def])
      \\ qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
      \\ EVAL_TAC \\ fs [])
  >- (fs [lcong_nil_simp]
      \\ CCONTR_TAC
      \\ qpat_x_assum ‘p ∉ _’ mp_tac
      \\ qpat_x_assum ‘trans _ (α,[]) _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘s’,‘v’,‘p’,‘c''’,‘α’]
      \\ Induct_on ‘c'''’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      >- metis_tac [lcong_nil_simp]
      >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
          \\ EVAL_TAC \\ fs [])
      \\ first_x_assum drule \\ simp [freeprocs_def])
  >- (Cases_on ‘α ≠ LFix’
      >- (drule trans_not_eq \\ fs [])
      \\ gs [catchup_of_def,project_def])
  >- (CCONTR_TAC
      \\ ntac 6 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 6 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 6 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 5 (pop_assum kall_tac)
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p’,‘v’,‘f’,‘vl’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  (* TODO: Fix *)
  >- (qmatch_goalsub_abbrev_tac ‘compile_network s _ l’
      \\ pop_assum kall_tac
      \\ Induct_on ‘l’
      \\ rw [compile_network_gen_def]
      \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘reduction^* (NPar a1 b1) (NPar a2 b2)’
      \\ irule RTC_SPLIT
      \\ qexists_tac ‘NPar a1 b2’
      \\ conj_tac
      >- (irule reduction_par_r \\ simp [])
      \\ irule reduction_par_l
      \\ unabbrev_all_tac
      \\ Cases_on ‘MEM h (procsOf c)’
      >- (irule RTC_TRANS \\ simp [project_def,reduction_def]
          \\ fs [dprocsOf_MEM_eq]
          \\ irule_at Any endpointSemTheory.trans_fix
          \\ drule_at Any project'_dsubst_commute
          \\ disch_then (qspec_then ‘c’ mp_tac)
          \\ impl_tac
          >- fs [project_def,dprocsOf_MEM_eq,dvarsOf_def]
          \\ rw []
          \\ qmatch_goalsub_abbrev_tac ‘RTC _ (NEndpoint _ _ (dsubst _ _ a1))’
          \\ qmatch_goalsub_abbrev_tac ‘RTC _ _ (NEndpoint _ _ (dsubst _ _ a2))’
          \\ ‘a1 = a2’ by (UNABBREV_ALL_TAC \\ simp [project_def,dprocsOf_MEM_eq])
          \\ simp [])
      \\ qspecl_then [‘c’,‘h’,‘dn’,‘dn’] assume_tac procsOf_dsubst_MEM_eq
      \\ ‘¬MEM h (procsOf (Fix dn c))’ by fs [procsOf_def,MEM_nub']
      \\ gs [project_nonmember_nil])
  >- (qpat_x_assum ‘trans _ _ _’ (assume_tac o ONCE_REWRITE_RULE [trans_cases])
      \\ fs []  \\ rveq
      \\ fs [not_trans_LFix_if_l,not_trans_LFix_if_r]
      \\ pop_assum kall_tac
      \\ pop_assum (assume_tac o Q.AP_TERM ‘chorLang$chor_size’)
      \\ fs [chorLangTheory.chor_size_def])
  >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chorLang$chor_size”)
      \\ EVAL_TAC \\ fs [])
  >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chorLang$chor_size”)
      \\ EVAL_TAC \\ fs [])
  \\ qpat_x_assum ‘trans _ _ _’ (assume_tac o ONCE_REWRITE_RULE [trans_cases])
  \\ fs []  \\ rveq
  \\ gs [not_trans_LFix_if_l,not_trans_LFix_if_r,lcong_nil_simp]
  \\ pop_assum kall_tac
  \\ pop_assum (assume_tac o Q.AP_TERM ‘chorLang$chor_size’)
  \\ fs [chorLangTheory.chor_size_def]
QED

Theorem procsOf_catchup_of:
  MEM h (procsOf (catchup_of α c)) ⇒ MEM h (procsOf c)
Proof
  Cases_on ‘α’ >> fs[catchup_of_def] >>
  Induct_on ‘c’ >> fs[procsOf_def,cut_sel_upto_def] >>
  rw[MEM_nub'] >>
  fs[procsOf_def,MEM_nub']
QED

Theorem trans_procsOf:
  ∀s c α l s' c' p.
  trans (s,c) (α,l) (s',c') ∧ MEM p (procsOf c') ⇒ MEM p (procsOf c)
Proof
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_pairind >>
  rw[procsOf_def,MEM_nub'] >>
  simp[] >>
  fs[GSYM dsubst_procsOf_set_eq_Fix]
QED

Theorem trans_label_procsOf_written:
  ∀s c α l s' c' x.
  trans (s,c) (α,l) (s',c') ∧ ~MEM h (procsOf c) ⇒
  written α ≠ SOME (x,h)
Proof
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_pairind >>
  rw[procsOf_def,MEM_nub'] >>
  simp[written_def]
QED

Theorem compile_network_preservation_ln_gen:
   ∀s c α s' c' ps. compile_network_ok s c ps
    ∧ trans (s,c) (α,[]) (s',c') ∧ chor_tl s c = (s',c') ∧ dvarsOf c = []
    ∧ set (procsOf c) ⊆ set ps ∧ ALL_DISTINCT ps
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s  c ps)
                      (compile_network s' (catchup_of α c') ps)
Proof
  rpt GEN_TAC >> disch_then strip_assume_tac >>
  imp_res_tac compile_network_ok_subset >>
  drule_all_then strip_assume_tac compile_network_preservation_ln >>
  simp[] >>
  qspecl_then [‘λp. MEM p (procsOf c)’,‘ps’] assume_tac PERM_SPLIT >>
  ‘PERM (FILTER (λp. MEM p (procsOf c)) ps) (procsOf c)’
    by(match_mp_tac PERM_ALL_DISTINCT >>
       rw[ALL_DISTINCT_FILTER,MEM_FILTER,FILTER_FILTER,EQ_IMP_THM] >>
       fs[SUBSET_DEF] >> res_tac >> fs[] >-
         (pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
          fs[FILTER_EQ_NIL,EVERY_MEM]) >>
       ‘ALL_DISTINCT (procsOf c)’ by(simp[procsOf_all_distinct]) >>
       qpat_x_assum ‘MEM _ (procsOf _)’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
       fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
       fs[FILTER_EQ_NIL,EVERY_MEM]) >>
  drule PERM_CONG >>
  disch_then(qspecl_then [‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’,‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’] mp_tac) >>
  simp[PERM_REFL] >>
  strip_tac >>
  dxrule_all PERM_TRANS >>
  pop_assum kall_tac >>
  strip_tac >>
  fs[Once PERM_SYM] >>
  match_mp_tac PERM_chor_compile_network_reduction' >>
  goal_assum drule >>
  conj_tac >-
    (drule ALL_DISTINCT_PERM >> simp[]) >>
  rename1 ‘procsOf c ++ rest’ >>
  match_mp_tac PERM_chor_compile_network_reduction' >>
  qexists_tac ‘rest ++ procsOf c’ >> simp[PERM_APPEND] >>
  conj_asm1_tac >- (drule ALL_DISTINCT_PERM >> disch_then(mp_tac o GSYM) >>
                    rw[] >> fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qhdtm_x_assum ‘PERM’ kall_tac >>
  Induct_on ‘rest’ >>
  simp[] >>
  rw[] >>
  res_tac >>
  simp[compile_network_gen_def] >>
  drule_then (mp_tac o ONCE_REWRITE_RULE[MONO_NOT_EQ]) trans_procsOf >>
  disch_then drule >>
  strip_tac >>
  drule (CONTRAPOS procsOf_catchup_of) >>
  disch_then(qspec_then ‘α’ assume_tac) >>
  simp[project_nonmember_nil] >>
  ‘projectS h s = projectS h s'’
    by(rw[fmap_eq_flookup,GSYM lookup_projectS'] >>
       CONV_TAC SYM_CONV >>
       drule_then match_mp_tac lookup_unwritten_after_trans_tup >>
       drule_then match_mp_tac trans_label_procsOf_written >>
       simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  match_mp_tac reduction_par_r >>
  simp[]
QED

Theorem compile_network_ok_chor_tl:
  ∀s c ps s' c'.
  compile_network_ok s c ps ∧ chor_tl s c = (s',c') ∧ dvarsOf c = [] ⇒
  compile_network_ok s' c' ps
Proof
  Induct_on ‘ps’ >> rw[compile_network_gen_def,dvarsOf_def] >>
  res_tac >>
  reverse (Cases_on ‘c’) >> fs[chor_tl_def,project_def,AllCaseEqs()] >> rveq >>
  fs[project_def] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
  >- (drule project'_dsubst_commute
      \\ disch_then (qspecl_then [‘h’,‘c''’,‘[]’] mp_tac)
      \\ simp [project_def])
  >- (‘¬MEM h (dprocsOf [] (Fix s'' c''))’ by simp [dprocsOf_def,MEM_nub']
      \\ drule project_nonmember_nil_lemma
      \\ impl_tac >- simp []
      \\ ‘¬MEM h (dprocsOf [(s'',dprocsOf [(s'',[])] c'')] c'')’
         by (simp [dprocsOf_MEM_eq]
             \\ conj_tac >- gs [dprocsOf_empty,procsOf_def,MEM_nub']
             \\ disj2_tac
             \\ gs [dprocsOf_empty,procsOf_def,MEM_nub'])
      \\ drule project_nonmember_nil_lemma
      \\ impl_tac >- gs [SUBSET_DEF,dvarsOf_def,nub'_FILTER,FILTER_EQ_NIL,EVERY_MEM,MEM_nub']
      \\ rw []
      \\ drule project'_dsubst_commute
      \\ disch_then (qspecl_then [‘h’,‘c''’,‘[]’] mp_tac)
      \\ impl_tac >- simp [] \\ fs [project_def])
  \\   metis_tac[split_sel_project_ok,split_sel_project_ok2]
QED

Definition trans_ln_cut_def:
  trans_ln_cut = (λp r. ∃τ q. trans p (τ,[]) q ∧
                 q = UNCURRY chor_tl p ∧
                 r = (FST q, catchup_of τ (SND q)))^*
End

Theorem compile_network_ok_catchup_of:
  compile_network_ok s c ps ⇒
  compile_network_ok s (catchup_of τ c) ps
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def] >>
  Induct_on ‘c’ >> fs[cut_sel_upto_def] >>
  rw[] >>
  drule compile_network_ok_dest_sel >>
  simp[]
QED

Theorem dvarsOf_cut_sel_upto:
  ∀α c.
    dvarsOf(cut_sel_upto p c) = dvarsOf c
Proof
  Induct_on ‘c’ >>
  rw[cut_sel_upto_def,dvarsOf_def,nub'_dvarsOf] >> first_x_assum MATCH_ACCEPT_TAC
QED

Theorem dvarsOf_catchup_of:
  ∀α c.
    dvarsOf(catchup_of α c) = dvarsOf c
Proof
  ho_match_mp_tac catchup_of_ind >>
  rw[catchup_of_def,dvarsOf_def,dvarsOf_cut_sel_upto]
QED

Theorem dvarsOf_chor_tl_nil:
  ∀s c s' c'.
    dvarsOf c = [] ∧
    chor_tl s c = (s',c') ⇒
    dvarsOf c' = []
Proof
  Induct_on ‘c’ >>
  rw[chor_tl_def,dvarsOf_def,MEM_nub',nub'_nil] >>
  fs[dvarsOf_def,nub'_nil] >>
  fs[FILTER_EQ_NIL,EVERY_MEM,MEM_nub'] >>
  ‘∀x. MEM x (dvarsOf (dsubst c s (Fix s c))) ⇒ F’
    by(strip_tac >>
       dep_rewrite.DEP_ONCE_REWRITE_TAC[set_dvarsOf_dsubst_eq] >>
       rw[dvarsOf_def,FILTER_EQ_NIL,EVERY_MEM,MEM_nub'] >>
       spose_not_then strip_assume_tac >> gs[]) >>
  spose_not_then strip_assume_tac >>
  Cases_on ‘dvarsOf (dsubst c s (Fix s c))’ >>
  fs[FORALL_AND_THM]
QED

Theorem compile_network_preservation_trans_ln_cut:
  ∀s c s' c'.
    compile_network_ok s  c (procsOf c) ∧ dvarsOf c = [] ∧
    trans_ln_cut (s,c) (s',c')
    ⇒ ∃s'' c''. trans_ln_cut (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))
Proof
   ‘∀p q.
    trans_ln_cut p q
    ⇒ ∀s c s' c' ps.
       compile_network_ok s  c ps ∧ dvarsOf c = [] ∧
       p = (s,c) ∧ q = (s',c') ∧ set(procsOf c) ⊆ set(ps) ∧ ALL_DISTINCT ps
       ⇒ ∃s'' c''.
          trans_ln_cut (s',c') (s'',c'') ∧
          reduction^* (compile_network s   c   ps)
                      (compile_network s'' c'' ps)’
   suffices_by metis_tac [SUBSET_REFL,procsOf_all_distinct]
   \\ ntac 3 strip_tac
   \\ pop_assum (mp_tac o REWRITE_RULE [trans_ln_cut_def])
   \\ map_every qid_spec_tac [‘q’,‘p’]
   \\ ho_match_mp_tac RTC_strongind
   \\ rw []
   >- (map_every qexists_tac [‘s’,‘c’] \\ fs [trans_ln_cut_def])
   \\ fs [GSYM trans_ln_cut_def]
   \\ Cases_on ‘chor_tl s c’
   \\ drule_all compile_network_preservation_ln_gen
   \\ rw [] \\ fs []
   \\ ‘compile_network_ok q (catchup_of τ r) ps’
        by metis_tac[compile_network_ok_chor_tl,compile_network_ok_catchup_of]
   \\ first_x_assum drule
   \\ impl_tac
   >- (simp[dvarsOf_catchup_of] >> imp_res_tac dvarsOf_chor_tl_nil >>
       fs[SUBSET_DEF] >> rw[] >> imp_res_tac procsOf_catchup_of >>
       imp_res_tac trans_procsOf >> res_tac)
   \\ strip_tac
   \\ metis_tac[RTC_RTC]
QED

Theorem no_self_comunication_cut_sel_upto:
  !p c. no_self_comunication c ==> no_self_comunication(cut_sel_upto p c)
Proof
  Induct_on `c` >> rw[cut_sel_upto_def,no_self_comunication_def]
QED

Theorem no_undefined_vars_cut_sel_upto:
  !p c. no_undefined_vars (s,c) ==> no_undefined_vars(s,cut_sel_upto p c)
Proof
  Induct_on `c` >> rw[cut_sel_upto_def,no_undefined_vars_def,free_variables_def] >>
  metis_tac[no_undefined_vars_def]
QED

Theorem no_self_comunication_catchup_of:
  ∀p τ.
  no_self_comunication p ⇒
  no_self_comunication (catchup_of τ p)
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def] >>
  metis_tac[no_self_comunication_cut_sel_upto]
QED

Theorem no_self_comunication_chor_tl:
  ∀p.
  no_self_comunication(SND p) ⇒
  no_self_comunication (SND(UNCURRY chor_tl p))
Proof
  PairCases >> Cases_on ‘p1’ >> rw[no_self_comunication_def,chor_tl_def] >>
  match_mp_tac no_self_comunication_dsubst >> rw[no_self_comunication_def]
QED

Theorem trans_ln_cut_IMP_trans_ln:
  ∀p q.
  trans_ln_cut p q ∧ no_self_comunication(SND p) ⇒ trans_ln p q
Proof
  simp[trans_ln_cut_def,trans_ln_def,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  fs[] >>
  imp_res_tac no_self_comunication_chor_tl >>
  drule_then(qspec_then ‘τ’ mp_tac) no_self_comunication_catchup_of >>
  strip_tac >>
  fs[] >>
  match_mp_tac RTC_TRANS >>
  simp[PULL_EXISTS] >>
  goal_assum drule >>
  pop_assum kall_tac >>
  drule trans_ln_catchup_of >>
  disch_then(qspec_then ‘τ’ strip_assume_tac) >>
  match_mp_tac(MP_CANON RTC_RTC) >>
  fs[trans_ln_def] >>
  goal_assum drule >>
  simp[]
QED

Theorem NRC_catchup:
  ∀p c s.
  no_self_comunication c ⇒
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p)
      (LENGTH (preSel p c))
      (s,c) (s,cut_sel_upto p c)
Proof
  ho_match_mp_tac(fetch "-" "preSel_ind") >> rw[] >>
  rw[preSel_def,NRC,chor_tl_def,PULL_EXISTS] >>
  fs[no_self_comunication_def] >>
  res_tac >>
  simp[Once cut_sel_upto_def] >>
  metis_tac[trans_rules]
QED

Theorem NRC_trans_ln_eq_deriv:
  ∀n p q r.
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p) n p q ∧
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p) n p r ⇒
  q = r
Proof
  Induct >> rw[] >>
  fs[NRC] >> res_tac >>
  rveq >>
  res_tac
QED

Theorem trans_ln_IMP_trans_ln_cut:
  ∀p q.
  trans_ln p q ∧ no_self_comunication(SND p) ⇒ ∃q'. trans_ln_cut p q' ∧ trans_ln q q'
Proof
  simp[Once trans_ln_def,GSYM AND_IMP_INTRO,GSYM PULL_FORALL,RTC_eq_NRC,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV List.rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases >> rw[NRC] >-
    (metis_tac[trans_ln_cut_def,trans_ln_def,RTC_REFL]) >>
  imp_res_tac no_self_comunication_chor_tl >>
  rename1 ‘SUC n’ >>
  Cases_on ‘τ’ >-
    (rename1 ‘LTau proc v’ >>
     Cases_on ‘LENGTH(preSel proc (SND(UNCURRY chor_tl p))) > n’ >-
       (drule NRC_catchup >>
        disch_then(qspecl_then [‘proc’,‘FST(UNCURRY chor_tl p)’] mp_tac) >>
        strip_tac >>
        fs[PAIR] >>
        qmatch_asmsub_abbrev_tac ‘NRC _ _ _ a1’ >> qexists_tac ‘a1’ >>
        qunabbrev_tac ‘a1’ >>
        conj_tac >-
         (simp[trans_ln_cut_def] >>
          match_mp_tac RTC_SUBSET >>
          simp[] >>
          goal_assum drule >>
          simp[catchup_of_def]) >>
        fs[GREATER_DEF] >>
        imp_res_tac LESS_ADD >>
        pop_assum(SUBST_ALL_TAC o GSYM) >>
        FULL_SIMP_TAC std_ss [Once ADD_SYM] >>
        FULL_SIMP_TAC std_ss [NRC_ADD_EQN] >>
        pop_assum mp_tac >>
        drule NRC_trans_ln_eq_deriv >>
        disch_then(last_assum o mp_then Any mp_tac) >>
        rpt strip_tac >> rveq >>
        simp[trans_ln_def] >>
        match_mp_tac NRC_RTC >>
        goal_assum drule) >>
     fs[GREATER_DEF,NOT_LESS] >>
     imp_res_tac LESS_EQ_ADD_EXISTS >>
     rveq >>
     FULL_SIMP_TAC std_ss [Once ADD_SYM] >>
     FULL_SIMP_TAC std_ss [NRC_ADD_EQN] >>
     drule NRC_catchup >>
     disch_then(qspecl_then [‘proc’,‘FST(UNCURRY chor_tl p)’] mp_tac) >>
     strip_tac >>
     fs[PAIR] >>
     drule NRC_trans_ln_eq_deriv >>
     disch_then(last_assum o mp_then Any mp_tac) >>
     strip_tac >> rveq >> fs[] >>
     first_x_assum(qspec_then ‘p'’ mp_tac) >>
     impl_tac >- simp[] >>
     disch_then drule >>
     impl_tac >- (simp[] >> metis_tac[no_self_comunication_cut_sel_upto]) >>
     strip_tac >>
     simp[Once CONJ_SYM] >> goal_assum drule >>
     fs[trans_ln_cut_def] >>
     match_mp_tac RTC_TRANS >>
     simp[PULL_EXISTS] >> goal_assum drule >>
     simp[PULL_EXISTS,catchup_of_def]) >>
  first_x_assum(qspec_then ‘n’ mp_tac) >>
  simp[] >> disch_then drule >>
  simp[] >>
  strip_tac >>
  qexists_tac ‘q'’ >> simp[] >>
  simp[trans_ln_cut_def] >>
  match_mp_tac RTC_TRANS >>
  fs[trans_ln_cut_def] >>
  simp[Once CONJ_SYM] >>
  goal_assum drule >>
  goal_assum drule >>
  simp[catchup_of_def]
QED

Theorem trans_ln_no_self_comunication:
  ∀sc sc'.
  trans_ln sc sc' ∧ no_self_comunication (SND sc) ⇒
  no_self_comunication(SND sc')
Proof
  simp[trans_ln_def,Once CONJ_SYM] >>
  ho_match_mp_tac RTC_lifts_invariants >>
  rpt PairCases >>
  rw[] >>
  imp_res_tac no_self_comunication_trans_pres
QED

Theorem compile_network_preservation_trans_ln:
  ∀s c s' c' pn.
    compile_network_ok s  c (procsOf c) ∧ dvarsOf c = [] ∧
    trans_ln (s,c) (s',c')
    ⇒ ∃s'' c''. trans_ln (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))
Proof
  rpt strip_tac >>
  drule trans_ln_IMP_trans_ln_cut >>
  impl_tac >- metis_tac[compile_network_ok_no_self_comunication,SND] >>
  strip_tac >>
  drule compile_network_preservation_trans_ln_cut >>
  rename1 ‘trans_ln_cut (s,c) sc’ >>
  PairCases_on ‘sc’ >>
  disch_then drule >>
  strip_tac >>
  drule trans_ln_cut_IMP_trans_ln >>
  impl_tac >-
    (drule compile_network_ok_no_self_comunication >>
     strip_tac >>
     imp_res_tac trans_ln_no_self_comunication >>
     fs[]) >>
  strip_tac >>
  drule_then drule trans_ln_trans_ln >>
  strip_tac >>
  res_tac >>
  goal_assum(drule_at (Pos last)) >>
  drule trans_ln_cut_IMP_trans_ln >>
  impl_tac >-
    (drule compile_network_ok_no_self_comunication >>
     strip_tac >>
     imp_res_tac trans_ln_no_self_comunication >>
     fs[]) >>
  metis_tac[trans_ln_trans_ln]
QED

Theorem compile_network_ok_project_ok:
  !s c pn. compile_network_ok s c pn <=> (!p. MEM p pn ==> project_ok p [] c)
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >> conj_tac >>
  Induct_on `pn` >>
  rw[compile_network_gen_def] >> simp[] >>
  res_tac
QED

Theorem chor_size_cut_sel_upto:
  !p c. chor_to_endpoint$chor_size (cut_sel_upto p c) <= chor_to_endpoint$chor_size c
Proof
  strip_tac >> Induct_on `c` >> rw[cut_sel_upto_def,chor_size_def] >> intLib.COOPER_TAC
QED

Theorem project_ok_cut_sel_upto:
  !p' c1 p dvars.
  project_ok p' dvars c1 ==>
  project_ok p' dvars (cut_sel_upto p c1)
Proof
  Induct_on `c1` >> rw[cut_sel_upto_def] >>
  fs[project_def] >>
  every_case_tac >> fs[]
QED

Theorem procsOf_cut_sel_upto:
  !p c1.
  set(procsOf(cut_sel_upto p c1)) ⊆ set(procsOf c1)
Proof
  Induct_on `c1` >> rw[cut_sel_upto_def,procsOf_def,set_nub'] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem compile_network_project:
  !s v p c' c2 l.
   compile_network s c l =
   FOLDR NPar NNil
   (MAP (λproc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (project' proc [] c)) l)
Proof
   Induct_on `l`
   >- rw[compile_network_gen_def]
   >> rpt strip_tac
   >> fs[compile_network_gen_def]
   >> fs[project_def]
QED

Theorem compile_network_eq_FOLDR:
  ∀s c l.
  compile_network s c l =
  FOLDR NPar NNil
        (MAP
         (λproc.
           NEndpoint proc
                     <|bindings := projectS proc s; queue := []|>
                     (project' proc [] c)) l)
Proof
  Induct_on ‘l’ >> rw[compile_network_gen_def]
QED

(* TODO: move to endpointProps? *)
Theorem trans_FOLDR_NPar_cases:
 ∀ps α q.
  trans (FOLDR NPar NNil ps) α q =
  ((∃ps1 p p' ps2.
     ps = ps1 ++ p::ps2 ∧
     trans p α p' ∧
     q = FOLDR NPar NNil (ps1 ++ p'::ps2)) ∨
   (∃ps1 n1 n1' ps2 n2 n2' ps3 p1 d p2.
     α = LTau ∧
     ps = ps1 ++ n1::ps2 ++ n2::ps3 ∧
     p1 ≠ p2 ∧
     trans n1 (LSend p1 d p2) n1' ∧
     trans n2 (LReceive p1 d p2) n2' ∧
     q = FOLDR NPar NNil (ps1 ++ n1'::ps2 ++ n2'::ps3)) ∨
   (∃ps1 n1 n1' ps2 n2 n2' ps3 p1 d p2.
     α = LTau ∧
     ps = ps1 ++ n1::ps2 ++ n2::ps3 ∧
     p1 ≠ p2 ∧
     trans n1 (LReceive p1 d p2) n1' ∧
     trans n2 (LSend p1 d p2) n2' ∧
     q = FOLDR NPar NNil (ps1 ++ n1'::ps2 ++ n2'::ps3)) ∨
   (∃ps1 n1 n1' ps2 n2 n2' ps3 p1 b p2.
     α = LTau ∧
     ps = ps1 ++ n1::ps2 ++ n2::ps3 ∧
     p1 ≠ p2 ∧
     trans n1 (LIntChoice p1 b p2) n1' ∧
     trans n2 (LExtChoice p1 b p2) n2' ∧
     q = FOLDR NPar NNil (ps1 ++ n1'::ps2 ++ n2'::ps3)) ∨
   (∃ps1 n1 n1' ps2 n2 n2' ps3 p1 b p2.
     α = LTau ∧
     ps = ps1 ++ n1::ps2 ++ n2::ps3 ∧
     p1 ≠ p2 ∧
     trans n1 (LExtChoice p1 b p2) n1' ∧
     trans n2 (LIntChoice p1 b p2) n2' ∧
     q = FOLDR NPar NNil (ps1 ++ n1'::ps2 ++ n2'::ps3)))
Proof
  Induct_on ‘ps’ >- (rw[Once endpointSemTheory.trans_cases]) >>
  rw[EQ_IMP_THM]
  >-  (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[endpointSemTheory.trans_cases]) >>
       fs[] >> rveq >> fs[]
       >- ((* com_l *)
           rfs[] >>
           disj2_tac >> disj1_tac >>
           qexists_tac ‘[]’ >>
           simp[] >>
           irule_at (Pos hd) EQ_REFL >>
           rpt(goal_assum drule) >>
           simp[])
       >- ((* com_r *)
           rfs[] >>
           ntac 2 disj2_tac >> disj1_tac >>
           qexists_tac ‘[]’ >>
           simp[] >>
           irule_at (Pos hd) EQ_REFL >>
           rpt(goal_assum drule) >>
           simp[])
       >- ((* com_choice_l *)
           rfs[] >>
           ntac 3 disj2_tac >> disj1_tac >>
           qexists_tac ‘[]’ >>
           simp[] >>
           irule_at (Pos hd) EQ_REFL >>
           rpt(goal_assum drule) >>
           simp[])
       >- ((* com_choice_r *)
           rfs[] >>
           ntac 4 disj2_tac >>
           qexists_tac ‘[]’ >>
           simp[] >>
           irule_at (Pos hd) EQ_REFL >>
           rpt(goal_assum drule) >>
           simp[])
       >- ((* par_l *)
           disj1_tac >> qexists_tac ‘[]’ >> simp[])
       >- ((* par_r *)
           rfs[]
           >- (disj1_tac >> Q.REFINE_EXISTS_TAC ‘_::_’ >> simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               goal_assum drule >> simp[])
           >- (disj2_tac >> disj1_tac >> Q.REFINE_EXISTS_TAC ‘_::_’ >> simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               rpt(goal_assum drule) >> simp[])
           >- (ntac 2 disj2_tac >> disj1_tac >> Q.REFINE_EXISTS_TAC ‘_::_’ >> simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               rpt(goal_assum drule) >> simp[])
           >- (ntac 3 disj2_tac >> disj1_tac >> Q.REFINE_EXISTS_TAC ‘_::_’ >> simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               rpt(goal_assum drule) >> simp[])
           >- (ntac 4 disj2_tac >> Q.REFINE_EXISTS_TAC ‘_::_’ >> simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               rpt(goal_assum drule) >> simp[])))
  >- (Cases_on ‘ps1’ >> fs[] >> rveq >- metis_tac[trans_par_l] >>
      metis_tac[trans_par_r])
  >- (Cases_on ‘ps1’ >> fs[] >> rveq >- metis_tac[trans_com_l] >>
      metis_tac[trans_par_r,trans_com_l])
  >- (Cases_on ‘ps1’ >> fs[] >> rveq >- metis_tac[trans_com_r] >>
      metis_tac[trans_par_r,trans_com_r])
  >- (Cases_on ‘ps1’ >> fs[] >> rveq >- metis_tac[trans_com_choice_l] >>
      metis_tac[trans_par_r,trans_com_choice_l])
  >- (Cases_on ‘ps1’ >> fs[] >> rveq >- metis_tac[trans_com_choice_r] >>
      metis_tac[trans_par_r,trans_com_choice_r])
QED

(* TODO: move to endpointProps *)
Theorem qcong_reduction_pres:
  ∀p1 p2 q1.
    qcong p1 q1 ∧ reduction꙳ p1 p2 ⇒
    ∃q2. reduction꙳ q1 q2 ∧ qcong p2 q2
Proof
  simp[Once CONJ_SYM] >> simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >- metis_tac[RTC_REFL,qcong_refl] >>
  irule_at (Pos hd) RTC_TRANS >>
  gs[reduction_def] >>
  drule_all_then strip_assume_tac qcong_trans_pres >>
  res_tac >>
  rpt(goal_assum drule)
QED

Theorem reduction_list_trans:
  reduction^* p1 p2 ==>
  ?n. list_trans p1 (REPLICATE n LTau) p2
Proof
  rw[RTC_eq_NRC] >>
  qexists_tac `n` >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`p1`,`p2`] >>
  Induct_on `n` >>
  rw[list_trans_def,NRC,reduction_def] >>
  res_tac >> goal_assum drule >> rw[]
QED

Theorem list_trans_reduction:
  !n p1 p2.
  list_trans p1 (REPLICATE n LTau) p2 ==>
  reduction^* p1 p2
Proof
  Induct >>
  rw[list_trans_def] >>
  match_mp_tac RTC_TRANS >>
  simp[reduction_def] >>
  res_tac >> goal_assum drule >>
  simp[]
QED

Theorem reduction_list_trans_eq:
  reduction^* p1 p2 ⇔ ∃n. list_trans p1 (REPLICATE n LTau) p2
Proof
  metis_tac[reduction_list_trans,list_trans_reduction]
QED

Theorem endpoint_confluence:
  ∀m p1 p2 p3.
   reduction p1 p2 /\
   reduction꙳ p1 p3 /\
   ALL_DISTINCT (MAP FST (endpoints p1))
   ==>
   (?n p4. reduction꙳ p2 p4 /\
        qcong p3 p4) \/
   (?n p4 p5. reduction꙳ p2 p4 /\
        reduction p3 p5 ∧
        qcong p4 p5)
Proof
  rw[reduction_list_trans_eq,reduction_def] >>
  drule_all_then strip_assume_tac endpoint_confluence_contract >>
  metis_tac[]
QED

Theorem SUBSET_compile_network_reduction:
  ∀l s s' c c' t.
    ALL_DISTINCT l
    ∧ set (procsOf c) ⊆ set l
    ∧ set (procsOf c') ⊆ set (procsOf c)
    ∧ reduction^* (compile_network s c (procsOf c)) (compile_network s c' (procsOf c))
    ⇒ reduction^* (compile_network s c l) (compile_network s c' l)
Proof
  rw []
  \\ drule SUBSET_PERM_exists_APPEND
  \\ disch_then (qspec_then ‘procsOf c’ mp_tac)
  \\ simp [chorSemTheory.procsOf_all_distinct]
  \\ rw []
  \\ irule PERM_chor_compile_network_reduction
  \\ qexists_tac ‘xs ++ procsOf c’
  \\ conj_tac >- (drule ALL_DISTINCT_PERM \\ disch_then (fs o single))
  \\ simp [PERM_SYM]
  \\ irule SUBSET_ep_reduction_with_extra
  \\ simp [chor_REPN_compile_network,chor_endpoints_compile_network_append]
  \\ MAP_EVERY qexists_tac [‘compile_network s c (procsOf c)’
                            ,‘compile_network s c' (procsOf c)’
                            ,‘endpoints (compile_network s c xs)’]
  \\ simp [chor_REPN_compile_network]
  \\ drule ALL_DISTINCT_PERM \\ disch_then (fs o single)
  \\ fs [ALL_DISTINCT_APPEND]
  \\ ‘∀e. MEM e xs ⇒ ¬MEM e (procsOf c')’
    by (rw [] \\ first_x_assum drule
        \\ fs [SUBSET_DEF] \\ rw []
        \\ drule MEM_PERM
        \\ disch_then (qspec_then ‘e’ (assume_tac o GSYM))
        \\ gs [MEM_APPEND]
        \\ CCONTR_TAC \\ gs [])
  \\ pop_assum mp_tac
  \\ ntac 4 (pop_assum kall_tac)
  \\ disch_then assume_tac
  \\ ntac 2 (last_x_assum kall_tac)
  \\ Induct_on ‘xs’
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,endpoints_def]
  \\ RES_TAC \\ fs [SUBSET_DEF]
  \\ pop_assum (qspec_then ‘h’ mp_tac)
  \\ pop_assum (qspec_then ‘h’ mp_tac)
  \\ rw []
  \\ fs [project_nonmember_nil]
QED

Theorem compile_network_reflection_lemma:
  ∀s c pn p2.
    compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_undefined_vars (s,c)
    ∧ no_self_comunication c
    ∧ dvarsOf c = []
    ∧ reduction (compile_network s c pn) p2
    ==> ∃s' c' p3.
             reduction^* p2 p3
             ∧ trans_s (s,c) (s',c')
             ∧ qcong p3 (compile_network s' c' pn)
             ∧ compile_network_ok s' c' pn
Proof
  ‘∀cs c s pn p2.
    cs = chor_to_endpoint$chor_size c ∧
    compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_undefined_vars (s,c)
    ∧ no_self_comunication c
    ∧ dvarsOf c = []
    ∧ reduction (compile_network s c pn) p2
    ==> ∃s' c' p3.
             reduction^* p2 p3
             ∧ trans_s (s,c) (s',c')
             ∧ qcong p3 (compile_network s' c' pn)
             ∧ compile_network_ok s' c' pn’ suffices_by metis_tac[] >>
  ho_match_mp_tac COMPLETE_INDUCTION >> Cases >- (rpt strip_tac >> Cases_on ‘c’ >> fs[chor_size_def]) >>
  strip_tac >> Cases >> fs[chor_size_def]
  >- ((* Nil *)
      pop_assum kall_tac >>
      rw[compile_network_eq_FOLDR,reduction_def,Once trans_FOLDR_NPar_cases] >>
      gs[MAP_EQ_APPEND] >> rveq >>
      fs[project_def] >>
      fs[Once endpointSemTheory.trans_cases])
  >- ((* IfThen *)
      rw[] >>
      rename [‘compile_network s (IfThen v p c1 c2) pn’] >>
      rename [‘reduction _ n2’] >>
      gs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
      rename1 ‘FLOOKUP _ _ = SOME d’ >>
      Cases_on ‘d = [1w]’ >-
        (‘reduction꙳ (compile_network s (IfThen v p c1 c2) pn)
                     (compile_network s (cut_sel_upto p c1) pn)’
           by (irule SUBSET_compile_network_reduction \\ simp []
               \\ conj_tac
               >- (simp [procsOf_def,set_nub']
                   \\ irule SUBSET_TRANS
                   \\ qexists_tac ‘set (procsOf c1)’
                   \\ simp [procsOf_cut_sel_upto]
                   \\ irule SUBSET_INSERT_RIGHT
                   \\ simp [])
               \\ irule reduction_if_true
               \\ fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
               \\ irule compile_network_ok_subset
               \\ asm_exists_tac \\ simp []) >>
         drule_then drule endpoint_confluence >>
         simp[FST_endpoints_compile_network] >>
         strip_tac
         >- (goal_assum drule >>
             irule_at (Pos hd) trans_s_step >>
             irule_at (Pos hd) trans_if_true >>
             simp[] >>
             irule_at (Pos hd) trans_ln_IMP_trans_s >>
             irule_at (Pos hd) trans_ln_cut_sel_upto >>
             fs[no_self_comunication_def] >>
             irule_at (Pos hd) qcong_sym >>
             goal_assum drule >>
             fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
             rpt strip_tac >> first_x_assum drule >>
             rw[project_def] >>
             TRY(drule_then MATCH_ACCEPT_TAC project_ok_cut_sel_upto) >>
             rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
             metis_tac[project_ok_cut_sel_upto,split_sel_project_ok]) >>
         last_x_assum(qspec_then ‘chor_to_endpoint$chor_size(cut_sel_upto p c1)’ mp_tac) >>
         impl_tac >- (qspecl_then [‘p’,‘c1’] assume_tac chor_size_cut_sel_upto >> DECIDE_TAC) >>
         disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         first_x_assum(fn thm => disch_then(resolve_then (Pat ‘reduction _ _’) mp_tac thm)) >>
         simp[] >>
         impl_tac
         >- (gs[dvarsOf_cut_sel_upto,no_self_comunication_cut_sel_upto,no_self_comunication_def,dvarsOf_def,
                free_variables_cut_sel_upto,procsOf_def,set_nub',nub'_nil] >>
             conj_tac
             >- (fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
                 rpt strip_tac >> first_x_assum drule >>
                 rw[project_def] >>
                 TRY(drule_then MATCH_ACCEPT_TAC project_ok_cut_sel_upto) >>
                 rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
                 metis_tac[project_ok_cut_sel_upto,split_sel_project_ok]) >>
             metis_tac[SUBSET_TRANS,procsOf_cut_sel_upto]) >>
         strip_tac >>
         goal_assum (drule_at (Pos last)) >>
         irule_at Any trans_s_step >>
         irule_at (Pos hd) trans_if_true >>
         simp[] >>
         irule_at (Pos hd) trans_s_trans_s >>
         irule_at (Pos hd) trans_ln_IMP_trans_s >>
         irule_at (Pos hd) trans_ln_cut_sel_upto >>
         fs[no_self_comunication_def] >>
         goal_assum drule >>
         irule_at (Pos hd) (MP_CANON RTC_RTC) >>
         goal_assum drule >>
         drule_at (Pos last) qcong_reduction_pres >>
         disch_then (resolve_then (Pos hd) mp_tac qcong_sym) >>
         disch_then drule >>
         strip_tac >>
         goal_assum drule >>
         metis_tac[qcong_trans,qcong_sym]) >>
      ‘reduction꙳ (compile_network s (IfThen v p c1 c2) pn)
                     (compile_network s (cut_sel_upto p c2) pn)’
           by (irule SUBSET_compile_network_reduction \\ simp []
               \\ conj_tac
               >- (simp [procsOf_def,set_nub']
                   \\ irule SUBSET_TRANS
                   \\ qexists_tac ‘set (procsOf c2)’
                   \\ simp [procsOf_cut_sel_upto]
                   \\ irule SUBSET_INSERT_RIGHT
                   \\ simp [])
               \\ irule reduction_if_false
               \\ fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
               \\ irule compile_network_ok_subset
               \\ asm_exists_tac \\ simp []) >>
      drule_then drule endpoint_confluence >>
      simp[FST_endpoints_compile_network] >>
      strip_tac
      >- (goal_assum drule >>
          irule_at (Pos hd) trans_s_step >>
          irule_at (Pos hd) trans_if_false >>
          simp[] >>
          irule_at (Pos hd) trans_ln_IMP_trans_s >>
          irule_at (Pos hd) trans_ln_cut_sel_upto >>
          fs[no_self_comunication_def] >>
          irule_at (Pos hd) qcong_sym >>
          goal_assum drule >>
          fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
          rpt strip_tac >> first_x_assum drule >>
          rw[project_def] >>
          TRY(drule_then MATCH_ACCEPT_TAC project_ok_cut_sel_upto) >>
          rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
          metis_tac[project_ok_cut_sel_upto,split_sel_project_ok]) >>
      last_x_assum(qspec_then ‘chor_to_endpoint$chor_size(cut_sel_upto p c2)’ mp_tac) >>
      impl_tac >- (qspecl_then [‘p’,‘c2’] assume_tac chor_size_cut_sel_upto >> DECIDE_TAC) >>
      disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      first_x_assum(fn thm => disch_then(resolve_then (Pat ‘reduction _ _’) mp_tac thm)) >>
      simp[] >>
      impl_tac
      >- (gs[dvarsOf_cut_sel_upto,no_self_comunication_cut_sel_upto,no_self_comunication_def,dvarsOf_def,
             free_variables_cut_sel_upto,procsOf_def,set_nub',nub'_nil] >>
          conj_tac
          >- (fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
              rpt strip_tac >> first_x_assum drule >>
              rw[project_def] >>
              TRY(drule_then MATCH_ACCEPT_TAC project_ok_cut_sel_upto) >>
              rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
              metis_tac[project_ok_cut_sel_upto,split_sel_project_ok]) >>
          metis_tac[SUBSET_TRANS,procsOf_cut_sel_upto]) >>
      strip_tac >>
      goal_assum (drule_at (Pos last)) >>
      irule_at Any trans_s_step >>
      irule_at (Pos hd) trans_if_false >>
      simp[] >>
      irule_at (Pos hd) trans_s_trans_s >>
      irule_at (Pos hd) trans_ln_IMP_trans_s >>
      irule_at (Pos hd) trans_ln_cut_sel_upto >>
      fs[no_self_comunication_def] >>
      goal_assum drule >>
      irule_at (Pos hd) (MP_CANON RTC_RTC) >>
      goal_assum drule >>
      drule_at (Pos last) qcong_reduction_pres >>
      disch_then (resolve_then (Pos hd) mp_tac qcong_sym) >>
      disch_then drule >>
      strip_tac >>
      goal_assum drule >>
      metis_tac[qcong_trans,qcong_sym])
  >- ((* Com *)
      rw[] >>
      rename [‘compile_network s (Com p1 v1 p2 v2 c) pn’] >>
      rename [‘reduction _ n2’] >>
      gs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
      rename1 ‘FLOOKUP _ _ = SOME d’ >>
      ‘p1 ≠ p2’
        by (fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
            res_tac >> fs[project_def] >>
            FULL_CASE_TAC >> fs[]) >>
      ‘reduction^* (compile_network s (Com p1 v1 p2 v2 c) pn) (compile_network (s |+ ((v2,p2),d)) c pn)’
        by(irule_at (Pos hd) chor_compile_network_COM' >>
           fs[procsOf_def,set_nub'] >>
           match_mp_tac RTC_TRANS >>
           simp[reduction_def] >>
           simp[compile_network_gen_def,project_def] >>
           irule_at (Pos hd) trans_com_l >>
           goal_assum drule >>
           irule_at (Pos hd) trans_send >>
           imp_res_tac lookup_projectS >>
           simp[] >>
           irule_at (Pos hd) trans_par_l >>
           irule_at (Pos hd) trans_enqueue >>
           simp[] >>
           match_mp_tac RTC_SUBSET >>
           simp[reduction_def] >>
           simp[fupdate_projectS] >>
           match_mp_tac trans_par_r >>
           rw[MEM_FILTER, cn_ignore_com, cn_ignore_state_update] >>
           match_mp_tac trans_par_l >>
           match_mp_tac trans_dequeue_gen >>
           simp[projectS_fupdate]) >>
      ‘ALL_DISTINCT (MAP FST (endpoints (compile_network s (Com p1 v1 p2 v2 c) pn)))’
        by(fs[FST_endpoints_compile_network]) >>
      Cases_on ‘n2 = compile_network (s |+ ((v2,p2),d)) c pn’ >-
        (rveq >>
         irule_at (Pos hd) RTC_REFL >>
         simp[trans_s_def] >>
         irule_at (Pos hd) RTC_SUBSET >>
         simp[PULL_EXISTS] >>
         irule_at (Pos hd) trans_com >>
         simp[] >> irule_at Any qcong_refl >>
         drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_com) >>
      drule_then drule endpoint_confluence >>
      simp[FST_endpoints_compile_network] >>
      strip_tac
      >- (goal_assum drule >>
          irule_at (Pos hd) trans_s_one >>
          irule_at (Pos hd) trans_com >>
          simp[qcong_sym] >>
          drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_com) >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c’ mp_tac) >>
      impl_tac >- gs[] >>
      disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      disch_then (drule_at (Pos last)) >>
      impl_tac >-
        (fs[no_self_comunication_def,procsOf_def,set_nub',DELETE_SUBSET_INSERT,dvarsOf_def,nub'_nil] >>
         drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_com) >>
      strip_tac >>
      drule_at (Pos last) qcong_reduction_pres >>
      disch_then(resolve_then (Pos hd) mp_tac qcong_sym) >>
      disch_then drule >>
      strip_tac >>
      irule_at (Pos hd) RTC_RTC >>
      rpt(goal_assum drule) >>
      irule_at (Pos hd) trans_s_step >>
      irule_at (Pos hd) trans_com >>
      simp[] >>
      goal_assum drule >>
      metis_tac[qcong_trans,qcong_sym])
  >- ((* Let *)
      rw[] >>
      rename [‘compile_network s (Let v p f vl c) pn’] >>
      rename [‘reduction _ n2’] >>
      gs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP,LIST_TO_SET_MAP] >>
      ‘EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))’
        by(rw[EVERY_MEM,MEM_MAP] >> fs[SUBSET_DEF,PULL_EXISTS] >>
           res_tac >> fs[FDOM_FLOOKUP]) >>
      ‘reduction (compile_network s (Let v p f vl c) pn)
                 (compile_network (s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))) c pn)’
        by(simp[reduction_def] >>
           match_mp_tac chor_PERM_compile_network_trans' >>
           qexists_tac ‘p::FILTER ($<> p) pn’ >>
           conj_tac
           >- (match_mp_tac PERM_ALL_DISTINCT >>
               rw[MEM_FILTER,FILTER_ALL_DISTINCT,EQ_IMP_THM] >>
               fs[procsOf_def,set_nub'] >>
               metis_tac[]) >>
           conj_tac >- (rw[MEM_FILTER,FILTER_ALL_DISTINCT,EQ_IMP_THM]) >>
           simp[compile_network_gen_def,project_def] >>
           rw[MEM_FILTER, cn_ignore_let, cn_ignore_state_update] >>
           match_mp_tac trans_par_l >>
           match_mp_tac trans_let_gen >>
           rw [projectS_fupdate] >>
           fs[EVERY_MEM,MAP_MAP_o,o_DEF,lookup_projectS'] >> metis_tac[]) >>
      ‘ALL_DISTINCT (MAP FST (endpoints (compile_network s (Let v p f vl c) pn)))’
        by(fs[FST_endpoints_compile_network]) >>
      Cases_on ‘n2 = compile_network (s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))) c pn’ >-
        (rveq >>
         irule_at (Pos hd) RTC_REFL >>
         simp[trans_s_def] >>
         irule_at (Pos hd) RTC_SUBSET >>
         simp[PULL_EXISTS] >>
         irule_at (Pos hd) trans_let >>
         simp[qcong_refl] >>
         fs[compile_network_ok_project_ok] >>
         rw[] >> res_tac >> fs[project_def] >>
         FULL_CASE_TAC >> fs[]) >>
      drule_all_then strip_assume_tac (endpoint_local_confluence_tau |> SIMP_RULE std_ss [GSYM reduction_def]) >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c’ mp_tac) >>
      impl_tac >- gs[] >>
      disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      disch_then (drule_at (Pos last)) >>
      impl_tac >-
        (fs[no_self_comunication_def,procsOf_def,set_nub',DELETE_SUBSET_INSERT,dvarsOf_def,nub'_nil] >>
         fs[compile_network_ok_project_ok] >>
         rw[] >> res_tac >> fs[project_def] >>
         FULL_CASE_TAC >> fs[]) >>
      strip_tac >>
      drule_at (Pos last) qcong_reduction_pres >>
      disch_then(resolve_then (Pos hd) mp_tac qcong_sym) >>
      disch_then drule >>
      strip_tac >>
      irule_at (Pos hd) RTC_TRANS >>
      rpt(goal_assum drule) >>
      irule_at (Pos hd) trans_s_step >>
      irule_at (Pos hd) trans_let >>
      simp[] >>
      goal_assum drule >>
      metis_tac[qcong_trans,qcong_sym]
     )
  >- ((* Sel *)
      rw[] >>
      rename [‘compile_network s (Sel p1 b p2 c) pn’] >>
      rename [‘reduction _ n2’] >>
      gs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
      ‘p1 ≠ p2’
        by (fs[compile_network_ok_project_ok,procsOf_def,set_nub'] >>
            res_tac >> fs[project_def] >>
            FULL_CASE_TAC >> fs[]) >>
      ‘reduction^* (compile_network s (Sel p1 b p2 c) pn) (compile_network s c pn)’
        by(irule_at (Pos hd) chor_compile_network_Sel' >>
           fs[procsOf_def,set_nub'] >>
           match_mp_tac RTC_TRANS >>
           simp[reduction_def] >>
           simp[compile_network_gen_def,project_def] >>
           irule_at (Pos hd) trans_com_choice_l >>
           goal_assum drule >>
           irule_at (Pos hd) trans_int_choice >>
           simp[] >>
           irule_at (Pos hd) trans_par_l >>
           irule_at (Pos hd) trans_enqueue_choice_gen >>
           simp[] >>
           rw[MEM_FILTER, cn_ignore_sel] >>
           match_mp_tac RTC_SUBSET >>
           simp[reduction_def] >>
           match_mp_tac trans_par_r >>
           match_mp_tac trans_par_l >>
           TRY(match_mp_tac trans_ext_choice_l_gen >> simp[] >> NO_TAC) >>
           TRY(match_mp_tac trans_ext_choice_r_gen >> simp[] >> NO_TAC)) >>
      ‘ALL_DISTINCT (MAP FST (endpoints (compile_network s (Sel p1 b p2 c) pn)))’
        by(fs[FST_endpoints_compile_network]) >>
      Cases_on ‘n2 = compile_network s c pn’ >-
        (rveq >>
         irule_at (Pos hd) RTC_REFL >>
         simp[trans_s_def] >>
         irule_at (Pos hd) RTC_SUBSET >>
         simp[PULL_EXISTS] >>
         irule_at (Pos hd) trans_sel >>
         simp[qcong_refl] >>
         drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_sel) >>
      drule_then drule (endpoint_confluence |> SIMP_RULE std_ss [GSYM reduction_def]) >>
      simp[FST_endpoints_compile_network] >>
      strip_tac
      >- (goal_assum drule >>
          irule_at (Pos hd) trans_s_one >>
          irule_at (Pos hd) trans_sel >>
          simp[qcong_sym] >>
          drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_sel) >>
      first_x_assum(qspec_then ‘chor_to_endpoint$chor_size c’ mp_tac) >>
      impl_tac >- gs[] >>
      disch_then(resolve_then (Pos hd) mp_tac EQ_REFL) >>
      disch_then (drule_at (Pos last)) >>
      impl_tac >-
        (fs[no_self_comunication_def,procsOf_def,set_nub',DELETE_SUBSET_INSERT,dvarsOf_def,nub'_nil] >>
         drule_then MATCH_ACCEPT_TAC compile_network_ok_dest_sel) >>
      strip_tac >>
      drule_at (Pos last) qcong_reduction_pres >>
      disch_then(resolve_then (Pos hd) mp_tac qcong_sym) >>
      disch_then drule >>
      strip_tac >>
      irule_at (Pos hd) RTC_RTC >>
      rpt(goal_assum drule) >>
      irule_at (Pos hd) trans_s_step >>
      irule_at (Pos hd) trans_sel >>
      simp[] >>
      goal_assum drule >>
      metis_tac[qcong_trans,qcong_sym]
     )
  >- ((* Fix *)
      pop_assum kall_tac >>
      rw[compile_network_eq_FOLDR,reduction_def,Once trans_FOLDR_NPar_cases]
      >- ((* the interesting case *)
          gs[MAP_EQ_APPEND] >> rveq >>
          qhdtm_x_assum ‘trans’ (strip_assume_tac o REWRITE_RULE[project_def]) >>
          rename [‘no_undefined_vars (s, Fix dn c)’] >>
          fs[dprocsOf_MEM_eq] >>
          reverse(Cases_on ‘MEM proc (procsOf c)’)
          >- (fs[project_def] >>
              spose_not_then kall_tac >>
              fs[Once endpointSemTheory.trans_cases] >>
              rveq >>
              rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)) >>
          fs[] >>
          irule_at Any trans_s_one >>
          irule_at Any trans_fix >>
          irule_at Any qcong_refl >>
          rename1 ‘ps1 ++ [proc] ++ ps2’ >>
          reverse conj_tac
          >- (fs[compile_network_ok_project_ok] >>
              rw[] >>
              match_mp_tac (project'_dsubst_commute
                            |> Ho_Rewrite.REWRITE_RULE [IMP_CONJ_THM,FORALL_AND_THM]
                            |> CONJUNCT2) >>
              fs[DISJ_IMP_THM,FORALL_AND_THM] >>
              gs[project_def,dprocsOf_MEM_eq] >>
              res_tac >>
              PURE_FULL_CASE_TAC >> fs[] >>
              dep_rewrite.DEP_ONCE_REWRITE_TAC [project_nonmember_nil_lemma] >>
              fs[dprocsOf_MEM_eq,dvarsOf_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF,MEM_nub']
             ) >>
          qpat_x_assum ‘_ ⊆ _’ kall_tac >>
          Induct_on ‘ps1’ >-
            (rw[] >> fs[Once endpointSemTheory.trans_cases] >> rveq >>
             fs[compile_network_gen_def] >>
             drule project'_dsubst_commute >>
             disch_then drule >>
             qpat_assum ‘project_ok _ _ _’ (mp_tac o REWRITE_RULE[project_def,dprocsOf_MEM_eq]) >>
             simp[] >>
             strip_tac >>
             disch_then drule >>
             impl_tac >- simp[] >>
             disch_then(mp_tac o REWRITE_RULE[project_def,dprocsOf_MEM_eq]) >>
             simp[] >>
             strip_tac >>
             CONV_TAC(RAND_CONV(REWRITE_CONV [project_def,dprocsOf_MEM_eq])) >>
             simp[] >>
             match_mp_tac reduction_par_r >>
             ntac 3 (pop_assum kall_tac) >>
             Induct_on ‘ps2’ >- simp[] >>
             rw[compile_network_gen_def] >>
             first_x_assum drule_all >>
             strip_tac >>
             match_mp_tac (MP_CANON RTC_RTC) >>
             irule_at (Pos last) reduction_par_r >>
             first_x_assum (irule_at (Pos hd)) >>
             match_mp_tac reduction_par_l >>
             simp[project_def,dprocsOf_MEM_eq] >>
             IF_CASES_TAC >-
               (simp[] >>
                match_mp_tac RTC_SUBSET >>
                simp[reduction_def,Once endpointSemTheory.trans_cases] >>
                drule project'_dsubst_commute >>
                disch_then drule >>
                qpat_assum ‘project_ok _ _ _’ (mp_tac o REWRITE_RULE[project_def,dprocsOf_MEM_eq]) >>
                simp[] >>
                strip_tac >>
                disch_then drule >>
                impl_tac >- simp[] >>
                rw[project_def,dprocsOf_MEM_eq]) >>
             dep_rewrite.DEP_ONCE_REWRITE_TAC[project_nonmember_nil] >>
             simp[] >>
             simp[procsOf_dsubst_not_MEM]) >>
          rw[compile_network_gen_def] >>
          first_x_assum drule_all >>
          strip_tac >>
          match_mp_tac (MP_CANON RTC_RTC) >>
          irule_at (Pos last) reduction_par_r >>
          first_x_assum (irule_at (Pos hd)) >>
          match_mp_tac reduction_par_l >>
          simp[project_def,dprocsOf_MEM_eq] >>
          IF_CASES_TAC >-
           (simp[] >>
            match_mp_tac RTC_SUBSET >>
            simp[reduction_def,Once endpointSemTheory.trans_cases] >>
            drule project'_dsubst_commute >>
            disch_then drule >>
            qpat_assum ‘project_ok _ _ _’ (mp_tac o REWRITE_RULE[project_def,dprocsOf_MEM_eq]) >>
            simp[] >>
            strip_tac >>
            disch_then drule >>
            impl_tac >- simp[] >>
            rw[project_def,dprocsOf_MEM_eq]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[project_nonmember_nil] >>
          simp[] >>
          simp[procsOf_dsubst_not_MEM]) >>
      gs[MAP_EQ_APPEND] >> rveq >>
      fs[project_def] >>
      spose_not_then kall_tac >>
      fs[Once endpointSemTheory.trans_cases] >>
      rveq >>
      rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
     )
  >- ((* Call *)
      pop_assum kall_tac >>
      rw[compile_network_eq_FOLDR,reduction_def,Once trans_FOLDR_NPar_cases] >>
      gs[MAP_EQ_APPEND] >> rveq >>
      fs[project_def] >>
      fs[Once endpointSemTheory.trans_cases])
QED

Theorem compile_network_reflection_lemma':
  ∀s c pn p2.
    compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_undefined_vars (s,c)
    ∧ no_self_comunication c
    ∧ dvarsOf c = []
    ∧ reduction (compile_network s c pn) p2
    ==> ∃s' c'.
             reduction^* p2 (compile_network s' c' pn)
             ∧ trans_s (s,c) (s',c')
             ∧ compile_network_ok s' c' pn
Proof
  rpt strip_tac >>
  drule_all compile_network_reflection_lemma >>
  strip_tac >>
  dxrule_then assume_tac qcong_sym >>
  drule empty_queue_qcong >>
  impl_tac
  >- (fs[compile_network_project] >>
      rename1 ‘MAP _ l’ >>
      rpt(pop_assum kall_tac) >>
      Induct_on ‘l’ >> fs[empty_q_def]) >>
  metis_tac[]
QED

Theorem trans_Send_compile_network_Nil:
  !ps s'' alpha p1 p2 d p3.
  trans (compile_network s'' Nil ps) (LSend p2 d p3) p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem trans_IntChoice_compile_network_Nil:
  !ps s'' alpha p1 p2 b p3.
  trans (compile_network s'' Nil ps) (LIntChoice p2 b p3) p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem trans_compile_network_Nil:
  !ps s'' alpha p1.
  trans (compile_network s'' Nil ps) LTau p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  imp_res_tac trans_Send_compile_network_Nil >> imp_res_tac trans_IntChoice_compile_network_Nil >> fs[] >>
  qpat_x_assum ` trans (NEndpoint _ _ _) _ _` (strip_assume_tac o ONCE_REWRITE_RULE[endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem reduction_compile_network_Nil:
  !s'' ps p1.
  reduction^* (compile_network s'' Nil ps) p1 ==> p1 = compile_network s'' Nil ps
Proof
  rw[Once RTC_cases,reduction_def] >>
  imp_res_tac trans_compile_network_Nil
QED

(* TODO: move to endpointProps *)
Theorem qcong_list_trans_pres:
  ∀p1 q1 alpha p2.
    qcong p1 q1 ∧ list_trans p1 alpha p2 ⇒
    ∃q2. list_trans q1 alpha q2 ∧ qcong p2 q2
Proof
  Induct_on ‘alpha’ >> rw[list_trans_def] >> simp[] >>
  drule_all_then strip_assume_tac qcong_trans_pres >>
  metis_tac[]
QED

(* TODO: move to chorProps *)
Theorem no_undefined_vars_trans_s_pres:
  ∀sc alpha sc'.
    no_undefined_vars sc ∧ trans_s sc sc' ⇒ no_undefined_vars sc'
Proof
  simp[trans_s_def,CONJ_SYM] >>
  ho_match_mp_tac RTC_lifts_invariants >>
  metis_tac[no_undefined_vars_trans_pres]
QED

Theorem no_self_comunication_trans_s_pres:
  ∀c s c s' c'.
  no_self_comunication c ∧ trans_s (s,c) (s',c') ⇒
  no_self_comunication c'
Proof
  ‘∀sc alpha sc'.
    (no_self_comunication o SND) sc ∧ trans_s sc sc' ⇒ (no_self_comunication o SND) sc'’
    by(simp[trans_s_def,CONJ_SYM] >>
       ho_match_mp_tac RTC_lifts_invariants >>
       rpt Cases >> rw[] >>
       rename1 ‘trans _ α’ >> Cases_on ‘α’ >> imp_res_tac no_self_comunication_trans_pres) >>
  metis_tac[o_DEF,SND]
QED

(* TODO: move to chorProps *)
Theorem procsOf_trans_SUBSET:
  ∀sc α sc'.
  trans sc α sc' ⇒ set(procsOf(SND sc')) ⊆ set(procsOf(SND sc))
Proof
  ho_match_mp_tac trans_ind >>
  rw[procsOf_def,set_nub',SUBSET_DEF] >> res_tac >> gs[] >>
  metis_tac[procsOf_dsubst_MEM_eq]
QED

Theorem procsOf_trans_s_SUBSET:
  ∀sc sc'.
    trans_s sc sc' ⇒ set(procsOf(SND sc')) ⊆ set(procsOf(SND sc))
Proof
  simp[trans_s_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >>
  imp_res_tac procsOf_trans_SUBSET >>
  metis_tac[SUBSET_TRANS]
QED

Theorem compile_network_reflection:
   ∀s c pn p2.
    reduction^* (compile_network s c pn) p2
    ∧ compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_self_comunication c
    ∧ no_undefined_vars (s,c)
    ∧ dvarsOf c = []
    ==> ∃s'' c'' p3.
              reduction^* p2 p3
              ∧ trans_s (s,c) (s'',c'')
              ∧ qcong p3 (compile_network s'' c'' pn)
              ∧ compile_network_ok s'' c'' pn
Proof
  simp[reduction_list_trans_eq,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases
  >- (rw[list_trans_def] >>
      CONV_TAC(RESORT_EXISTS_CONV rev) >>
      qexists_tac `0` >> rw[list_trans_def] >>
      metis_tac[trans_s_def,RTC_REFL,qcong_refl])
  >- (rw[list_trans_def,GSYM reduction_def] >>
      drule(compile_network_reflection_lemma'
            |> REWRITE_RULE[PULL_EXISTS,reduction_list_trans_eq]) >>
      rpt(disch_then drule) >>
      strip_tac >>
      rveq >>
      dxrule endpoint_confluence_weak_contract >>
      disch_then dxrule >>
      impl_tac
      >- (fs[reduction_def] >>
          drule endpoint_names_trans >>
          simp[FST_endpoints_compile_network]) >>
      strip_tac >>
      rename1 `list_trans (compile_network _ _ _) (REPLICATE stepcount _) _` >>
      first_x_assum(qspec_then `stepcount` mp_tac ) >>
      impl_tac >- simp[] >>
      disch_then drule >>
      impl_tac
      >- (imp_res_tac no_undefined_vars_trans_s_pres >>
          imp_res_tac no_self_comunication_trans_s_pres >>
          simp[] >>
          imp_res_tac procsOf_trans_s_SUBSET >>
          metis_tac[SND,SUBSET_TRANS,dvarsOf_nil_trans_s]) >>
      strip_tac >>
      drule_all qcong_list_trans_pres >>
      strip_tac >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      Q.REFINE_EXISTS_TAC ‘_ + _’ >>
      simp[GSYM REPLICATE_APPEND,list_trans_append,PULL_EXISTS] >>
      ntac 2 (goal_assum drule) >>
      irule_at Any trans_s_trans_s >>
      rpt(goal_assum drule) >>
      metis_tac[qcong_trans,qcong_sym])
QED

Theorem compile_network_reflection':
   ∀s c pn p2.
    reduction^* (compile_network s c pn) p2
    ∧ compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_self_comunication c
    ∧ no_undefined_vars (s,c)
    ∧ dvarsOf c = []
    ==> ∃s'' c''.
              reduction^* p2 (compile_network s'' c'' pn)
              ∧ trans_s (s,c) (s'',c'')
              ∧ compile_network_ok s'' c'' pn
Proof
  rpt strip_tac >>
  drule_all compile_network_reflection >>
  strip_tac >>
  dxrule_then assume_tac qcong_sym >>
  drule empty_queue_qcong >>
  impl_tac
  >- (fs[compile_network_project] >>
      rename1 ‘MAP _ l’ >>
      rpt(pop_assum kall_tac) >>
      Induct_on ‘l’ >> fs[empty_q_def]) >>
  metis_tac[]
QED

Theorem compile_network_reflection_procs:
   ∀s c pn p2.
    reduction^* (compile_network s c (procsOf c)) p2
    ∧ compile_network_ok s c (procsOf c)
    ∧ no_undefined_vars (s,c)
    ∧ dvarsOf c = []
    ==> ∃s'' c''.
              reduction^* p2 (compile_network s'' c'' (procsOf c))
              ∧ trans_s (s,c) (s'',c'')
Proof
  rpt strip_tac >>
  drule compile_network_reflection' >>
  disch_then match_mp_tac >>
  simp[procsOf_all_distinct] >>
  imp_res_tac compile_network_ok_no_self_comunication
QED

Theorem trans_s_nil:
  trans_s (s,Nil) sc ==> sc = (s,Nil)
Proof
  rw[trans_s_def,Once RTC_cases] >>
  fs[Once trans_cases]
QED

Theorem compile_network_preservation:
   ∀s c s'' c''.
    compile_network_ok s c (procsOf c)
    ∧ dvarsOf c = []
    ∧ trans_s (s,c) (s'',c'')
    ∧ no_undefined_vars (s,c)
    ==> ∃s''' c''' p2.
              reduction^* (compile_network s c (procsOf c)) p2
              ∧ trans_s (s'',c'') (s''',c''')
              /\ p2 = (compile_network s''' c''' (procsOf c))
Proof
  rw []
  \\ imp_res_tac compile_network_ok_no_self_comunication
  \\ drule_all trans_s_ln
  \\ rw []
  \\ drule_all compile_network_preservation_trans_ln
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ irule trans_s_trans_s
  \\ IMP_RES_TAC trans_ln_IMP_trans_s
  \\ asm_exists_tac \\ fs []
QED

Theorem proj_has_reduction:
   ∀s c s'' c''.
    compile_network_ok s c (procsOf c)
    ∧ dvarsOf c = []
    ∧ no_undefined_vars (s,c)
    ==> (∃p2.
          reduction (compile_network s c (procsOf c)) p2) ∨
          net_end(compile_network s c (procsOf c))
Proof
  Cases_on ‘c’
  >- (* Nil *) rw[compile_network_gen_def,procsOf_def,net_end_def]
  >- (rw[procsOf_def,compile_network_gen_def,nub'_def,reduction_def,project_def] >>
      disj1_tac >>
      irule_at (Pos hd) trans_par_l >>
      gvs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
      Cases_on ‘v = [1w]’
      >- (irule_at (Pos hd) endpointSemTheory.trans_if_true >>
          rw[lookup_projectS]) >>
      irule_at (Pos hd) endpointSemTheory.trans_if_false >>
      rw[] >>
      irule_at (Pos hd) lookup_projectS >>
      simp[])
  >- (rw[procsOf_def,compile_network_gen_def,nub'_def,reduction_def,project_def] >>
      disj1_tac >>
      irule_at (Pos hd) trans_com_l >>
      irule_at Any trans_send >>
      gvs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
      irule_at (Pos hd) lookup_projectS >>
      simp[] >>
      irule_at (Pos hd) trans_par_l >>
      irule_at (Pos hd) trans_enqueue >>
      simp[])
  >- (rw[procsOf_def,compile_network_gen_def,nub'_def,reduction_def,project_def] >>
      disj1_tac >>
      irule_at (Pos hd) trans_par_l >>
      irule_at (Pos hd) endpointSemTheory.trans_let >>
      gvs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP,EVERY_MEM,SUBSET_DEF,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS] >>
      rw[] >>
      irule_at (Pos hd) lookup_projectS >>
      metis_tac[])
  >- (rw[procsOf_def,compile_network_gen_def,nub'_def,reduction_def,project_def] >>
      disj1_tac >>
      irule_at (Pos hd) trans_com_choice_l >>
      irule_at Any trans_int_choice >>
      irule_at Any trans_par_l >>
      Cases_on ‘b’ >> rw[]
      >- (irule_at Any trans_enqueue_choice_l >> rw [])
      >- (irule_at Any trans_enqueue_choice_r >> rw []))
  >- (rw[] >>
      rename1 ‘compile_network _ _ l’ >>
      Induct_on ‘l’ >> rw[compile_network_gen_def,net_end_def] >>
      gvs[project_def] >>
      rw[]
      >- (disj1_tac >>
          simp[reduction_def] >>
          irule_at Any trans_par_l >>
          irule_at Any endpointSemTheory.trans_fix)
      >- (gvs[] >>
          disj1_tac >>
          gvs[reduction_def] >>
          irule_at Any trans_par_r >>
          goal_assum drule)
      >- (gvs[] >>
          disj1_tac >>
          gvs[reduction_def] >>
          irule_at Any trans_par_l >>
          irule_at Any endpointSemTheory.trans_fix)
      >- (gvs[net_end_def]))
  >- (gvs[dvarsOf_def])
QED

Theorem proj_has_reduction':
   ∀s c s'' c''.
    compile_network_ok s c ps
    ∧ dvarsOf c = []
    ∧ no_undefined_vars (s,c)
    ∧ set(procsOf c) ⊆ set ps
    ∧ ALL_DISTINCT ps
    ==> (∃p2.
          reduction (compile_network s c ps) p2) ∨
          net_end(compile_network s c ps)
Proof
  rpt strip_tac >>
  ‘∀l. ALL_DISTINCT(l ++ procsOf c) ∧
       compile_network_ok s c (procsOf c) ⇒
       (∃p2. reduction (compile_network s c (l ++ procsOf c)) p2) ∨
        net_end (compile_network s c (l ++ procsOf c))’
    by(Induct_on ‘l’ >>
       rw[]
       >- (drule_all proj_has_reduction >>
           metis_tac[]) >>
       gvs[compile_network_gen_def] >>
       simp[project_nonmember_nil,net_end_def] >>
       metis_tac[reduction_def,trans_par_r]) >>
  qspecl_then [‘λp. MEM p (procsOf c)’,‘ps’] assume_tac PERM_SPLIT >>
  ‘PERM (FILTER (λp. MEM p (procsOf c)) ps) (procsOf c)’
    by(match_mp_tac PERM_ALL_DISTINCT >>
       rw[ALL_DISTINCT_FILTER,MEM_FILTER,FILTER_FILTER,EQ_IMP_THM] >>
       fs[SUBSET_DEF] >> res_tac >> fs[] >-
         (pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
          fs[FILTER_EQ_NIL,EVERY_MEM]) >>
       ‘ALL_DISTINCT (procsOf c)’ by(simp[procsOf_all_distinct]) >>
       qpat_x_assum ‘MEM _ (procsOf _)’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
       fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
       fs[FILTER_EQ_NIL,EVERY_MEM]) >>
  drule PERM_CONG >>
  disch_then(qspecl_then [‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’,‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’] mp_tac) >>
  simp[PERM_REFL] >>
  strip_tac >>
  dxrule_all PERM_TRANS >>
  pop_assum kall_tac >>
  strip_tac >>
  fs[Once PERM_SYM] >>
  qmatch_asmsub_abbrev_tac ‘PERM (_ ++ a1)’ >>
  first_x_assum(qspec_then ‘a1’ mp_tac) >>
  impl_tac >-
   (conj_tac
    >- (imp_res_tac ALL_DISTINCT_PERM >>
        gvs[ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
    match_mp_tac compile_network_ok_subset >>
    metis_tac[]) >>
  strip_tac
  >- (drule_at (Pos last) PERM_TRANS >>
      disch_then(qspec_then ‘a1 ++ procsOf c’ mp_tac) >>
      simp[PERM_APPEND] >>
      strip_tac >>
      drule PERM_rcong_chor_compile_network >>
      disch_then(qspecl_then [‘s’,‘c’] mp_tac) >>
      strip_tac >>          
      dxrule epn_rcong_imp_trans >>
      rw[FORALL_AND_THM] >>
      gvs[reduction_def] >>
      metis_tac[]) >>
  cheat
QED

val _ = export_theory ()

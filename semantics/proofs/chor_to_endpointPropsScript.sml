open preamble choreoUtilsTheory chorLangTheory
     chorLangPropsTheory chor_to_endpointTheory
     endpointLangTheory;

val _ = new_theory "chor_to_endpointProps";

val _ = set_grammar_ancestry
  ["endpointLang","chor_to_endpoint","chorLangProps","chorLang"];


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
  TRY (first_x_assum (qspec_then ‘dvars’ assume_tac) >> gs [OPTREL_refl] >> NO_TAC) >>
  gs[DISJ_IMP_THM,FORALL_AND_THM] >>
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
  fs[ALOOKUP_NONE,MEM_nub']
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
  fs[ALOOKUP_NONE,MEM_nub']
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

Theorem compile_network_ok_subset:
  ∀s c ps qs.
  compile_network_ok s c qs ∧ set ps ⊆ set qs ⇒
  compile_network_ok s c ps
Proof
  Induct_on ‘ps’ >>
  rw[compile_network_gen_def] >- imp_res_tac compile_network_ok_project_ok >>
  res_tac
QED

Definition cut_sel_upto_def:
  cut_sel_upto p (Sel p1 b p2 c) =
    (if p = p1 then
       cut_sel_upto p c
     else
       Sel p1 b p2 c)
  ∧ cut_sel_upto p c = c
End

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

Theorem compile_network_eq_all_project:
   ∀c c' s l. compile_network_ok s c l
    ∧ (∀p. MEM p l ⇒ project' p [] c = project' p [] c')
    ⇒ compile_network s c l = compile_network s c' l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
QED

Theorem project_if_l_eq:
   ∀v p q dvars c1 c2.
    project_ok q dvars (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c1 ≠ Sel p b t c')
    ⇒ project' q dvars (IfThen v p c1 c2) = project' q dvars c1
Proof
  Cases_on `c1`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []
QED

Theorem project_if_r_eq:
   ∀v p dvars q c1 c2.
    project_ok q dvars (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c2 ≠ Sel p b t c')
    ⇒ project' q dvars (IfThen v p c1 c2) = project' q dvars c2
Proof
  Cases_on `c2`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []
QED

Theorem compile_network_if_l_eq:
   ∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b q c'. c1 ≠ Sel p b q c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c1 l
Proof
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_l_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
QED

Theorem compile_network_if_l:
  ∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c1 l
Proof
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]
QED

Theorem compile_network_if_r:
  ∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c2 l
Proof
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]
QED

Theorem compile_network_if_r_eq:
   ∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b p2 c'. c2 ≠ Sel p b p2 c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c2 l
Proof
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_r_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
QED

val _ = export_theory ()

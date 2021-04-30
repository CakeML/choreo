open preamble choreoUtilsTheory chorPropsTheory
     projectionTheory payloadPropsTheory
     endpointPropsTheory

open endpointCongTheory
open payloadCongTheory

open chorSemTheory endpointLangTheory

open chor_to_endpointTheory
     endpoint_to_choiceTheory
     endpoint_to_payloadTheory
     payload_closureTheory
open chor_to_endpointProofTheory
     endpoint_to_choiceProofTheory
     endpoint_to_payloadProofTheory
     payload_closureProofTheory
open bisimulationTheory
open payload_bisimTheory

val _ = new_theory "projectionProof";

Triviality to_choice_preservation =
  endpoint_to_choiceProofTheory.compile_network_preservation;

Triviality to_endpoint_preservation =
  chor_to_endpointProofTheory.compile_network_preservation;

Triviality to_payload_preservation =
  endpoint_to_payloadProofTheory.compile_network_preservation;

Triviality to_closure_preservation =
  payload_closureProofTheory.compile_network_preservation_alt;

Theorem endpoints_compile_network_chor:
  ∀s c l. MAP FST (endpointProps$endpoints (compile_network s (c : chor) l)) = l
Proof
  rw [] \\ Induct_on ‘l’
  \\ rw [endpoints_def,compile_network_gen_def]
QED

(* gen_fresh_name generates a fresh name that is not in the initial list *)
Theorem gen_fresh_name_same:
  ∀l. ¬MEM (gen_fresh_name l) l
Proof
  Cases >- fs[gen_fresh_name_def] >>
  rename1 `s::l` >>
  simp[] >>
  `STRLEN s < STRLEN(gen_fresh_name (s::l))`
    by(simp[gen_fresh_name_def] >>
       qid_spec_tac `s` >>
       Induct_on `l` >> rw[] >>
       first_x_assum(qspec_then `h` mp_tac) >> intLib.COOPER_TAC) >>
  conj_tac >- (spose_not_then strip_assume_tac >> fs[]) >>
  pop_assum kall_tac >>
  `!s'. MEM s' l ==> STRLEN s' < STRLEN(gen_fresh_name (s::l))`
    by(simp[gen_fresh_name_def] >>
       qid_spec_tac `s` >>
       qid_spec_tac `l` >>
       ho_match_mp_tac SNOC_INDUCT >>
       rw[FOLDL_SNOC] >> rw[] >>
       res_tac >>
       first_x_assum(qspec_then `s` mp_tac) >> intLib.COOPER_TAC) >>
  spose_not_then strip_assume_tac >> res_tac >>
  fs[]
QED

Theorem gen_fresh_nameE:
  ∀l. set l' ⊆ set l ⇒ ¬MEM (gen_fresh_name l) l'
Proof
  metis_tac[SUBSET_DEF,gen_fresh_name_same]
QED

(* endpoint_to_choice compilation step generates a choice_free_network *)
Theorem choice_free_network_compile_network_fv:
  ∀epn fv. choice_free_network (compile_network_fv fv epn)
Proof
  Induct \\ rw [choice_free_network_def,compile_network_fv_def]
  \\ Induct_on ‘e’ \\ rw [choice_free_endpoint_def,
                          endpoint_to_choiceTheory.compile_endpoint_def]
QED

Theorem junkcong_swap_endpoint:
  ∀fvs n1 n2.
    junkcong fvs n1 n2 ⇒
    ∀fv l s e1 s'.
      fvs = {fv} ∧ ~MEM fv (free_var_names_endpoint e1) ∧
      n1 = NEndpoint l s (endpoint_to_choice$compile_endpoint fv e1) ∧
      n2 = NEndpoint l s' (endpoint_to_choice$compile_endpoint fv e1) ⇒
     junkcong {fv} (NEndpoint l s e1) (NEndpoint l s' e1)
Proof
  ho_match_mp_tac junkcong_strongind >> rw[]
  >- metis_tac[junkcong_refl]
  >- metis_tac[junkcong_sym]
  >- (imp_res_tac junkcong_endpoint_rel_endpoint >> rveq >> metis_tac[junkcong_trans])
  >- (match_mp_tac junkcong_add_junk >> rfs[])
QED

Theorem junkcong_fv:
  ∀fvs n1 n2.
    endpointProps$junkcong fvs n1 n2 ⇒
    ∀fv l s e1 s'.
      fvs = {fv} ∧ MEM fv (free_var_names_endpoint e1) ∧
      n1 = NEndpoint l s e1 ∧
      n2 = NEndpoint l s' e1 ⇒
     s = s'
Proof
  ho_match_mp_tac junkcong_strongind >> rw[]
  >- (imp_res_tac junkcong_endpoint_rel_endpoint >> rveq >>
      metis_tac[junkcong_free_var_names])
  >- rfs[]
QED

Theorem free_var_names_var_names:
  MEM fv (endpointLang$free_var_names_endpoint e) ⇒ MEM fv (var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[endpointLangTheory.var_names_endpoint_def,endpointLangTheory.free_var_names_endpoint_def,MEM_FILTER] >>
  res_tac >> fs[]
QED

Theorem payload_free_var_names_var_names:
  MEM fv (payloadLang$free_var_names_endpoint e) ⇒ MEM fv (var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[payloadLangTheory.var_names_endpoint_def,payloadLangTheory.free_var_names_endpoint_def,MEM_FILTER] >>
  res_tac >> fs[]
QED

Theorem payload_free_var_names_var_names_network:
  MEM fv (payloadLang$free_var_names_network n) ⇒ MEM fv (payloadLang$var_names_network n)
Proof
  Induct_on ‘n’ >> rw[payloadLangTheory.var_names_endpoint_def,payloadLangTheory.free_var_names_endpoint_def,payloadLangTheory.var_names_network_def,payloadLangTheory.free_var_names_network_def,MEM_FILTER] >>
  res_tac >> fs[payload_free_var_names_var_names]
QED

Theorem free_var_names_var_names_network:
  MEM fv (endpointLang$free_var_names_network n) ⇒ MEM fv (endpointLang$var_names_network n)
Proof
  Induct_on ‘n’ >> rw[endpointLangTheory.var_names_endpoint_def,endpointLangTheory.free_var_names_endpoint_def,endpointLangTheory.var_names_network_def,endpointLangTheory.free_var_names_network_def,MEM_FILTER] >>
  res_tac >> fs[free_var_names_var_names]
QED

Theorem var_names_compile_to_payload:
  choice_free_endpoint n ⇒
  var_names_endpoint(endpoint_to_payload$compile_endpoint n) = var_names_endpoint n
Proof
  Induct_on ‘n’ >> rw[payloadLangTheory.var_names_endpoint_def,endpointLangTheory.var_names_endpoint_def,endpoint_to_payloadTheory.compile_endpoint_def,MEM_FILTER,choice_free_endpoint_def]
QED

Theorem var_names_compile_to_payload_network:
  choice_free_network n ⇒
  var_names_network(compile_network conf n) = var_names_network n
Proof
  Induct_on ‘n’ >> rw[payloadLangTheory.var_names_endpoint_def,payloadLangTheory.free_var_names_endpoint_def,payloadLangTheory.var_names_network_def,payloadLangTheory.free_var_names_network_def,MEM_FILTER,endpoint_to_payloadTheory.compile_network_def,choice_free_network_def,endpointLangTheory.var_names_network_def] >>
  res_tac >> fs[var_names_compile_to_payload]
QED

Theorem free_var_names_compile_to_payload:
  choice_free_endpoint n ⇒
  free_var_names_endpoint(endpoint_to_payload$compile_endpoint n) = free_var_names_endpoint n
Proof
  Induct_on ‘n’ >> rw[payloadLangTheory.free_var_names_endpoint_def,endpointLangTheory.free_var_names_endpoint_def,endpoint_to_payloadTheory.compile_endpoint_def,MEM_FILTER,choice_free_endpoint_def]
QED

Theorem free_var_names_compile_to_payload_network:
  choice_free_network n ⇒
  free_var_names_network(compile_network conf n) = free_var_names_network n
Proof
  Induct_on ‘n’ >> rw[payloadLangTheory.free_var_names_endpoint_def,payloadLangTheory.free_var_names_endpoint_def,payloadLangTheory.free_var_names_network_def,payloadLangTheory.free_var_names_network_def,MEM_FILTER,endpoint_to_payloadTheory.compile_network_def,choice_free_network_def,endpointLangTheory.free_var_names_network_def] >>
  res_tac >> fs[free_var_names_compile_to_payload]
QED

Theorem junkcong_compile_network_fv:
  ∀fv e1 e2.
  junkcong {fv}
    (compile_network_fv fv e1)
    e2 ∧ ~MEM fv (var_names_network e1) ⇒
  ∃e2'.
    junkcong {fv} (e1) e2' ∧
    e2 = compile_network_fv fv e2'
Proof
  Induct_on ‘e1’ >> rw[compile_network_fv_def,var_names_network_def]
  >- (imp_res_tac junkcong_nil_rel_nil >> rveq >> goal_assum drule >> rw[compile_network_fv_def])
  >- (imp_res_tac junkcong_par_rel_par >> rveq >> res_tac >> rveq >>
      metis_tac[junkcong_par,compile_network_fv_def])
  >- (imp_res_tac junkcong_endpoint_rel_endpoint >> rveq >>
      qexists_tac ‘NEndpoint s s2 e’ >>
      rw[compile_network_fv_def] >>
      drule_then match_mp_tac junkcong_swap_endpoint >> rw[] >>
      metis_tac[free_var_names_var_names])
QED

Theorem fix_network_compile_network:
  ∀epn conf. fix_network (compile_network conf epn)
Proof
  Induct \\ rw [endpoint_to_payloadTheory.compile_network_def,fix_network_def,payloadLangTheory.endpoints_def]
  \\ fs [fix_network_def,endpoint_to_payloadTheory.compile_state_def]
  \\ Induct_on ‘e’ \\ rw [endpoint_to_payloadTheory.compile_endpoint_def,fix_endpoint_def]
QED

Theorem split_sel_dvarsOf:
  ∀c r h p b.
    split_sel h p c = SOME (b,r)
    ⇒ dvarsOf r = dvarsOf c
Proof
  Induct \\ rw [split_sel_def,dvarsOf_def,nub'_dvarsOf]
  \\ metis_tac []
QED

Triviality dvarsOf_imp_free_fix_names_endpoint_aux:
  ∀h l c x.
    MEM x (free_fix_names_endpoint
           (compile_endpoint (compile_endpoint fv (project' h l c))))
    ⇒ MEM x (dvarsOf c)
Proof
  ho_match_mp_tac project_ind \\ rw [] \\ pop_assum mp_tac
  \\ EVAL_TAC \\ gs [dvarsOf_def,nub'_nil,nub'_dvarsOf,procsOf_def,MEM_nub']
  \\ EVERY_CASE_TAC \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub']
  \\ EVAL_TAC \\ simp []
  \\ TRY (rw [] \\ metis_tac [split_sel_dvarsOf] \\ NO_TAC)
  \\ rw [MEM_FILTER]
QED

Theorem dvarsOf_imp_free_fix_names_endpoint:
  ∀h l c x.
    dvarsOf c = []
    ⇒ free_fix_names_endpoint
        (compile_endpoint (compile_endpoint fv (project' h l c))) = []
Proof
  rw []
  \\ qspecl_then [‘h’,‘l’,‘c’] assume_tac dvarsOf_imp_free_fix_names_endpoint_aux
  \\ gs [] \\ qmatch_goalsub_abbrev_tac ‘ ll = []’
  \\ pop_assum kall_tac
  \\ CCONTR_TAC \\ Cases_on ‘ll’
  \\ gs [] \\ metis_tac []
QED

Theorem dvarsOf_imp_free_fix_names_network:
  ∀c s conf fv l.
    dvarsOf c = []
    ⇒ free_fix_names_network
        (endpoint_to_payload$compile_network conf
           (compile_network_fv fv
              (compile_network s c l))) = []
Proof
  rw []
  \\ induct_on ‘l’ \\ EVAL_TAC \\ rw [] \\ gs []
  \\ simp [dvarsOf_imp_free_fix_names_endpoint]
QED

Triviality DELETE_eq_INTER:
∀s x.  (s DELETE x) = ({y | x ≠ y} ∩ s)
Proof
  rw [FUN_EQ_THM] \\ metis_tac []
QED

Theorem split_sel_free_variables:
  split_sel p1 p2 c = SOME(b,c') ⇒
  free_variables c' = free_variables c
Proof
  Induct_on ‘c’ >> rw[split_sel_def,free_variables_def]
QED

Theorem no_undefined_vars_chor_to_network:
  ∀s c conf fv l.
    no_undefined_vars (s,c)
    ⇒ no_undefined_vars_network
        (endpoint_to_payload$compile_network conf
             (compile_network_fv fv
                (compile_network s c l)))
Proof
  rw []
  \\ induct_on ‘l’ \\ EVAL_TAC \\ rw [] \\ gs []
  >- (pop_assum kall_tac \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac ‘project' h l c’
      (* \\ ‘l = []’ by simp [Abbr‘l’] *)
      (* \\ pop_assum mp_tac *) \\ pop_assum kall_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘h’,‘l’,‘c’,‘s’])
      \\ ho_match_mp_tac project_ind
      \\ rw []
      >- (pop_assum mp_tac \\ EVAL_TAC \\ simp [])
      >- (EVAL_TAC \\ gs []
          \\ EVERY_CASE_TAC
          \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub',no_undefined_vars_def,free_variables_def]
          \\ EVAL_TAC \\ gs []
          >- (gs [DELETE_SUBSET_INSERT]
              \\ first_x_assum (qspec_then ‘s |+ ((c,p2),ARB)’ assume_tac)
              \\ gs [FDOM_FLOOKUP]
              \\ dxrule_then (qspec_then ‘c’ assume_tac) SUBSET_DELETE_BOTH
              \\ simp [LIST_TO_SET_FILTER]
              \\ ho_match_mp_tac SUBSET_TRANS
              \\ qmatch_asmsub_abbrev_tac ‘_ ⊆ tt’
              \\ gs [DELETE_eq_INTER]
              \\ first_x_assum (irule_at Any)
              \\ UNABBREV_ALL_TAC
              \\ simp [MAP_KEYS_def]
              \\ qmatch_goalsub_abbrev_tac ‘_ INSERT tt’
              \\ rw [SUBSET_DEF])
          \\ gs [DELETE_SUBSET_INSERT]
          \\ first_x_assum (qspec_then ‘s |+ ((c,p2),ARB)’ assume_tac)
          \\ gs [MAP_KEYS_def]
          \\ simp [FDOM_DRESTRICT]
          \\ first_x_assum (irule_at Any)
          \\ simp [])
      >- (EVAL_TAC \\ gs []
          \\ EVERY_CASE_TAC
          \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub',no_undefined_vars_def,free_variables_def]
          \\ EVAL_TAC \\ gs []
          >- (gs [DELETE_SUBSET_INSERT]
              \\ first_x_assum (qspec_then ‘s |+ ((h',p1),ARB)’ assume_tac)
              \\ conj_tac
              >- (gs [MAP_KEYS_def,SUBSET_DEF]
                  \\ simp [FDOM_DRESTRICT]
                  \\ rw [] \\ gs [MEM_MAP]
                  \\ qexists_tac ‘(x,h)’ \\ simp [])
              \\ gs []
              \\ dxrule_then (qspec_then ‘h'’ assume_tac) SUBSET_DELETE_BOTH
              \\ simp [LIST_TO_SET_FILTER]
              \\ ho_match_mp_tac SUBSET_TRANS
              \\ qmatch_asmsub_abbrev_tac ‘_ ⊆ tt’
              \\ gs [DELETE_eq_INTER]
              \\ first_x_assum (irule_at Any)
              \\ UNABBREV_ALL_TAC
              \\ simp [MAP_KEYS_def]
              \\ qmatch_goalsub_abbrev_tac ‘_ INSERT tt’
              \\ rw [SUBSET_DEF])
          \\ gs [DELETE_SUBSET_INSERT]
          \\ first_x_assum (qspec_then ‘s |+ ((h',p1),ARB)’ assume_tac)
          \\ gs [])
      >- (EVAL_TAC \\ gs []
          \\ EVERY_CASE_TAC
          \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub',no_undefined_vars_def,free_variables_def]
          \\ EVAL_TAC \\ gs []
          \\ TRY (gs [MAP_KEYS_def,SUBSET_DEF]
                  \\ simp [FDOM_DRESTRICT]
                  \\ rw [] \\ gs [MEM_MAP]
                  \\ qexists_tac ‘(h',h)’ \\ simp [] \\ NO_TAC)
          \\ rw [LIST_TO_SET_APPEND,FILTER_APPEND,LIST_TO_SET_FILTER]
          \\ irule SUBSET_TRANS \\ irule_at Any (CONJUNCT2 INTER_SUBSET)
          \\ rw [] \\ first_x_assum irule
          \\ IMP_RES_TAC split_sel_free_variables
          \\ rw [])
      >- (EVAL_TAC \\ gs []
          \\ EVERY_CASE_TAC
          \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub',no_undefined_vars_def,free_variables_def]
          \\ EVAL_TAC \\ gs []
          \\ first_x_assum drule
          \\ rw [LIST_TO_SET_FILTER]
          \\ irule SUBSET_TRANS \\ irule_at Any (CONJUNCT2 INTER_SUBSET)
          \\ simp [])
      \\ EVAL_TAC \\ gs []
      \\ EVERY_CASE_TAC
      \\ gs [nub'_dvarsOf,project_def,procsOf_def,MEM_nub',no_undefined_vars_def,free_variables_def]
      \\ EVAL_TAC \\ gs [])
  \\ gs [no_undefined_vars_network_def]
  \\ pop_assum mp_tac
  \\ EVAL_TAC \\ simp []
QED

Theorem projection_preservation_junkcong:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
   ∧ dvarsOf c = []
   ⇒ ∃s''' c''' epn0 epn.
      trans_s (s'',c'') (s''',c''') ∧
      junkcong {new_fv s c}
               (project_choice (new_fv s c) s''' c''' (procsOf c))
               epn0 ∧
      compile_rel conf epn (compile_network_alt (compile_network conf epn0)) ∧
      (reduction conf)^* (projection conf s c (procsOf c)) epn
Proof
  rw []
  \\ drule to_endpoint_preservation
  \\ rpt (disch_then drule)
  \\ strip_tac \\ rveq \\ fs []
  \\ asm_exists_tac \\ rw []
  \\ first_x_assum (mp_then Any mp_tac to_choice_preservation)
  \\ qmatch_goalsub_abbrev_tac ‘endpoints to_epn’
  \\ qmatch_goalsub_abbrev_tac ‘junkcong {fv}’
  \\ disch_then (qspec_then ‘fv’ mp_tac)
  \\ impl_tac \\ rw []
  >- rw [Abbr‘to_epn’,endpoints_compile_network_chor,procsOf_all_distinct]
  >- rw [Abbr‘fv’,gen_fresh_name_same]
  \\ fs [projection_def,endpoint_to_choiceTheory.compile_network_def]
  \\ drule_then assume_tac junkcong_sym \\  asm_exists_tac
  \\ fs [projection_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_asmsub_abbrev_tac ‘reduction^* to_choice n3’
  \\ drule to_payload_preservation
  \\ disch_then drule
  \\ impl_tac
  >- rw [Abbr‘to_choice’,choice_free_network_compile_network_fv]
  \\ strip_tac
  \\ drule to_closure_preservation
  \\ impl_tac
  >- (simp [fix_network_compile_network]
      \\ UNABBREV_ALL_TAC
      \\ simp [dvarsOf_imp_free_fix_names_network,no_undefined_vars_chor_to_network])
  \\ rw [] \\ asm_exists_tac \\ simp []
QED

Theorem projection_top_preservation_junkcong:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
   ∧ dvarsOf c = []
   ⇒ ∃s''' c''' epn0 epn.
      trans_s (s'',c'') (s''',c''') ∧
      junkcong {new_fv s c}
               (project_choice (new_fv s c) s''' c''' (procsOf c))
               epn0 ∧
      compile_rel conf epn (compile_network_alt (compile_network conf epn0)) ∧
      (reduction conf)^* (projection_top conf s c (procsOf c)) epn
Proof
  rpt strip_tac >>
  drule_all projection_preservation_junkcong >>
  strip_tac >>
  rpt(goal_assum drule) >>
  gvs[projection_def,projection_top_def]
  \\ metis_tac[compile_network_reduction_alt,RTC_RTC]
QED

Theorem trans_s_trans:
  trans_s (s,c) (s',c') ∧ trans_s (s',c') (s'',c'') ⇒
  trans_s (s,c) (s'',c'')
Proof
  rw[trans_s_def] >> imp_res_tac RTC_RTC
QED

Theorem split_sel_variables:
  split_sel p1 p2 c = SOME(b,c') ⇒
  variables c' = variables c
Proof
  Induct_on ‘c’ >> rw[split_sel_def,variables_def]
QED

Theorem variables_IN_procsOF:
  x ∈ variables c ⇒ MEM (SND x) (procsOf c)
Proof
  Induct_on ‘c’ >> rw[procsOf_def,variables_def,MEM_nub',MEM_MAP] >> rw[]
QED

Theorem project'_variables_eq:
  ∀proc dvars c.
  project_ok proc dvars c ⇒
  set (var_names_endpoint (project' proc dvars c)) = IMAGE FST (variables c ∩ {(a,v) | a=a ∧ v = proc})
Proof
  ho_match_mp_tac project_ind >> rw[project_def,var_names_endpoint_def,variables_def] >>
  res_tac >> fs[SUBSET_DEF,INTER_DEF,IMAGE_DEF,FUN_EQ_THM,PULL_EXISTS,MEM_MAP] >-
    (metis_tac[IN_DEF]) >-
    (metis_tac[IN_DEF]) >>
  rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
  fs[var_names_endpoint_def] >>
  rw[] >> res_tac >>
  rveq >-
   metis_tac[split_sel_variables,IN_DEF] >-
   metis_tac[split_sel_variables,IN_DEF] >>
  CCONTR_TAC >> gs [] >> dxrule variables_IN_procsOF >>
  strip_tac >> dxrule procsOf_dprocsOf_MEM >>
  gs [] >> metis_tac []
QED

Theorem projection_variables_eq_lemma:
  ∀procs s c.
  compile_network_ok s c procs ⇒
  set (var_names_network (compile_network s c procs)) = IMAGE FST (variables c ∩ {(a,v) | a=a ∧ MEM v procs})
Proof
  Induct_on ‘procs’ >> rw[compile_network_gen_def,var_names_network_def] >>
  res_tac >>
  rw[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
  rfs[project'_variables_eq,PULL_EXISTS] >>
  rveq >> metis_tac[]
QED

Theorem projection_variables_eq:
  ∀s c.
  compile_network_ok s c (procsOf c) ⇒
  set (var_names_network (compile_network s c (procsOf c))) = IMAGE FST (variables c)
Proof
  rpt strip_tac >> drule projection_variables_eq_lemma >>
  disch_then SUBST_ALL_TAC >>
  rw[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
  metis_tac[FST,PAIR,variables_IN_procsOF]
QED

Theorem project'_variables_SUBSET:
  ∀proc dvars c.
  set (var_names_endpoint (project' proc dvars c)) ⊆ IMAGE FST (variables c)
Proof
  ho_match_mp_tac project_ind >> rw[project_def,var_names_endpoint_def,variables_def] >>
  res_tac >> fs[SUBSET_DEF] >-
    (rw[PULL_EXISTS,MEM_MAP]) >>
  rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
  fs[var_names_endpoint_def] >>
  rw[] >> res_tac >>
  rveq >> metis_tac[split_sel_variables]
QED

Theorem project'_free_variables_SUBSET:
  ∀proc dvars c.
  set (free_var_names_endpoint (project' proc dvars c)) ⊆ IMAGE FST (free_variables c ∩ {(a,proc) | a=a})
Proof
  ho_match_mp_tac project_ind >> rw[project_def,free_var_names_endpoint_def,free_variables_def] >>
  res_tac >> fs[SUBSET_DEF] >>
  TRY(rw[PULL_EXISTS,MEM_MAP,MEM_FILTER] >> res_tac >> fs[] >> NO_TAC) >>
  rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
  fs[free_var_names_endpoint_def] >>
  rw[] >> res_tac >>
  rveq >> fs[] >> rveq >> fs[] >> metis_tac[FST,SND,split_sel_free_variables]
QED

Theorem projection_variables_SUBSET:
  ∀s c procs.
  set(var_names_network (compile_network s c procs)) ⊆
  IMAGE FST (variables c)
Proof
  Induct_on ‘procs’ >> rw[compile_network_gen_def,var_names_network_def] >>
  MATCH_ACCEPT_TAC project'_variables_SUBSET
QED

Theorem projection_free_variables_SUBSET:
  ∀s c procs.
  set(free_var_names_network (compile_network s c procs)) ⊆
  IMAGE FST (free_variables c)
Proof
  Induct_on ‘procs’ >> rw[compile_network_gen_def,free_var_names_network_def] >>
  match_mp_tac(MATCH_MP (SUBSET_TRANS |> IMP_CANON |> hd) (SPEC_ALL project'_free_variables_SUBSET)) >> rw[]
QED

Theorem endpoint_to_payload_free_var_names:
  MEM v (free_var_names_endpoint(endpoint_to_payload$compile_endpoint e)) ⇒
  MEM v (free_var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[payloadLangTheory.free_var_names_endpoint_def,endpointLangTheory.free_var_names_endpoint_def,endpoint_to_payloadTheory.compile_endpoint_def] >>
  fs[MEM_FILTER]
QED

Theorem junkcong_compile_to_payload:
  ∀fvs e1 e2 conf.
  endpointProps$junkcong fvs e1 e2 ⇒
  payloadProps$junkcong fvs (compile_network conf e1) (compile_network conf e2)
Proof
  simp[GSYM PULL_FORALL] >>
  ho_match_mp_tac junkcong_ind >> rw[payloadPropsTheory.junkcong_refl]
  >- metis_tac[payloadPropsTheory.junkcong_sym]
  >- metis_tac[payloadPropsTheory.junkcong_trans]
  >- (simp[endpoint_to_payloadTheory.compile_network_def,compile_state_def] >>
      irule payloadPropsTheory.junkcong_add_junk'' >> rw[] >>
      metis_tac[endpoint_to_payload_free_var_names])
  >- (rw[endpoint_to_payloadTheory.compile_network_def] >> metis_tac[payloadPropsTheory.junkcong_par])
QED

Definition perm1_def:
  perm1 v1 v2 v = if v = v1 then v2 else if v = v2 then v1 else v
End

Definition perm_endpoint_def:
  (perm_endpoint v1 v2 (payloadLang$Nil) = Nil)
  ∧ (perm_endpoint v1 v2 (Send p v n e) = Send p (perm1 v1 v2 v) n (perm_endpoint v1 v2 e))
  ∧ (perm_endpoint v1 v2 (Receive p v d e) = Receive p (perm1 v1 v2 v) d (perm_endpoint v1 v2 e))
  ∧ (perm_endpoint v1 v2 (Fix d e) = Fix d (perm_endpoint v1 v2 e))
  ∧ (perm_endpoint v1 v2 (Call d) = Call d)
  ∧ (perm_endpoint v1 v2 (Letrec d vl e) = Letrec d (MAP (perm1 v1 v2) vl) (perm_endpoint v1 v2 e))
  ∧ (perm_endpoint v1 v2 (FCall d vl) = FCall d (MAP (perm1 v1 v2) vl))
  ∧ (perm_endpoint v1 v2 (IfThen v e1 e2) =
        IfThen (perm1 v1 v2 v)
               (perm_endpoint v1 v2 e1)
               (perm_endpoint v1 v2 e2))
  ∧ (perm_endpoint v1 v2 (Let v f vl e) =
       Let (perm1 v1 v2 v)
           f
           (MAP (perm1 v1 v2) vl)
           (perm_endpoint v1 v2 e)
     )
End

Definition perm_bindings_def:
  perm_bindings v1 v2 vs =
  if v1 ∈ FDOM vs ∧ v2 ∈ FDOM vs then
    vs |+ (v1,THE(FLOOKUP vs v2)) |+ (v2,THE(FLOOKUP vs v1))
  else if v1 ∈ FDOM vs then
    DRESTRICT vs (λx. x ≠ v1) |+ (v2,THE(FLOOKUP vs v1))
  else if v2 ∈ FDOM vs then
    DRESTRICT vs (λx. x ≠ v2) |+ (v1,THE(FLOOKUP vs v2))
  else vs
End


Definition perm_closure_def:
  perm_closure v1 v2 (Closure vars (funs,bind) e) =
  Closure (MAP (perm1 v1 v2) vars)
          (* Had to use lambda since (I ##) gives termination errors *)
          (MAP (λ(d,f). (d,perm_closure v1 v2 f)) funs, perm_bindings v1 v2 bind)
          (perm_endpoint v1 v2 e)
Termination
  WF_REL_TAC ‘inv_image $< (closure_size o SND o SND)’ >>
  rw[payloadLangTheory.closure_size_def] >> imp_res_tac ALOOKUP_MEM >>
  imp_res_tac payloadLangTheory.closure_size_MEM >>
  DECIDE_TAC
End

Definition perm_state_def:
  perm_state v1 v2 s  =
    s with <| bindings := perm_bindings v1 v2 s.bindings;
              funs := MAP (I ## perm_closure v1 v2) s.funs |>
End

Definition perm_network_def:
  (perm_network v1 v2 NNil = NNil) ∧
  (perm_network v1 v2 (NPar n1 n2) = NPar (perm_network v1 v2 n1) (perm_network v1 v2 n2)) ∧
  (perm_network v1 v2 (NEndpoint p s e) =
   NEndpoint p (perm_state v1 v2 s) (perm_endpoint v1 v2 e)
  )
End

Theorem perm_bindings_FLOOKUP:
  FLOOKUP (perm_bindings v1 v2 vs) v = FLOOKUP vs (perm1 v1 v2 v)
Proof
  rw[perm1_def,perm_bindings_def,FLOOKUP_UPDATE,FDOM_FLOOKUP,FLOOKUP_DRESTRICT] >> rw[] >> fs[] >>
  Cases_on ‘FLOOKUP vs v1’ >> fs[] >>
  Cases_on ‘FLOOKUP vs v2’ >> fs[] >>
  Cases_on ‘FLOOKUP vs v’ >> fs[]
QED

Theorem perm_state_FLOOKUP:
  FLOOKUP (perm_state v1 v2 s).bindings v = FLOOKUP s.bindings (perm1 v1 v2 v)
Proof
  rw[perm_state_def,perm_bindings_FLOOKUP]
QED

Theorem perm_state_ALOOKUP:
  ALOOKUP (perm_state v1 v2 s).funs d = OPTION_MAP (perm_closure v1 v2) (ALOOKUP s.funs d)
Proof
   qspecl_then [‘perm_closure v1 v2’] assume_tac ETA_THM >>
   rw[perm_state_def,perm_closure_def,PAIR_MAP_app,ALOOKUP_MAP]
QED

Theorem perm1_cancel[simp]:
  perm1 v1 v2 (perm1 v1 v2 x) = x
Proof
  rw[perm1_def] >> fs[CaseEq "bool"] >> fs[]
QED

Theorem perm_endpoint_cancel[simp]:
  perm_endpoint v1 v2 (perm_endpoint v1 v2 e) = e
Proof
  Induct_on ‘e’ >>
  rw[perm_endpoint_def] >>
  rw[MAP_MAP_o,o_DEF]
QED

Theorem perm_bindings_cancel[simp]:
  perm_bindings v1 v2 (perm_bindings v1 v2 x) = x
Proof
  rw[fmap_eq_flookup,perm_bindings_FLOOKUP,perm1_def]
QED

Theorem perm_closure_cancel[simp]:
  ∀v1 v2 cf. perm_closure v1 v2 (perm_closure v1 v2 cf) = cf
Proof
  ho_match_mp_tac perm_closure_ind \\ rw[perm_closure_def]
  >- (Induct_on ‘vars’ \\ rw[])
  >- (Induct_on ‘funs’ \\ rw[] \\ rpt (gs[] \\ pairarg_tac) \\ rveq \\ gs[] \\ metis_tac [])
QED

Theorem perm_state_cancel[simp]:
  perm_state v1 v2 (perm_state v1 v2 x) = x
Proof
  rw[payloadLangTheory.state_component_equality,perm_state_def,perm1_def,PAIR_MAP_app]
  \\ qmatch_goalsub_abbrev_tac ‘_ = xs’ \\ pop_assum kall_tac
  \\ Induct_on ‘xs’ \\ rw[] \\ Cases_on ‘h’ \\ simp [perm_closure_cancel]
QED

Theorem perm_network_cancel[simp]:
  ∀v1 v2 n1 n2.
  perm_network v1 v2 (perm_network v1 v2 n1) = n1
Proof
  Induct_on ‘n1’ >> rw[perm_network_def] >> rw[perm_network_def]
QED

Theorem MEM_perm_endpoint:
  ∀e fv1 fv2 fv3.
  MEM fv1 (free_var_names_endpoint(perm_endpoint fv2 fv3 e)) = MEM (perm1 fv2 fv3 fv1) (free_var_names_endpoint e)
Proof
  Induct >> rw[perm_endpoint_def,payloadLangTheory.free_var_names_endpoint_def,EQ_IMP_THM,MEM_FILTER,perm1_cancel,MEM_MAP] >> rw[perm1_cancel] >>
  TRY(fs[perm1_def] >> every_case_tac >> fs[] >> NO_TAC) >>
  TRY disj1_tac >>
  qexists_tac ‘perm1 fv2 fv3 fv1’ >>
  rw[perm1_cancel]
QED

Theorem MEM_perm_network:
  ∀n fv1 fv2 fv3.
  MEM fv1 (free_var_names_network(perm_network fv2 fv3 n)) = MEM (perm1 fv2 fv3 fv1) (free_var_names_network n)
Proof
  Induct >> rw[perm_network_def,payloadLangTheory.free_var_names_network_def,MEM_perm_endpoint]
QED

Theorem perm_network_rotate:
  ∀v1 v2 n1 n2.
  perm_network v1 v2 n1 = n2 ⇒
  perm_network v1 v2 n2 = n1
Proof
  Induct_on ‘n1’ >> rw[perm_network_def] >> rw[perm_network_def]
QED

Theorem bisim_upto_sym:
  ∀ts R p q.
  (R p q ∧ symmetric R ∧
   ∀p q l.
     R p q ⇒
     (∀p'. ts p l p' ⇒ ∃q'. ts q l q' ∧ R p' q')) ⇒
  BISIM_REL ts p q
Proof
  rw[BISIM_REL_def] >>
  qexists_tac ‘λp q. R p q ∨ R q p’ >>
  rw[BISIM_def] >>
  metis_tac[symmetric_def]
QED

Theorem perm_state_queues[simp]:
  perm_state v1 v2 (s with queues := qs) = (perm_state v1 v2 s) with queues := qs
Proof
  rw[perm_state_def]
QED

Theorem perm_state_queues'[simp]:
  (perm_state v1 v2 s).queues = s.queues
Proof
  rw[perm_state_def]
QED

Theorem perm_state_bupd[simp]:
  (perm_state v1 v2 (s with bindings := x.bindings |+ (v, d))) =
  s with <| bindings := ((perm_state v1 v2 x).bindings |+ (perm1 v1 v2 v, d));
            funs := MAP (I ## perm_closure v1 v2) s.funs |>
Proof
  rw[payloadLangTheory.state_component_equality,fmap_eq_flookup,perm_state_FLOOKUP] >-
    (rw[FLOOKUP_UPDATE] >> fs[] >> simp[perm_state_FLOOKUP]) >-
    (rw[PAIR_MAP_app,perm_state_def])
QED

Theorem perm_endpoint_dsubst:
  ∀v1 v2 e e' d.
    perm_endpoint v1 v2 (dsubst e d e') =
      dsubst (perm_endpoint v1 v2 e) d
             (perm_endpoint v1 v2 e')
Proof
  rw [] \\ induct_on ‘e’
  \\ rw [payloadLangTheory.dsubst_def,perm_endpoint_def]
QED

Theorem perm1_MEM:
  MEM v l ⇔ MEM (perm1 v1 v2 v) (MAP (perm1 v1 v2) l)
Proof
  Induct_on ‘l’ \\ rw[] \\ rw[perm1_def] \\ simp[]
QED

Theorem MAP_FST_MAP:
  MAP FST (MAP (f ## I) l) = MAP f (MAP FST l)
Proof
  Induct_on ‘l’ \\ simp[]
QED

Theorem MAP_SND_MAP:
  MAP SND (MAP (I ## f) l) = MAP f (MAP SND l)
Proof
  Induct_on ‘l’ \\ simp[]
QED

Theorem perm_bindings_update_list:
  perm_bindings v1 v2 (v |++ l) = perm_bindings v1 v2 v |++ MAP (perm1 v1 v2 ## I) l
Proof
  Induct_on ‘l’ \\ rw [FUPDATE_LIST_THM]
  \\ Cases_on ‘h’ \\ Cases_on ‘MEM q (MAP FST l)’
  >- (simp[FUPDATE_FUPDATE_LIST_MEM]
      \\ mp_tac (GEN_ALL FUPDATE_FUPDATE_LIST_MEM)
      \\ disch_then(qspecl_then[‘r’,‘MAP (perm1 v1 v2 ## I) l’,
                                ‘perm1 v1 v2 q’,
                                ‘perm_bindings v1 v2 v’] mp_tac)
      \\ impl_tac
      >- (simp[MAP_FST_MAP]
          \\ irule ((fst o EQ_IMP_RULE) perm1_MEM) \\ simp[])
      \\ rw [])
  >- (simp[FUPDATE_FUPDATE_LIST_COMMUTES]
      \\ mp_tac (GEN_ALL FUPDATE_FUPDATE_LIST_COMMUTES)
      \\ disch_then(qspecl_then[‘r’,‘MAP (perm1 v1 v2 ## I) l’,
                                ‘perm1 v1 v2 q’,
                                ‘perm_bindings v1 v2 v’] mp_tac)
      \\ impl_tac
      >- (simp[MAP_FST_MAP] \\ CCONTR_TAC \\ fs[]
          \\ drule ((snd o EQ_IMP_RULE) perm1_MEM)
          \\ simp[])
      \\ rw[] \\ pop_assum kall_tac
      \\ rw[fmap_eq_flookup,perm_bindings_FLOOKUP]
      \\ rw[FLOOKUP_UPDATE]
      \\ fs[perm1_cancel,perm_bindings_FLOOKUP,fmap_eq_flookup])
QED

Theorem perm_network_bisim:
  BISIM_REL (trans conf) (perm_network v1 v2 n) n
Proof
  match_mp_tac bisim_upto_sym >>
  qexists_tac ‘λn1 n2. n2 = perm_network v1 v2 n1’ >>
  rw[symmetric_def,EQ_IMP_THM] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac (List.rev [‘conf’,‘p’,‘l’,‘p'’]) >>
  ho_match_mp_tac payloadSemTheory.trans_ind >>
  rw[perm_network_def,perm_endpoint_def] >>
  TRY (MAP_FIRST (fn thm => match_mp_tac thm >> simp[perm_state_FLOOKUP] >>
                            rpt(goal_assum drule) >> simp[] >> NO_TAC)
                 (CONJUNCTS payloadSemTheory.trans_rules)) >-
    (drule payloadSemTheory.trans_enqueue >>
     disch_then(qspecl_then [‘conf’,‘perm_state v1 v2 s’,‘d’,‘perm_endpoint v1 v2 e’] mp_tac) >>
     simp[]) >-
    (drule payloadSemTheory.trans_dequeue_last_payload >>
     disch_then(qspecl_then [‘conf’,‘perm_state v1 v2 s’,
                             ‘perm1 v1 v2 v’,
                             ‘perm_endpoint v1 v2 e’,
                             ‘d’,‘tl’,‘ds’] mp_tac) >>
     simp[] >> qmatch_goalsub_abbrev_tac ‘trans _ _ _ ep1 ⇒ trans _ _ _ ep2’ >>
     ‘ep1 = ep2’ suffices_by (rveq >> simp[]) >>
     UNABBREV_ALL_TAC >> simp[payloadLangTheory.state_component_equality,perm_state_def,PAIR_MAP_app]) >-
    (drule payloadSemTheory.trans_dequeue_intermediate_payload >>
     disch_then(qspecl_then [‘conf’,‘perm_state v1 v2 s’,‘perm1 v1 v2 v’,‘perm_endpoint v1 v2 e’] mp_tac) >>
     simp[]) >-
    (‘EVERY IS_SOME (MAP (FLOOKUP (perm_state v1 v2 s).bindings) (MAP (perm1 v1 v2) vl))’
       by(fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,perm_state_FLOOKUP]) >>
     drule payloadSemTheory.trans_let >>
     disch_then(qspecl_then [‘conf’,‘perm1 v1 v2 v’,‘p’,‘f’,‘perm_endpoint v1 v2 e’] mp_tac) >>
     simp[MAP_MAP_o,o_DEF,perm_state_FLOOKUP] >>
     qmatch_goalsub_abbrev_tac ‘a1 ⇒ a2’ >> ‘a1 = a2’ suffices_by simp[] >>
     unabbrev_all_tac >>
     AP_TERM_TAC >>
     AP_THM_TAC >>
     AP_TERM_TAC >>
     simp[payloadLangTheory.state_component_equality,perm_state_def,PAIR_MAP_app]) >-
   (rw[perm_endpoint_dsubst,payloadSemTheory.trans_fix,perm_endpoint_def]) >-
   (‘EVERY (IS_SOME o FLOOKUP (perm_state v1 v2 s).bindings) (MAP (perm1 v1 v2) vars)’
       by(fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,perm_state_FLOOKUP]) >>
    drule payloadSemTheory.trans_letrec >>
    disch_then(qspecl_then [‘conf’,‘p’,‘dn’,‘perm_endpoint v1 v2 e’] mp_tac) >>
    simp[perm_state_def,perm_closure_def,PAIR_MAP_app]) >-
   (‘EVERY (IS_SOME o FLOOKUP (perm_state v1 v2 s).bindings) (MAP (perm1 v1 v2) args)’
       by(fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,perm_state_FLOOKUP]) >>
    pop_assum (mp_then Any mp_tac payloadSemTheory.trans_call) >>
    disch_then(qspecl_then [‘conf’,‘p’,‘dn’,
                            ‘MAP (perm1 v1 v2) params’,
                            ‘MAP (I ## perm_closure v1 v2) funs’,
                            ‘perm_bindings v1 v2 bindings’,
                            ‘perm_endpoint v1 v2 e’] mp_tac) >>
    impl_tac >-
     (simp[perm_state_ALOOKUP,perm_closure_def,PAIR_MAP_app]) >>
    simp[perm_state_def,perm_closure_def,PAIR_MAP_app] >>
    qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ s1 _) ⇒ trans _ _ _ (NEndpoint _ s2 _)’ >>
    ‘s1 = s2’ suffices_by simp[] >>
    UNABBREV_ALL_TAC >> simp[payloadLangTheory.state_component_equality] >>
    simp[perm_bindings_update_list,perm_bindings_FLOOKUP] >>
    AP_TERM_TAC >> simp[ZIP_MAP,MAP_ZIP,PAIR_MAP_app] >>
    qabbrev_tac ‘ll = ZIP (params,args)’ >>
    pop_assum kall_tac >>
    induct_on ‘ll’ >> simp[] >> rw[] >> Cases_on ‘h’ >> simp[perm_bindings_FLOOKUP])
QED

Theorem perm_endpoint:
  ∀fv1 fv2 conf n.
  ~MEM fv1 (var_names_endpoint n) ∧ ~MEM fv2 (var_names_endpoint n) ⇒
    (perm_endpoint fv1 fv2 (compile_endpoint (endpoint_to_choice$compile_endpoint fv1 n))) =
    (compile_endpoint (endpoint_to_choice$compile_endpoint fv2 n))
Proof
  Induct_on ‘n’ >>
  rw[endpoint_to_payloadTheory.compile_endpoint_def,endpoint_to_choiceTheory.compile_endpoint_def,perm_endpoint_def,var_names_endpoint_def] >>
  rw[perm1_def] >>
  rw[MAP_EQ_ID,perm1_def] >> rw[] >> metis_tac[]
QED

Theorem compile_endpoint_support':
  !e fv fv1. MEM fv1 (free_var_names_endpoint (endpoint_to_choice$compile_endpoint fv e))
   ==> MEM fv1 (free_var_names_endpoint e)
Proof
  Induct >> rpt strip_tac
  >> fs[endpoint_to_choiceTheory.compile_endpoint_def,free_var_names_endpoint_def,MEM_FILTER]
  >> every_case_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]
  >> res_tac >> fs[]
QED

Theorem perm_state_restrict:
  (perm_state fv1 fv2 ss).bindings \\ fv1 \\ fv2 = ss.bindings \\ fv1 \\ fv2
Proof
  rw[fmap_eq_flookup] >> rw[DOMSUB_FLOOKUP_THM,perm_state_FLOOKUP] >>
  rw[perm1_def]
QED

Theorem perm_state_bindings[simp]:
  (perm_state fv1 fv2 ss) with bindings := x =
    ss with <| bindings := x; funs := MAP (I ## perm_closure fv1 fv2) ss.funs |>
Proof
  rw[perm_state_def]
QED

Theorem perm_network:
  ∀fv1 fv2 conf n.
  ~MEM fv1 (var_names_network n) ∧ ~MEM fv2 (var_names_network n) ⇒
  junkcong {fv1;fv2}
    (perm_network fv1 fv2 (compile_network conf (compile_network_fv fv1 n)))
    (compile_network conf (compile_network_fv fv2 n))
Proof
  Induct_on ‘n’ >>
  rw[compile_network_fv_def,endpoint_to_payloadTheory.compile_network_def,
     perm_network_def,var_names_network_def,
     payloadPropsTheory.junkcong_refl,perm_endpoint] >-
   metis_tac[payloadPropsTheory.junkcong_par] >>
  qmatch_goalsub_abbrev_tac ‘NEndpoint s (perm_state _ _ ss)’ >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint s ((perm_state fv1 fv2 ss)
                               with bindings := ((perm_state fv1 fv2 ss).bindings \\ fv1))
                 (compile_endpoint (compile_endpoint fv2 e))’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[] >>
               spose_not_then strip_assume_tac >>
               drule_then assume_tac endpoint_to_payload_free_var_names >>
               drule_then assume_tac compile_endpoint_support' >>
               drule free_var_names_var_names >> fs[]) >>
  qmatch_goalsub_abbrev_tac ‘NEndpoint s sss’ >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint s (sss with bindings := (sss.bindings \\ fv2)) (compile_endpoint (compile_endpoint fv2 e))’ >>
  qunabbrev_tac ‘sss’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[] >>
               spose_not_then strip_assume_tac >>
               drule_then assume_tac endpoint_to_payload_free_var_names >>
               drule_then assume_tac compile_endpoint_support' >>
               drule free_var_names_var_names >> fs[]) >>
  simp[] >>
  simp[perm_state_restrict] >>
  match_mp_tac payloadPropsTheory.junkcong_sym >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint s (ss with bindings := (ss.bindings \\ fv1)) (compile_endpoint (compile_endpoint fv2 e))’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[] >>
               spose_not_then strip_assume_tac >>
               drule_then assume_tac endpoint_to_payload_free_var_names >>
               drule_then assume_tac compile_endpoint_support' >>
               drule free_var_names_var_names >> fs[]) >>
  qmatch_goalsub_abbrev_tac ‘NEndpoint s sss’ >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint s (sss with bindings := (sss.bindings \\ fv2)) (compile_endpoint (compile_endpoint fv2 e))’ >>
  qunabbrev_tac ‘sss’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[] >>
               spose_not_then strip_assume_tac >>
               drule_then assume_tac endpoint_to_payload_free_var_names >>
               drule_then assume_tac compile_endpoint_support' >>
               drule free_var_names_var_names >> fs[]) >>
  qmatch_goalsub_abbrev_tac ‘junkcong _ (NEndpoint _ ss1 _) (NEndpoint _ ss2 _)’ >>
  ‘ss1 = ss2’ suffices_by simp[payloadPropsTheory.junkcong_refl] >>
  fs[Abbr‘ss1’,Abbr‘ss2’,payloadLangTheory.state_component_equality] >>
  simp[Abbr‘ss’,compile_state_def]
QED

Definition restrict_network_def:
   (restrict_network vs (payloadLang$NNil) = NNil)
/\ (restrict_network vs (NEndpoint p s e) = NEndpoint p (s with bindings := DRESTRICT s.bindings vs) e)
/\ (restrict_network vs (NPar n1 n2) = NPar (restrict_network vs n1) (restrict_network vs n2))
End

Theorem perm_network':
  ∀fv1 fv2 fv3 conf n.
  ~MEM fv1 (var_names_network n) ∧ ~MEM fv2 (var_names_network n) ⇒
  (restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2)
    (perm_network fv1 fv2 (compile_network conf (compile_network_fv fv1 n))))
  =
  (restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2)
    (compile_network conf (compile_network_fv fv2 n)))
Proof
  Induct_on ‘n’ >>
  rw[compile_network_fv_def,endpoint_to_payloadTheory.compile_network_def,
     perm_network_def,var_names_network_def,
     payloadPropsTheory.junkcong_refl,perm_endpoint,
     restrict_network_def] >>
  rw[payloadLangTheory.state_component_equality,fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
  rw[perm_state_FLOOKUP,perm1_def,compile_state_def]
QED

Theorem restrict_network_bisim:
  ~MEM fv1 (free_var_names_network n) ∧ ~MEM fv2 (free_var_names_network n)
  ⇒
  BISIM_REL (trans conf) (restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) n) n
Proof
  rw[] >>
  ho_match_mp_tac junkcong_bisim >>
  qexists_tac ‘{fv1;fv2}’ >>
  Induct_on ‘n’ >> fs[payloadLangTheory.free_var_names_network_def,restrict_network_def,payloadPropsTheory.junkcong_refl] >-
   (metis_tac[payloadPropsTheory.junkcong_par]) >>
  rw[] >>
  rename1 ‘NEndpoint p’ >>
  rename1 ‘(s with bindings := _)’ >>
  ‘DRESTRICT s.bindings (λx. x ≠ fv1 ∧ x ≠ fv2) = s.bindings \\ fv1 \\ fv2’
    by(rw[fmap_eq_flookup,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw[] >> fs[]) >>
  pop_assum SUBST_ALL_TAC >>
  match_mp_tac payloadPropsTheory.junkcong_sym >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint p (s with bindings := s.bindings \\ fv1) e’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[]) >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint p ((s with bindings := s.bindings \\ fv1) with bindings := (s with bindings := s.bindings \\ fv1).bindings \\ fv2) e’ >>
  conj_tac >- (match_mp_tac payloadPropsTheory.junkcong_remove_junk >> simp[]) >>
  simp[payloadPropsTheory.junkcong_refl]
QED

Theorem junkcong_binding_LIST_REL_bindings:
  ∀fv epn1 epn2.
    payloadProps$junkcong fv epn1 epn2 ⇒
    LIST_REL (λ((p1,s1,e1) (p2,s2,e2)).
                e1 = e2 ∧ p1 = p2 ∧
                (∀x. x ∈ (FDOM s1.bindings DIFF FDOM s2.bindings)
                     ⇒ ¬MEM x (free_var_names_endpoint e1)) ∧
                (∀x. x ∈ (FDOM s2.bindings DIFF FDOM s1.bindings)
                     ⇒ ¬MEM x (free_var_names_endpoint e2)))
             (endpoints epn1) (endpoints epn2)
Proof
  ho_match_mp_tac payloadPropsTheory.junkcong_strongind
  \\ rw[payloadLangTheory.endpoints_def] \\ simp[]
  >- (Induct_on ‘epn1’ \\ rw[payloadLangTheory.endpoints_def]
      \\ last_x_assum assume_tac
      \\ dxrule_all (EQ_IMP_RULE LIST_REL_APPEND  |> fst) \\ rw[])
  >- (pop_assum mp_tac \\ pop_assum kall_tac
      \\ qmatch_goalsub_abbrev_tac ‘LIST_REL _ e1 e2’
      \\ pop_assum kall_tac \\ pop_assum kall_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘e2’,‘e1’]
      \\ ho_match_mp_tac LIST_REL_ind
      \\ rw[] \\ PairCases_on ‘h1’ \\ PairCases_on ‘h2’
      \\ gs[] \\ metis_tac[INTER_COMM])
  >- (ho_match_mp_tac LIST_REL_trans
      \\ qexists_tac ‘endpoints epn1'’
      \\ simp[] \\ rw[]
      \\ qmatch_goalsub_abbrev_tac ‘_ e1 e2’
      \\ pop_assum kall_tac \\ pop_assum kall_tac
      \\ qmatch_asmsub_abbrev_tac ‘_ e1 e3’
      \\ PairCases_on ‘e1’
      \\ PairCases_on ‘e2’
      \\ PairCases_on ‘e3’
      \\ gs[] \\ metis_tac [])
  >- (qpat_x_assum ‘LIST_REL _ (endpoints epn1) _’ assume_tac
      \\ (EQ_IMP_RULE LIST_REL_APPEND  |> fst  |> GEN_ALL  |> dxrule_all)
      \\ simp[payloadLangTheory.endpoints_def])
QED

Theorem junkcong_no_undefined_vars_closure_aux:
  ∀fv epn1 epn2.
    payloadProps$junkcong fv epn1 epn2 ⇒
    (EVERY (λ(p,s,e). EVERY (λ(s,cl). no_undefined_vars_closure cl) s.funs) (endpoints epn1)
     ⇔ EVERY (λ(p,s,e). EVERY (λ(s,cl). no_undefined_vars_closure cl) s.funs) (endpoints epn2))
Proof
  ho_match_mp_tac payloadPropsTheory.junkcong_strongind
  \\ rw[] \\ EQ_TAC \\ rw[]
  \\ gs[no_undefined_vars_network_def,payloadLangTheory.endpoints_def,
       no_undefined_vars_closure_def]
  >- (drule junkcong_binding_LIST_REL_bindings
      \\ rw[payloadLangTheory.endpoints_def]
      \\ gs[SUBSET_DEF,INTER_DEF]
      \\ metis_tac [])
  >- (drule junkcong_binding_LIST_REL_bindings
      \\ rw[payloadLangTheory.endpoints_def]
      \\ gs[SUBSET_DEF,INTER_DEF]
      \\ metis_tac [])
  >- (gs [SUBSET_DEF] \\ rw[] \\ first_x_assum drule
      \\ rw[] \\ rw[] \\ gs[])
  >- (gs [SUBSET_DEF] \\ rw[] \\ first_x_assum drule
      \\ rw[] \\ rw[] \\ gs[])
QED

Theorem junkcong_no_undefined_vars_network:
  ∀fv epn epn'.
    junkcong fv epn epn' ⇒
    (no_undefined_vars_network epn ⇔ no_undefined_vars_network epn')
Proof
  ho_match_mp_tac payloadPropsTheory.junkcong_strongind
  \\ rw[] \\ EQ_TAC \\ rw[]
  \\ gs[no_undefined_vars_network_def,payloadLangTheory.endpoints_def,
       no_undefined_vars_closure_def]
  >- (drule junkcong_no_undefined_vars_closure_aux
      \\ rw[payloadLangTheory.endpoints_def] \\ gs[]
      \\ drule junkcong_binding_LIST_REL_bindings
      \\ rw[payloadLangTheory.endpoints_def]
      \\ gs[SUBSET_DEF,INTER_DEF]
      \\ metis_tac [])
  >- (drule junkcong_no_undefined_vars_closure_aux
      \\ rw[payloadLangTheory.endpoints_def] \\ gs[]
      \\ drule junkcong_binding_LIST_REL_bindings
      \\ rw[payloadLangTheory.endpoints_def]
      \\ gs[SUBSET_DEF,INTER_DEF]
      \\ metis_tac [])
  >- (gs [SUBSET_DEF] \\ rw[] \\ first_x_assum drule
      \\ rw[] \\ rw[] \\ gs[])
  >- (gs [SUBSET_DEF] \\ rw[] \\ first_x_assum drule
      \\ rw[] \\ rw[] \\ gs[])
QED

Theorem junkcong_free_fix_names_network:
  ∀fv epn epn'.
    junkcong fv epn epn' ⇒
    (free_fix_names_network epn = free_fix_names_network epn')
Proof
  ho_match_mp_tac payloadPropsTheory.junkcong_strongind
  \\ rw[payloadLangTheory.free_fix_names_network_def]
QED

Theorem projection_preservation:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
   ∧ dvarsOf c = []
   ⇒ ∃s''' c''' epn.
      trans_s (s'',c'') (s''',c''') ∧
      (reduction conf)^* (projection conf s c (procsOf c))
                         epn ∧
      BISIM_REL (trans conf) (projection conf s''' c''' (procsOf c)) epn
Proof
  rw [] >>
  drule_all_then strip_assume_tac projection_preservation_junkcong >>
  goal_assum drule >>
  goal_assum drule >>
  fs[projection_def,endpoint_to_choiceTheory.compile_network_def] >>
  fs[project_choice_def,compile_rel_def] >>
  drule junkcong_compile_to_payload >>
  disch_then(qspec_then ‘conf’ strip_assume_tac) >>
  match_mp_tac BISIM_SYM >>
  drule_then(qspec_then ‘conf’ assume_tac) junkcong_bisim >>
  match_mp_tac BISIM_TRANS >>
  dxrule_then assume_tac BISIM_SYM >>
  goal_assum drule >>
  irule compile_network_alt_fully_abstract >> simp[fix_network_compile_network] >>
  conj_tac >-
   (drule_then (mp_tac o GSYM) junkcong_no_undefined_vars_network >> rw[] >>
    irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (drule junkcong_free_fix_names_network >>
    qmatch_goalsub_abbrev_tac ‘free_fix_names_network pp’ >>
    ‘free_fix_names_network pp = []’ suffices_by  rw[] >>
    UNABBREV_ALL_TAC >>
    irule dvarsOf_imp_free_fix_names_network >>
    drule_all trans_s_trans >>
    disch_then (mp_then Any assume_tac dvarsOf_nil_trans_s) >>
    gs[]) >>
  conj_tac >-
   (irule dvarsOf_imp_free_fix_names_network >>
    drule_all trans_s_trans >>
    disch_then (mp_then Any assume_tac dvarsOf_nil_trans_s) >>
    gs[]) >>
  match_mp_tac BISIM_TRANS >>
  goal_assum drule >>
  qpat_abbrev_tac ‘fv1 = gen_fresh_name _’ >>
  qpat_abbrev_tac ‘fv2 = gen_fresh_name _’ >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ a1 a2’ >>
  ‘~MEM fv1 (free_var_names_network a1) ∧ ~MEM fv2 (free_var_names_network a1)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          match_mp_tac (compile_network_support |> ONCE_REWRITE_RULE[MONO_NOT_EQ]) >>
          match_mp_tac (projection_free_variables_SUBSET |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          match_mp_tac(MATCH_MP IMAGE_SUBSET (SPEC_ALL free_variables_variables) |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          imp_res_tac trans_s_variables_mono >>
          dxrule_then dxrule SUBSET_TRANS >>
          strip_tac >>
          match_mp_tac(IMAGE_SUBSET |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(PURE_REWRITE_CONV[SUBSET_DEF,Once MONO_NOT_EQ]))) |> MP_CANON) >>
          goal_assum drule >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM projection_variables_eq] >>
          simp[gen_fresh_name_same]) >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[endpoint_to_choiceProofTheory.MEM_free_vars_compile_network'] >>
          simp[gen_fresh_name_same] >>
          match_mp_tac(CONTRAPOS(SPEC_ALL free_var_names_var_names_network)) >>
          simp[gen_fresh_name_same])
      ) >>
  ‘~MEM fv1 (free_var_names_network a2) ∧ ~MEM fv2 (free_var_names_network a2)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >>
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MEM_free_vars_compile_network'] >>
          conj_tac >> match_mp_tac gen_fresh_nameE >>
          simp[projection_variables_eq] >>
          metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
                    IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET])) >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a1’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a2’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM perm_network'] >>
  conj_tac >-
    (MAP_EVERY qunabbrev_tac [‘fv1’,‘fv2’] >>
     simp[gen_fresh_name_same] >>
     match_mp_tac gen_fresh_nameE >>
     simp[projection_variables_eq] >>
     metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
               IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET]) >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ (restrict_network _ a1) (restrict_network _ a2)’ >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a1’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[] >>
    qunabbrev_tac ‘a1’ >> simp[MEM_perm_network] >>
    rw[perm1_def]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a2’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  match_mp_tac BISIM_SYM >>
  simp[perm_network_bisim]
QED

Theorem projection_top_preservation:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
   ∧ dvarsOf c = []
   ⇒ ∃s''' c''' epn.
      trans_s (s'',c'') (s''',c''') ∧
      (reduction conf)^* (projection_top conf s c (procsOf c))
                         epn ∧
      BISIM_REL (trans conf) (projection conf s''' c''' (procsOf c)) epn
Proof
  rw [] >>
  drule_all_then strip_assume_tac projection_top_preservation_junkcong >>
  goal_assum drule >>
  goal_assum drule >>
  fs[projection_def,endpoint_to_choiceTheory.compile_network_def] >>
  fs[project_choice_def,compile_rel_def] >>
  drule junkcong_compile_to_payload >>
  disch_then(qspec_then ‘conf’ strip_assume_tac) >>
  match_mp_tac BISIM_SYM >>
  drule_then(qspec_then ‘conf’ assume_tac) junkcong_bisim >>
  match_mp_tac BISIM_TRANS >>
  dxrule_then assume_tac BISIM_SYM >>
  goal_assum drule >>
  irule compile_network_alt_fully_abstract >> simp[fix_network_compile_network] >>
  conj_tac >-
   (drule_then (mp_tac o GSYM) junkcong_no_undefined_vars_network >> rw[] >>
    irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (drule junkcong_free_fix_names_network >>
    qmatch_goalsub_abbrev_tac ‘free_fix_names_network pp’ >>
    ‘free_fix_names_network pp = []’ suffices_by  rw[] >>
    UNABBREV_ALL_TAC >>
    irule dvarsOf_imp_free_fix_names_network >>
    drule_all trans_s_trans >>
    disch_then (mp_then Any assume_tac dvarsOf_nil_trans_s) >>
    gs[]) >>
  conj_tac >-
   (irule dvarsOf_imp_free_fix_names_network >>
    drule_all trans_s_trans >>
    disch_then (mp_then Any assume_tac dvarsOf_nil_trans_s) >>
    gs[]) >>
  match_mp_tac BISIM_TRANS >>
  goal_assum drule >>
  qpat_abbrev_tac ‘fv1 = gen_fresh_name _’ >>
  qpat_abbrev_tac ‘fv2 = gen_fresh_name _’ >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ a1 a2’ >>
  ‘~MEM fv1 (free_var_names_network a1) ∧ ~MEM fv2 (free_var_names_network a1)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          match_mp_tac (compile_network_support |> ONCE_REWRITE_RULE[MONO_NOT_EQ]) >>
          match_mp_tac (projection_free_variables_SUBSET |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          match_mp_tac(MATCH_MP IMAGE_SUBSET (SPEC_ALL free_variables_variables) |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          imp_res_tac trans_s_variables_mono >>
          dxrule_then dxrule SUBSET_TRANS >>
          strip_tac >>
          match_mp_tac(IMAGE_SUBSET |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(PURE_REWRITE_CONV[SUBSET_DEF,Once MONO_NOT_EQ]))) |> MP_CANON) >>
          goal_assum drule >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM projection_variables_eq] >>
          simp[gen_fresh_name_same]) >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[endpoint_to_choiceProofTheory.MEM_free_vars_compile_network'] >>
          simp[gen_fresh_name_same] >>
          match_mp_tac(CONTRAPOS(SPEC_ALL free_var_names_var_names_network)) >>
          simp[gen_fresh_name_same])
      ) >>
  ‘~MEM fv1 (free_var_names_network a2) ∧ ~MEM fv2 (free_var_names_network a2)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >>
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MEM_free_vars_compile_network'] >>
          conj_tac >> match_mp_tac gen_fresh_nameE >>
          simp[projection_variables_eq] >>
          metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
                    IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET])) >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a1’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a2’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM perm_network'] >>
  conj_tac >-
    (MAP_EVERY qunabbrev_tac [‘fv1’,‘fv2’] >>
     simp[gen_fresh_name_same] >>
     match_mp_tac gen_fresh_nameE >>
     simp[projection_variables_eq] >>
     metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
               IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET]) >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ (restrict_network _ a1) (restrict_network _ a2)’ >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a1’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[] >>
    qunabbrev_tac ‘a1’ >> simp[MEM_perm_network] >>
    rw[perm1_def]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a2’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  match_mp_tac BISIM_SYM >>
  simp[perm_network_bisim]
QED

val from_choice_reflection =
  endpoint_to_choiceProofTheory.compile_network_reflection;

val from_endpoint_reflection =
  chor_to_endpointProofTheory.compile_network_reflection;

val from_payload_reflection =
  endpoint_to_payloadProofTheory.compile_network_reflection;

val from_closure_reflection =
  payload_closureProofTheory.compile_network_reflection_alt;

(* Enpoints names are preserved over the endpoint_to_choice
   compilation step (generic version)
*)
Theorem endpoints_compile_network_choice_aux:
  ∀epn fv.
   MAP FST (endpoints (endpoint_to_choice$compile_network_fv fv epn))
   = MAP FST (endpoints epn)
Proof
  Induct
  \\ rw [endpoint_to_choiceTheory.compile_network_fv_def,
         endpoints_def]
QED

(* Enpoints names are preserved over the endpoint_to_choice
   compilation step
*)
Theorem endpoints_compile_network_choice:
  ∀epn.
   MAP FST (endpoints (endpoint_to_choice$compile_network epn)) = MAP FST (endpoints epn)
Proof
  rw [endpoint_to_choiceTheory.compile_network_def,endpoints_compile_network_choice_aux]
QED

(* split_sel can only remove processes *)
Triviality MEM_partners_endpoint_split_sel:
  ∀(c : chor) p dvars l b x r.
   split_sel p l c = SOME (b,r) ∧
   no_self_comunication c ∧
   MEM x (partners_endpoint (project' p dvars r))
   ⇒ MEM x (partners_endpoint (project' p dvars c))
Proof
  Induct
  \\ fs [project_def,partners_endpoint_def,
         no_self_comunication_def,
         split_sel_def]
  \\ rw [partners_endpoint_def]
  >- (Cases_on ‘x = l’ \\ fs [] \\ metis_tac [])
  \\ metis_tac []
QED

(* split_sel preserves no_self_comunication_def *)
Theorem split_sel_no_self_comunication:
  ∀c p l b r.
    split_sel p l c = SOME (b,r) ∧
    no_self_comunication c
    ⇒ no_self_comunication r
Proof
  Induct \\ rw [split_sel_def,no_self_comunication_def] \\ fs []
  \\ metis_tac []
QED

(* projecting a process does not remove/change any other process
   when compared with the choreography (procsOf)
*)
Theorem MEM_partners_endpoint_imp_procsOf:
  ∀(c : chor) p dvars x.
    no_self_comunication c ∧
    MEM x (partners_endpoint (project' p dvars c))
    ⇒ MEM x (procsOf c)
Proof
  Induct
  \\ rw [procsOf_def,
         chor_to_endpointTheory.project_def,
         partners_endpoint_def,
         nub'_def]
  \\ TRY (fn (asms,goal) =>
            goal |> dest_disj |> fst
                 |> (fn t => (ASM_CASES_TAC t \\ fs []) (asms,goal)))
  \\ fs [MEM_FILTER,MEM_nub',no_self_comunication_def]
  \\ TRY (EVERY_CASE_TAC \\ fs [partners_endpoint_def] \\ NO_TAC)
  >- metis_tac []
  >- metis_tac []
  >- (EVERY_CASE_TAC \\ fs [partners_endpoint_def]
      >- metis_tac []
      >- metis_tac []
      \\ disj2_tac \\ first_x_assum irule
      \\ imp_res_tac MEM_partners_endpoint_split_sel
      \\ metis_tac [])
  >- let val d_tac = first_x_assum irule
                     \\ imp_res_tac MEM_partners_endpoint_split_sel
                     \\ metis_tac []
     in EVERY_CASE_TAC \\ fs [partners_endpoint_def]
        >- (disj2_tac \\ d_tac)
        >- (disj1_tac \\ d_tac)
        >- (disj2_tac \\ d_tac)
     end
  \\ metis_tac []
QED

(* NOT_USED *)
Theorem MEM_partners_network_FILTER:
  ∀l x s (c : chor) P.
   MEM x (partners_network (compile_network s c (FILTER P l)))
   ⇒ MEM x (partners_network (compile_network s c l))
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         partners_network_def]
  >- (disj1_tac \\ fs [])
  \\ disj2_tac \\ metis_tac []
QED

(* NOT USED *)
Theorem MEM_partners_network_nub':
  ∀l s (c : chor) x.
    MEM x (partners_network (compile_network s c (nub' l)))
    ⇒ MEM x (partners_network (compile_network s c l))
Proof
  Induct \\ rw [chor_to_endpointTheory.compile_network_gen_def,
                partners_network_def,nub'_def]
  >- (disj1_tac \\ fs [])
  \\ disj2_tac \\ first_x_assum irule
  \\ irule MEM_partners_network_FILTER
  \\ asm_exists_tac \\ fs []
QED

(* NOT USED *)
Theorem MEM_partners_network_APPEND:
  ∀l r x s (c : chor) P.
   MEM x (partners_network (compile_network s c (l ++ r)))
   ⇒ MEM x (partners_network (compile_network s c l)) ∨
     MEM x (partners_network (compile_network s c r))
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         partners_network_def]
  >- (disj1_tac \\ fs [])
  \\ metis_tac []
QED

(* Simplification of the traversal of partners_network when
   using a projected network
*)
Theorem partners_network_compile_network:
  ∀l (c : chor) dvars s.
    partners_network (compile_network s c l)
    = FLAT (MAP (\proc. partners_endpoint (project' proc [] c)) l)
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         partners_network_def]
QED

(* Projected networks are closed
   (only mentions processes withing the network)
*)
Theorem closed_network_from_chor:
  ∀s (c : chor).
   no_self_comunication c
   ⇒ closed_network (compile_network s c (procsOf c))
Proof
  rw [closed_network_def,
      closed_under_def,
      endpoints_compile_network_chor,
      partners_network_compile_network,
      SUBSET_DEF]
  \\ fs [MEM_FLAT,MEM_MAP,no_self_comunication_def] \\ rveq
  \\ irule MEM_partners_endpoint_imp_procsOf \\ fs []
  \\ asm_exists_tac \\ fs []
QED

(* Simplification of the traversal of endpoints when
   using a projected network
*)
Theorem endpoints_ok_compile_network:
  ∀l (c : chor) s.
   EVERY endpoint_ok (endpoints (compile_network s c l))
   = EVERY I (MAP (λp . ¬MEM p (partners_endpoint (project' p [] c))) l)
Proof
  Induct \\ rw [chor_to_endpointTheory.compile_network_gen_def,
                endpoint_ok_def,
                endpoints_def]
QED

(* The projected process is not mentioned withing its code
   (because no self-communication is allowed)
*)
Theorem MEM_partners_endpoint_project:
  ∀(c : chor) p dvars. no_self_comunication c ⇒ ¬MEM p (partners_endpoint (project' p dvars c))
Proof
 Induct
 \\ rw [partners_endpoint_def, chor_to_endpointTheory.project_def,no_self_comunication_def]
 \\ EVERY_CASE_TAC \\ rw [partners_endpoint_def]
 \\ CCONTR_TAC \\ fs []
 \\ imp_res_tac MEM_partners_endpoint_split_sel \\ rfs []
QED

(* projected networks always have empty queues *)
Theorem compile_network_empty_q:
  ∀l s (c : chor). empty_q (compile_network s c l)
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         endpointPropsTheory.empty_q_def]
QED

(* projected choice-free networks preserve empty_q_epn *)
Theorem compile_network_fv_empty_q:
  ∀epn fv.
   empty_q epn
   ⇒ empty_q (compile_network_fv fv epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

(* projected payload networks preserve empty_q_* *)
Theorem empty_q_to_payload:
  ∀epn conf. empty_q epn ⇒ empty_q (compile_network conf epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

Theorem empty_q_to_closure:
  ∀epn conf. empty_q epn ⇒ empty_q (compile_network_alt epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

Theorem empty_q_to_closure':
  ∀epn conf. empty_q epn ⇒ empty_q (payload_closure$compile_network epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

Theorem endpoints_compile_network_payload:
  ∀epn conf.
   MAP FST (endpoints (endpoint_to_payload$compile_network conf epn)) = MAP FST (endpoints epn)
Proof
  Induct \\ rw [endpoint_to_payloadTheory.compile_network_def,
                endpointPropsTheory.endpoints_def,
                payloadLangTheory.endpoints_def]
QED

Theorem endpoints_compile_network_closure:
  ∀epn conf.
   MAP FST (endpoints (payload_closure$compile_network_alt epn)) = MAP FST (endpoints epn)
Proof
  Induct \\ rw [payload_closureTheory.compile_network_alt_def,
                payloadLangTheory.endpoints_def]
QED

Theorem endpoints_compile_network_closure':
  ∀epn conf.
   MAP FST (endpoints (payload_closure$compile_network epn)) = MAP FST (endpoints epn)
Proof
  Induct \\ rw [payload_closureTheory.compile_network_def,
                payloadLangTheory.endpoints_def]
QED

Theorem projection_reflection_junkcong:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ dvarsOf c = []
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection conf s c (procsOf c)) epn
   ⇒ ∃epn0 epn1 c' s'.
       compile_rel conf epn (compile_network_alt epn0) ∧
       fix_network epn0 ∧ free_fix_names_network epn0 = [] ∧
       no_undefined_vars_network epn0 ∧
       (reduction conf)^* epn0 (compile_network conf epn1) ∧
       trans_s (s,c) (s',c') ∧
       junkcong {new_fv s c} (project_choice (new_fv s c) s' c' (procsOf c)) epn1 ∧
       compile_network_ok s' c' (procsOf c)
Proof
  rw [projection_def]
  \\ first_assum (mp_then Any mp_tac from_closure_reflection)
  \\ impl_tac
  \\ rw [fix_network_compile_network,
         endpoint_to_choiceTheory.compile_network_def,
         dvarsOf_imp_free_fix_names_network,
         no_undefined_vars_chor_to_network]
  >- rw [endpoints_compile_network_choice_aux,
         endpoints_compile_network_chor,
         endpoints_compile_network_payload,
         procsOf_all_distinct]
  \\ asm_exists_tac \\ simp[]
  \\ first_assum (mp_then Any mp_tac from_payload_reflection)
  \\ impl_tac \\ rw []
  >- (rw [endpoints_compile_network_choice_aux,
         endpoints_compile_network_chor,
         procsOf_all_distinct])
  >- (rw [choice_free_network_compile_network_fv,
          endpoint_to_choiceTheory.compile_network_def])
  \\ fs [endpoint_to_choiceTheory.compile_network_def]
  \\ first_assum (mp_then Any mp_tac from_choice_reflection)
  \\ impl_tac
  >- (rw [gen_fresh_name_same,
          endpoints_compile_network_chor,
          closed_network_from_chor,
          procsOf_all_distinct,
          endpoints_ok_compile_network,
          MEM_partners_endpoint_project]
      \\ qmatch_goalsub_abbrev_tac ‘MAP _ l’
      \\ rpt (pop_assum (K ALL_TAC))
      \\ Induct_on ‘l’ \\ rw [])
  \\ rw []
  \\ first_assum (mp_then Any mp_tac from_endpoint_reflection)
  \\ rw [] \\ fs[procsOf_all_distinct]
  \\ first_assum (mp_then Any mp_tac to_choice_preservation)
  \\ qmatch_asmsub_abbrev_tac ‘junkcong {fv}’
  \\ disch_then (qspec_then ‘fv’ mp_tac)
  \\ impl_tac
  >- metis_tac [endpoints_compile_network_chor,
                procsOf_all_distinct,
                endpoint_names_reduction,
                Abbr‘fv’,
                gen_fresh_name_same,
                reduction_var_names_mono]
  \\ rw []
  \\ qspecl_then [‘compile_network_fv fv n4’,‘n3’] mp_tac junkcong_reduction_pres
  \\ disch_then (drule_then drule) \\ rw []
  \\ qpat_assum ‘reduction^* p4 _’ (mp_then Any (drule_then assume_tac) RTC_SPLIT)
  \\ first_assum (mp_then Any mp_tac to_payload_preservation)
  \\ disch_then (qspec_then ‘conf’ mp_tac)
  \\ impl_tac
  >- (fs [] \\ irule choice_free_reduction
      \\ metis_tac [choice_free_network_compile_network_fv])
  \\ rw []
  \\ qpat_assum ‘(reduction conf)^* p3 _’ (mp_then Any (drule_then assume_tac) RTC_SPLIT)
  \\ qspec_then ‘p3''’ drule endpointPropsTheory.qcong_sym
  \\ disch_then (mp_then Any mp_tac endpointPropsTheory.empty_queue_qcong)
  \\ rw [compile_network_empty_q]
  \\ first_x_assum (mp_then Any drule junkcong_trans)
  \\ rw [] \\ drule empty_q_junkcong
  \\ impl_tac
  >- rw [compile_network_fv_empty_q,compile_network_empty_q]
  \\ rw []
  \\ drule_then (qspec_then ‘conf’ assume_tac) empty_q_to_payload
  \\ first_x_assum (irule_at Any) \\ simp[]
  \\ conj_tac
  >- (irule fix_network_reduction_RTC_pres
      \\ first_x_assum (irule_at Any)
      \\ simp[fix_network_compile_network])
  \\ conj_tac
  >- (qmatch_asmsub_abbrev_tac ‘(reduction conf)^* pp p3’
      \\ qspecl_then [‘conf’,‘pp’,‘p3’] mp_tac free_fix_names_network_reduction_RTC_pres
      \\ impl_tac >- simp[Abbr‘pp’,fix_network_compile_network]
      \\ qunabbrev_tac ‘pp’ \\ drule dvarsOf_imp_free_fix_names_network
      \\ rw[])
  >- (irule no_undefined_vars_network_reduction_RTC_pres
      \\ first_x_assum (irule_at Any)
      \\ simp[no_undefined_vars_chor_to_network])
QED

Theorem projection_top_reflection_junkcong:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ dvarsOf c = []
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection_top conf s c (procsOf c)) epn
   ⇒ ∃epn0 epn1 epn2 c' s'.
       (reduction conf)^* epn epn2 ∧
       compile_rel conf epn2 (compile_network_alt epn0) ∧
       fix_network epn0 ∧ free_fix_names_network epn0 = [] ∧
       no_undefined_vars_network epn0 ∧
       (reduction conf)^* epn0 (compile_network conf epn1) ∧
       trans_s (s,c) (s',c') ∧
       junkcong {new_fv s c} (project_choice (new_fv s c) s' c' (procsOf c)) epn1 ∧
       compile_network_ok s' c' (procsOf c)
Proof
  rw [projection_def,projection_top_def,endpoint_to_choiceTheory.compile_network_def] >>
  qmatch_asmsub_abbrev_tac ‘RTC _ (compile_network a1)’ >>
  qspecl_then [‘conf’,‘a1’] assume_tac compile_network_reduction_alt >>
  dxrule payloadConfluenceTheory.payload_confluence >>
  disch_then drule >>
  impl_tac >-
   (simp[] >>
    rw [Abbr ‘a1’,endpoints_compile_network_choice_aux,
        endpoints_compile_network_chor,
        endpoints_compile_network_payload,
        payload_closureProofTheory.compile_network_endpoints,
        procsOf_all_distinct]) >>
  strip_tac >>
  goal_assum dxrule >>
  unabbrev_all_tac >>
  gvs[GSYM projection_def,GSYM projection_top_def,GSYM endpoint_to_choiceTheory.compile_network_def] >>
  drule_all projection_reflection_junkcong >>
  rpt strip_tac >>
  rpt(goal_assum drule) >>
  gvs[project_choice_def]
QED

Theorem projection_reflection_aux:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ dvarsOf c = []
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection conf s c (procsOf c)) epn
   ⇒ ∃epn0 epn1 c' s'.
       compile_rel conf epn (compile_network_alt epn0) ∧
       fix_network epn0 ∧ free_fix_names_network epn0 = [] ∧
       no_undefined_vars_network epn0 ∧
       (reduction conf)^* epn0 epn1 ∧
      compile_network_ok s' c' (procsOf c) ∧
      trans_s (s,c) (s',c') ∧
      BISIM_REL (trans conf) (projection conf s' c' (procsOf c)) (compile_network_alt epn1)
Proof
  rw [] >>
  drule_all_then strip_assume_tac projection_reflection_junkcong >>
  goal_assum drule >> goal_assum drule >>
  goal_assum drule >> goal_assum drule >>
  goal_assum drule >> goal_assum drule >>
  fs[projection_def,endpoint_to_choiceTheory.compile_network_def] >>
  fs[project_choice_def,compile_rel_def] >>
  drule junkcong_compile_to_payload >>
  disch_then(qspec_then ‘conf’ strip_assume_tac) >>
  drule_then(qspec_then ‘conf’ assume_tac) junkcong_bisim >>
  irule compile_network_alt_fully_abstract >> simp[fix_network_compile_network] >>
  conj_tac >-
   (irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (drule_then (mp_tac o GSYM) junkcong_no_undefined_vars_network >> rw[] >>
    irule no_undefined_vars_chor_to_network >>
    metis_tac[trans_s_trans,no_undefined_vars_trans_s_pres]) >>
  conj_tac >-
   (irule dvarsOf_imp_free_fix_names_network >>
    dxrule_then assume_tac dvarsOf_nil_trans_s >>
    gs[]) >>
  conj_tac >-
   (drule junkcong_free_fix_names_network >>
    qmatch_goalsub_abbrev_tac ‘free_fix_names_network pp’ >>
    ‘free_fix_names_network pp = []’ suffices_by  rw[] >>
    UNABBREV_ALL_TAC >>
    irule dvarsOf_imp_free_fix_names_network >>
    dxrule_then assume_tac dvarsOf_nil_trans_s >>
    gs[]) >>
  irule BISIM_TRANS >>
  first_x_assum (irule_at Any) >>
  irule BISIM_SYM >>
  qpat_abbrev_tac ‘fv1 = gen_fresh_name _’ >>
  qpat_abbrev_tac ‘fv2 = gen_fresh_name _’ >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ a1 a2’ >>
  ‘~MEM fv1 (free_var_names_network a1) ∧ ~MEM fv2 (free_var_names_network a1)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          match_mp_tac (compile_network_support |> ONCE_REWRITE_RULE[MONO_NOT_EQ]) >>
          match_mp_tac (projection_free_variables_SUBSET |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          match_mp_tac(MATCH_MP IMAGE_SUBSET (SPEC_ALL free_variables_variables) |> REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) >>
          imp_res_tac trans_s_variables_mono >>
          match_mp_tac(IMAGE_SUBSET |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(PURE_REWRITE_CONV[SUBSET_DEF,Once MONO_NOT_EQ]))) |> MP_CANON) >>
          goal_assum drule >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM projection_variables_eq] >>
          simp[gen_fresh_name_same]) >-
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[endpoint_to_choiceProofTheory.MEM_free_vars_compile_network'] >>
          simp[gen_fresh_name_same] >>
          match_mp_tac(CONTRAPOS(SPEC_ALL free_var_names_var_names_network)) >>
          simp[gen_fresh_name_same])
      ) >>
  ‘~MEM fv1 (free_var_names_network a2) ∧ ~MEM fv2 (free_var_names_network a2)’
    by(unabbrev_all_tac >>
       conj_asm1_tac >>
         (dep_rewrite.DEP_ONCE_REWRITE_TAC[free_var_names_compile_to_payload_network] >>
          conj_tac >- simp[choice_free_network_compile_network_fv] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[MEM_free_vars_compile_network'] >>
          conj_tac >> match_mp_tac gen_fresh_nameE >>
          simp[projection_variables_eq] >>
          metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
                    IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET])) >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a1’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘restrict_network (λx. x ≠ fv1 ∧ x ≠ fv2) a2’ >>
  conj_tac >-
   (match_mp_tac BISIM_SYM >> match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM perm_network'] >>
  conj_tac >-
    (MAP_EVERY qunabbrev_tac [‘fv1’,‘fv2’] >>
     simp[gen_fresh_name_same] >>
     match_mp_tac gen_fresh_nameE >>
     simp[projection_variables_eq] >>
     metis_tac[free_var_names_var_names_network,SUBSET_DEF,SUBSET_TRANS,
               IMAGE_SUBSET,trans_s_variables_mono,projection_variables_SUBSET]) >>
  qmatch_goalsub_abbrev_tac ‘BISIM_REL _ (restrict_network _ a1) (restrict_network _ a2)’ >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a1’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[] >>
    qunabbrev_tac ‘a1’ >> simp[MEM_perm_network] >>
    rw[perm1_def]) >>
  match_mp_tac BISIM_SYM >>
  match_mp_tac BISIM_TRANS >>
  qexists_tac ‘a2’ >>
  conj_tac >-
   (match_mp_tac restrict_network_bisim >> simp[]) >>
  MAP_EVERY qunabbrev_tac [‘a1’,‘a2’] >>
  match_mp_tac BISIM_SYM >>
  simp[perm_network_bisim]
QED

Theorem BISIM_REL_reduction_RTC:
  ∀conf q p p'.
    (reduction conf)^* p p' ∧ BISIM_REL (trans conf)  p q
    ⇒ ∃q'. (reduction conf)^* q q' ∧ BISIM_REL (trans conf) p' q'
Proof
  strip_tac
  \\ ‘∀p p'. (reduction conf)^* p p'
             ⇒ ∀q. BISIM_REL (trans conf)  p q
                   ⇒ ∃q'. (reduction conf)^* q q' ∧
                          BISIM_REL (trans conf) p' q'’
  suffices_by metis_tac[]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw[]
  >- metis_tac[RTC_REFL]
  >- (gs[payloadSemTheory.reduction_def]
      \\ drule (BISIM_REL_cases  |> SPEC_ALL |>  EQ_IMP_RULE  |> fst)
      \\ disch_then (qspec_then ‘LTau’ assume_tac)
      \\ gs[] \\ pop_assum drule \\ rw []
      \\ last_x_assum drule \\ rw[]
      \\ pop_assum (irule_at Any)
      \\ irule RTC_TRANS
      \\ metis_tac[payloadSemTheory.reduction_def])
QED

Theorem projection_reflection:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ dvarsOf c = []
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection conf s c (procsOf c)) epn
   ⇒ ∃epn' c' s'.
       (reduction conf)^* epn epn' ∧
      trans_s (s,c) (s',c') ∧
      BISIM_REL (trans conf) (projection conf s' c' (procsOf c)) epn' ∧
      compile_network_ok s' c' (procsOf c)
Proof
  rw[] \\ drule_all projection_reflection_aux
  \\ rw[] \\ fs[compile_rel_def]
  \\ drule_then drule to_closure_preservation
  \\ impl_tac >- simp[]
  \\ rw[] \\ drule BISIM_REL_reduction_RTC
  \\ disch_then (qspec_then ‘epn’ mp_tac)
  \\ impl_tac >- simp[BISIM_SYM]
  \\ rw[] \\ gs[compile_rel_def]
  \\ metis_tac[BISIM_TRANS,BISIM_SYM]
QED

Theorem REPN_projection:
  ∀conf s c l. REPN (projection conf s c l)
Proof
  rw [projection_def]
  \\ qmatch_goalsub_abbrev_tac ‘compile_network conf epn’
  \\ ‘REPN epn’
    by (rw [Abbr‘epn’]
        \\ qmatch_goalsub_abbrev_tac ‘compile_network epn’
        \\ ‘REPN epn’ by rw [Abbr‘epn’,chor_REPN_compile_network]
        \\ qpat_x_assum ‘Abbrev _’ kall_tac
        \\ fs [endpoint_to_choiceTheory.compile_network_def]
        \\ qmatch_goalsub_abbrev_tac ‘compile_network_fv fv epn’
        \\ pop_assum kall_tac
        \\ pop_assum mp_tac
        \\ map_every qid_spec_tac [‘fv’,‘epn’]
        \\ Induct \\ rw []
        \\ fs [endpointCongTheory.REPN_def,
               endpoint_to_choiceTheory.compile_network_fv_def]
        \\ Cases_on ‘epn’
        \\ fs [endpointCongTheory.REPN_def,
               endpoint_to_choiceTheory.compile_network_fv_def,
               var_names_network_def])
  \\ qpat_x_assum ‘Abbrev _’ kall_tac
  \\ Induct_on ‘epn’
  \\ fs [endpointCongTheory.REPN_def,
         payloadCongTheory.REPN_def,
         compile_network_def]
  >- EVAL_TAC
  \\ rw []
  \\ Cases_on ‘epn’ \\ fs [endpointCongTheory.REPN_def]
  \\ rw [endpoint_to_payloadTheory.compile_network_def,
         payload_closureTheory.compile_network_alt_def,
         payloadCongTheory.REPN_def]
QED

Theorem REPN_projection_top:
  ∀conf s c l. REPN (projection_top conf s c l)
Proof
  rw[projection_top_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_goalsub_rename_tac ‘compile_network_fv fv _’
  \\ map_every qid_spec_tac [‘s’,‘c’,‘l’]
  \\ Induct \\ EVAL_TAC \\ rw [] \\ EVAL_TAC
QED

Theorem endpoints_projection:
  ∀conf s c l. MAP FST (endpoints (projection conf s c l)) = l
Proof
  rw [projection_def,
      endpoints_compile_network_payload,
      endpoints_compile_network_choice,
      endpoints_compile_network_closure,
      endpoints_compile_network_chor]
QED

Theorem endpoints_projection_top:
  ∀conf s c l. MAP FST (endpoints (projection_top conf s c l)) = l
Proof
  rw [projection_top_def,
      endpoints_compile_network_payload,
      endpoints_compile_network_choice,
      endpoints_compile_network_closure',
      endpoints_compile_network_chor]
QED

Theorem projection_empty_q:
  ∀conf s c l. empty_q (projection conf s c l)
Proof
  rw [projection_def,
      endpoint_to_choiceTheory.compile_network_def,
      empty_q_to_payload,
      empty_q_to_closure,
      compile_network_fv_empty_q,
      compile_network_empty_q]
QED

Theorem projection_top_empty_q:
  ∀conf s c l. empty_q (projection_top conf s c l)
Proof
  rw [projection_top_def,
      endpoint_to_choiceTheory.compile_network_def,
      empty_q_to_payload,
      empty_q_to_closure',
      compile_network_fv_empty_q,
      compile_network_empty_q]
QED

Theorem empty_q_normalised_network:
  ∀n. empty_q n ⇒ normalised_network n
Proof
  Induct \\ rw[payloadPropsTheory.empty_q_def,
               payloadLangTheory.normalised_network_def,
               payloadLangTheory.normalised_def,
               payloadLangTheory.normalise_queues_def]
QED

Theorem projection_net_end:
  ∀l conf s. net_end (projection conf s Nil l)
Proof
  Induct \\ EVAL_TAC
  \\ rw [] \\ pop_assum (ASSUME_TAC o EVAL_RULE)
  \\ rw []
QED

Theorem net_end_net_find:
  ∀n p.
   net_end n ∧ net_has_node n p
   ⇒ ∃s. net_find p n = SOME (NEndpoint p s Nil)
Proof
  Induct \\ EVAL_TAC
  \\ rw []
  >- (fs [net_has_node_IS_SOME_net_find]
      \\ first_x_assum drule_all
      \\ fs [IS_SOME_EXISTS])
  >- (Cases_on ‘IS_SOME (net_find p n)’ \\ fs []
      \\ fs [GSYM net_has_node_IS_SOME_net_find]
      \\ res_tac
      \\ rw [] \\ fs [])
  \\ Cases_on ‘e’ \\ fs [payloadLangTheory.net_end_def]
QED

Theorem chor_deadlock_freedom':
  ∀c s c' s'.
   no_undefined_vars (s,c) ∧
   no_self_comunication c  ∧
   dvarsOf c = [] ∧
   trans_s (s,c) (s',c')
   ⇒ c' = Nil ∨ ∃τ l s'' c''. trans (s',c') (τ,l) (s'',c'')
Proof
  simp[trans_s_def] >>
  Induct_on ‘RTC’ >>
  rw[]
  >- (drule_then drule deadlockFreedomTheory.chor_deadlock_freedom >>
      rw[not_finish_def,DISJ_EQ_IMP] >>
      Cases_on ‘∃x. c = Call x’
      >- gvs[dvarsOf_def] >>
      gvs[] >>
      metis_tac[]) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  Cases_on ‘c'''’ >> simp[] >>
  drule_then drule deadlockFreedomTheory.chor_deadlock_freedom >>
  impl_tac >-
   (rw[not_finish_def] >>
    spose_not_then strip_assume_tac >>
    gvs[] >>
    qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
    gvs[]) >>
  strip_tac >>
  gvs[GSYM trans_s_def] >>
  conj_tac >- metis_tac[no_undefined_vars_trans_pres] >>
  conj_tac >- metis_tac[PAIR,FST,SND,no_self_comunication_trans_pres] >>
  metis_tac[PAIR,FST,SND,dvarsOf_nil_trans]
QED

Theorem BISIM_REL_reduction_TC:
  ∀conf q p p'.
    (reduction conf)^+ p p' ∧ BISIM_REL (trans conf)  p q
    ⇒ ∃q'. (reduction conf)^+ q q' ∧ BISIM_REL (trans conf) p' q'
Proof
  strip_tac
  \\ ‘∀p p'. (reduction conf)^+ p p'
             ⇒ ∀q. BISIM_REL (trans conf)  p q
                   ⇒ ∃q'. (reduction conf)^+ q q' ∧
                          BISIM_REL (trans conf) p' q'’
  suffices_by metis_tac[]
  \\ ho_match_mp_tac TC_INDUCT
  \\ rw[]
  >- (gs[payloadSemTheory.reduction_def]
      \\ drule (BISIM_REL_cases  |> SPEC_ALL |>  EQ_IMP_RULE  |> fst)
      \\ disch_then (qspec_then ‘LTau’ assume_tac)
      \\ gs[] \\ pop_assum drule \\ rw []
      \\ irule_at Any (cj 1 TC_RULES)
      \\ metis_tac[payloadSemTheory.reduction_def])
  >- metis_tac [TC_RULES,BISIM_REL_def,BISIM_TRANS]
QED

Theorem net_end_projection:
  ∀s c l conf.
    net_end (compile_network s c l) ⇒ net_end (projection conf s c l)
Proof
  rw[projection_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_goalsub_rename_tac ‘compile_network_fv fv epn’
  \\ pop_assum mp_tac
  \\ Induct_on ‘epn’
  \\ EVAL_TAC \\ rw [] \\ EVAL_TAC
  \\ Cases_on ‘e’ \\ gs [net_end_def] \\ EVAL_TAC
QED

Theorem net_end_eq_projection_nil:
  ∀s c l conf.
    net_end (projection conf s c l)
    ⇒ projection conf s c l = projection conf s Nil l
Proof
  rw[projection_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_goalsub_rename_tac ‘compile_network_fv fv’
  \\ qmatch_goalsub_rename_tac ‘compile_network_fv fv' (compile_network s Nil l)’
  \\ Induct_on ‘l’
  \\ EVAL_TAC \\ rw [] \\ EVAL_TAC
  >- (qmatch_goalsub_abbrev_tac ‘nub' ll’
      \\ ‘ll = []’ suffices_by simp[nub'_def]
      \\ UNABBREV_ALL_TAC
      \\ qmatch_goalsub_abbrev_tac ‘written_var_names_endpoint ee’
      \\ ‘fix_endpoint ee’
        by (UNABBREV_ALL_TAC
            \\ qmatch_goalsub_rename_tac ‘fix_endpoint (compile_endpoint ep)’
            \\ rpt (pop_assum kall_tac)
            \\ Induct_on ‘ep’ \\ EVAL_TAC \\ rw[])
      \\ Cases_on ‘ee’
      \\ gs [payloadLangTheory.net_end_def,
             compile_endpoint_def,fix_endpoint_def,written_var_names_endpoint_def])
  >- (qmatch_goalsub_abbrev_tac ‘ee = _’
      \\ Cases_on ‘ee’
      \\ gs [payloadLangTheory.net_end_def,
             compile_endpoint_def,fix_endpoint_def,written_var_names_endpoint_def])
QED

Theorem projection_deadlock_freedom_lemma:
  compile_network_ok s c (procsOf c) ∧ conf.payload_size > 0 ∧
  no_undefined_vars (s,c) ∧ dvarsOf c = [] ∧
  (reduction conf)^* (projection conf s c (procsOf c)) epn ∧
  no_self_comunication c
  ⇒
  (∃s. BISIM_REL (trans conf) (projection conf s Nil (procsOf c)) epn)
  ∨ ∃epn''. reduction conf epn epn''
Proof
  rpt strip_tac >>
  drule projection_reflection >>
  rpt(disch_then drule) >>
  rpt strip_tac >>
  reverse(qpat_x_assum ‘RTC _ _ _’ (strip_assume_tac o REWRITE_RULE[Once RTC_cases]))
  >- metis_tac[] >>
  rveq >>
  drule chor_deadlock_freedom' >>
  rpt(disch_then drule) >>
  rpt strip_tac
  >- metis_tac[] >>
  drule proj_has_reduction' >>
  impl_tac
  >- (drule dvarsOf_nil_trans_s >>
      drule no_undefined_vars_trans_s_pres >>
      drule procsOf_trans_s_SUBSET >>
      simp[procsOf_all_distinct]) >>
  rw[]
  >- (disj2_tac >>
      gvs[projection_def] >>
      drule_then assume_tac (cj 1 TC_RULES) >>
      drule_at (Pos last) endpoint_to_choiceProofTheory.compile_network_preservation_TC >>
      qmatch_goalsub_abbrev_tac ‘var_names_network nn’ >>
      disch_then (qspec_then ‘gen_fresh_name (var_names_network nn)’ mp_tac) >>
      impl_tac >- simp[Abbr‘nn’,gen_fresh_name_same,
                       endpoints_compile_network_chor,procsOf_all_distinct] >>
      rw[] >>
      drule endpoint_to_payloadProofTheory.compile_network_preservation_TC >>
      disch_then drule >> simp[choice_free_network_compile_network_fv] >>
      rw[] >>
      drule compile_network_preservation_alt_TC >>
      impl_tac
      >- (rw[fix_network_compile_network,Abbr‘nn’]
          >- (irule_at Any dvarsOf_imp_free_fix_names_network >>
              metis_tac[FST,SND,dvarsOf_nil_trans_s])
          >- metis_tac [no_undefined_vars_trans_s_pres,
                        no_undefined_vars_chor_to_network])>>
      rw []>>gs[Abbr‘nn’,endpoint_to_choiceTheory.compile_network_def]>>
      qmatch_asmsub_abbrev_tac ‘BISIM_REL _ nn’>>
      drule_all BISIM_REL_reduction_TC>>simp[Once TC_CASES1]>>metis_tac[])
  >- metis_tac[net_end_projection,net_end_eq_projection_nil]
QED

Theorem endpoints_trans_lift:
  ∀epn2 l1 l2.
    trans conf (NEndpoint p s e) α (NEndpoint p' s' e') ∧
    endpoints epn2 = l1 ++ [(p,s,e)] ++ l2 ⇒
    ∃epn3.
      trans conf epn2 α epn3 ∧
      endpoints epn3 = l1 ++ [(p',s',e')] ++ l2
Proof
  Induct_on ‘epn2’ >>
  gvs[payloadLangTheory.endpoints_def] >>
  rw[APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)]
  >- (res_tac >>
      irule_at (Pos hd) payloadSemTheory.trans_par_l >>
      goal_assum drule >>
      rw[payloadLangTheory.endpoints_def])
  >- (res_tac >>
      irule_at (Pos hd) payloadSemTheory.trans_par_r >>
      goal_assum drule >>
      rw[payloadLangTheory.endpoints_def]) >>
  gvs[APPEND_EQ_SING] >>
  goal_assum drule >>
  simp[payloadLangTheory.endpoints_def]
QED

Theorem EVERY_Nil_trans:
  ∀conf epn1 α epn2.
    trans conf epn1 α epn2 ∧
    EVERY (λ(p,s,e). e = Nil) (endpoints epn1)
    ⇒
    ∃p d q. α = LReceive p d q ∧ MEM q (MAP FST (endpoints epn1)) ∧
            EVERY (λ(p,s,e). e = Nil) (endpoints epn2)
Proof
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac payloadSemTheory.trans_ind >>
  rw[payloadLangTheory.endpoints_def] >>
  metis_tac[]
QED

(* TODO: move *)
Definition partners_payload_def:
  (partners_payload Nil = [])
∧ (partners_payload (Send p v n e) = p::partners_payload e)
∧ (partners_payload (Receive p v d e) = p::partners_payload e)
∧ (partners_payload (IfThen v e1 e2) = partners_payload e1 ++ partners_payload e2)
∧ (partners_payload (Let v f vl e) = partners_payload e)
∧ (partners_payload (Fix dv e) = partners_payload e)
∧ (partners_payload (Call dv) = [])
∧ (partners_payload (Letrec dv vars e1) = partners_payload e1)
∧ (partners_payload (FCall dv vars) = [])
End

Definition partners_payload_closure_def:
  partners_payload_closure (Closure vars1 (fs1,bds1) e1) =
  (partners_payload e1 ++
   FLAT(MAP partners_payload_closure (MAP SND fs1)))
Termination
  WF_REL_TAC ‘inv_image $< (closure_size)’ >>
  rw[payloadLangTheory.closure_size_def,MEM_MAP] >>
  Cases_on ‘y’ >>
  imp_res_tac payloadLangTheory.closure_size_MEM >>
  DECIDE_TAC
End

Theorem payload_bisim_nil_lemma:
  ∀epn1 epn2.
  BISIM_REL (trans conf) epn1 epn2 ∧
  conf.payload_size > 0 ∧
  no_undefined_vars_network epn2 ∧
  letrec_network epn2 ∧
  EVERY (λ(p,s,e). e = Nil) (endpoints epn1) ∧
  EVERY (λ(p,s,e). ∀q. q ∈ FRANGE(s.queues) ⇒ EVERY (λx. final x ∨ intermediate x) q) (endpoints epn2) ∧
  EVERY (λ(p,s,e). ~MEM p (partners_payload e)) (endpoints epn2) ∧
  EVERY (λ(p,s,e). (∀f n.
                        MEM (f,n) (arities e) ⇒
                        ∃vs fs bds e'.
                          ALOOKUP s.funs f = SOME(Closure vs (fs,bds) e') ∧
                          LENGTH vs = n
                   )) (endpoints epn2)
  ⇒
  EVERY (λ(p,s,e). e = Nil) (endpoints epn2)
Proof
  rw[] >>
  CCONTR_TAC >>
  gvs[EVERY_MEM,EXISTS_MEM] >>
  pairarg_tac >>
  gvs[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  gvs[no_undefined_vars_network_def,letrec_network_def] >> 
  rename1 ‘(p,s,e)’ >>
  Cases_on ‘e’ >>
  gvs[payloadLangTheory.free_var_names_endpoint_def,FDOM_FLOOKUP,letrec_endpoint_def,
      DISJ_IMP_THM,FORALL_AND_THM,partners_payload_def]
  >- ((* Send: epn2 can do an LSend, but epn1 can't; ergo, contradiction*)
     drule_at (Pos last) endpoints_trans_lift >>
     rename1 ‘Send _ vv n’ >>
     rename1 ‘FLOOKUP _ _ = SOME dd’ >>
     Cases_on ‘LENGTH dd − n > conf.payload_size’
     >- (disch_then(resolve_then (Pos hd) drule payloadSemTheory.trans_send_intermediate_payload) >>
         disch_then drule >>
         disch_then drule >>
         strip_tac >>
         gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
         last_x_assum drule >>
         strip_tac >>
         drule EVERY_Nil_trans >>
         impl_tac >- rw[EVERY_MEM] >>
         rw[])
     >- (disch_then(resolve_then (Pos hd) drule payloadSemTheory.trans_send_last_payload) >>
         disch_then (drule_at (Pos last)) >>
         disch_then (qspec_then ‘conf’ mp_tac) >>
         impl_tac >- fs[] >>
         strip_tac >>
         gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
         last_x_assum drule >>
         strip_tac >>
         drule EVERY_Nil_trans >>
         impl_tac >- rw[EVERY_MEM] >>
         rw[]))
  >- ((* Receive: more involved *)
      rename1 ‘Receive q d l’ >>
      Cases_on ‘qlk s.queues q’
      >- (drule_at (Pos last) endpoints_trans_lift >>
          disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_enqueue) >>
          disch_then(qspecl_then [‘q’,‘[2w]’,‘conf’] mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
          last_x_assum drule >>
          strip_tac >>
          drule_at (Pos last) endpoints_trans_lift >>
          disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_dequeue_intermediate_payload) >>
          disch_then(qspecl_then [‘[]’,‘[2w]’,‘conf’] mp_tac) >>
          impl_tac >- simp[payloadLangTheory.intermediate_def] >>
          strip_tac >>
          gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
          qpat_x_assum ‘∀l q. trans conf epn3 l q ⇒ _’ drule >>
          strip_tac >>
          drule EVERY_Nil_trans >>
          impl_tac >- (imp_res_tac EVERY_Nil_trans >>
                       gvs[EVERY_MEM]) >>
          rw[]) >>
      rename1 ‘m::_’ >>
      ‘final m ∨ intermediate m’
        by(first_x_assum(match_mp_tac o MP_CANON) >>
           gvs[payloadLangTheory.qlk_def,payloadLangTheory.fget_def,AllCaseEqs(),
               FRANGE_FLOOKUP,PULL_EXISTS] >>
           goal_assum drule >> simp[])
      >- (drule_at (Pos last) endpoints_trans_lift >>
          disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_dequeue_last_payload) >>
          disch_then (drule_at (Pos last)) >>
          disch_then (drule_at (Pos last)) >>
          disch_then (qspec_then ‘conf’ mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
          last_x_assum drule >>
          strip_tac >>
          drule EVERY_Nil_trans >>
          impl_tac >- rw[EVERY_MEM] >>
          rw[])
      >- (drule_at (Pos last) endpoints_trans_lift >>
          disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_dequeue_intermediate_payload) >>
          disch_then (drule_at (Pos last)) >>
          disch_then (drule_at (Pos last)) >>
          disch_then (qspec_then ‘conf’ mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
          last_x_assum drule >>
          strip_tac >>
          drule EVERY_Nil_trans >>
          impl_tac >- rw[EVERY_MEM] >>
          rw[])
     )
  >- ((* IfThen: epn2 can do an LTau, but epn1 can't *)
     drule_at (Pos last) endpoints_trans_lift >>
     rename1 ‘IfThen vv’ >>
     rename1 ‘FLOOKUP _ _ = SOME dd’ >>
     Cases_on ‘dd = [1w]’
     >- (rveq >>
         disch_then(resolve_then (Pos hd) drule payloadSemTheory.trans_if_true) >>
         disch_then(qspec_then ‘conf’ strip_assume_tac) >>
         gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
         last_x_assum drule >>
         strip_tac >>
         drule EVERY_Nil_trans >>
         impl_tac >- rw[EVERY_MEM] >>
         rw[])
     >- (rveq >>
         disch_then(resolve_then (Pos hd) drule payloadSemTheory.trans_if_false) >>
         disch_then(qspec_then ‘conf’ strip_assume_tac) >>
         gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
         last_x_assum drule >>
         strip_tac >>
         drule EVERY_Nil_trans >>
         impl_tac >- rw[EVERY_MEM] >>
         rw[])
     )
  >- ((* Let: epn2 can do an LTau, but epn1 can't *)
     drule_at (Pos last) endpoints_trans_lift >>
     rename1 ‘Let _ f l’ >>
     disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_let) >>
     disch_then(qspec_then ‘conf’ mp_tac) >>
     impl_tac
     >- (gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,SUBSET_DEF,FDOM_FLOOKUP,IS_SOME_EXISTS]) >>
     strip_tac >>
     gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
     last_x_assum drule >>
     strip_tac >>
     drule EVERY_Nil_trans >>
     impl_tac >- rw[EVERY_MEM] >>
     rw[])
  >- ((* Letrec: epn2 can do an LTau, but epn1 can't *)
     drule_at (Pos last) endpoints_trans_lift >>
     rename1 ‘Letrec f vs e’ >>
     disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_letrec) >>
     disch_then(qspec_then ‘conf’ mp_tac) >>
     impl_tac
     >- (gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,SUBSET_DEF,FDOM_FLOOKUP,IS_SOME_EXISTS,
             arities_def]) >>
     strip_tac >>
     gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
     last_x_assum drule >>
     strip_tac >>
     drule EVERY_Nil_trans >>
     impl_tac >- rw[EVERY_MEM] >>
     rw[])
  >- ((* FCall: epn2 can do an LTau, but epn1 can't *)
     gvs[arities_def] >>     
     drule_at (Pos last) endpoints_trans_lift >>
     disch_then(resolve_then (Pos hd) mp_tac payloadSemTheory.trans_call) >>
     disch_then drule >>
     disch_then(qspec_then ‘conf’ mp_tac) >>
     impl_tac
     >- (gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,SUBSET_DEF,FDOM_FLOOKUP,IS_SOME_EXISTS,
             arities_def]) >>
     strip_tac >>
     gvs[Once BISIM_REL_cases,FORALL_AND_THM] >>
     last_x_assum drule >>
     strip_tac >>
     drule EVERY_Nil_trans >>
     impl_tac >- rw[EVERY_MEM] >>
     rw[])
QED

Theorem projection_deadlock_freedom:
  compile_network_ok s c (procsOf c) ∧ conf.payload_size > 0 ∧
  no_undefined_vars (s,c) ∧ dvarsOf c = [] ∧
  (reduction conf)^* (projection conf s c (procsOf c)) epn ∧
  no_self_comunication c
  ⇒
  EVERY (λ(p,s,e). e = Nil) (endpoints epn)
  ∨ ∃epn''. reduction conf epn epn''
Proof
  cheat
QED
        
val _ = export_theory ()

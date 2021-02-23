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
  payload_closureProofTheory.compile_network_preservation_alt

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
  ∀c s conf fv.
    dvarsOf c = []
    ⇒ free_fix_names_network
        (endpoint_to_payload$compile_network conf
           (compile_network_fv fv
              (compile_network s c (procsOf c)))) = []
Proof
  rw [] \\ qmatch_goalsub_abbrev_tac ‘compile_network _ _ l’
  \\ pop_assum kall_tac
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
  ∀s c conf fv.
    no_undefined_vars (s,c)
    ⇒ no_undefined_vars_network
        (endpoint_to_payload$compile_network conf
             (compile_network_fv fv
                (compile_network s c (procsOf c))))
Proof
  rw [] \\ qmatch_goalsub_abbrev_tac ‘compile_network _ _ l’
  \\ pop_assum kall_tac
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
          (MAP (λ(d,f). (d,perm_closure v1 v2 f)) funs, perm_bindings v1 v2 bind) e
Termination
  WF_REL_TAC ‘inv_image $< (closure_size o SND o SND)’ >>
  rw[payloadLangTheory.closure_size_def] >> imp_res_tac ALOOKUP_MEM >>
  imp_res_tac closure_size_MEM >>
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

Theorem perm1_cancel[simp]:
  perm1 v1 v2 (perm1 v1 v2 x) = x
Proof
  rw[perm1_def] >> fs[CaseEq "bool"] >> fs[]
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

Theorem perm_endpoint_cancel[simp]:
  perm_endpoint v1 v2 (perm_endpoint v1 v2 e) = e
Proof
  Induct_on ‘e’ >>
  rw[perm_endpoint_def] >>
  rw[MAP_MAP_o,o_DEF]
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
     UNABBREV_ALL_TAC >> simp[payloadLangTheory.state_component_equality]) >-
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
     simp[payloadLangTheory.state_component_equality]) >-
   (rw[perm_endpoint_dsubst,payloadSemTheory.trans_fix,perm_endpoint_def]) >-

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
  !e fv fv1. MEM fv1 (free_var_names_endpoint (compile_endpoint fv e))
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
  (perm_state fv1 fv2 ss) with bindings := x = ss with bindings := x
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
  Induct_on ‘n’ >> rw[compile_network_fv_def,compile_network_def,perm_network_def,var_names_network_def,payloadPropsTheory.junkcong_refl,perm_endpoint] >-
    metis_tac[payloadPropsTheory.junkcong_par] >>
  rename1 ‘NEndpoint s (perm_state _ _ ss)’ >>
  match_mp_tac payloadPropsTheory.junkcong_trans >>
  qexists_tac ‘NEndpoint s ((perm_state fv1 fv2 ss) with bindings := ((perm_state fv1 fv2 ss).bindings \\ fv1)) (compile_endpoint (compile_endpoint fv2 e))’ >>
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
  simp[payloadPropsTheory.junkcong_refl]
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
  Induct_on ‘n’ >> rw[compile_network_fv_def,compile_network_def,perm_network_def,var_names_network_def,payloadPropsTheory.junkcong_refl,perm_endpoint,restrict_network_def] >>
  rw[payloadLangTheory.state_component_equality,fmap_eq_flookup,FLOOKUP_DRESTRICT] >>
  rw[perm_state_FLOOKUP,perm1_def]
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

Theorem projection_preservation:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
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
  fs[project_choice_def] >>
  drule junkcong_compile_to_payload >>
  disch_then(qspec_then ‘conf’ strip_assume_tac) >>
  match_mp_tac BISIM_SYM >>
  drule_then(qspec_then ‘conf’ assume_tac) junkcong_bisim >>
  match_mp_tac BISIM_TRANS >>
  dxrule_then assume_tac BISIM_SYM >>
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


(* Enpoints names are preserved over the endpoint_to_choice
   compilation step (generic version)
*)
Theorem endpoints_compile_network_epn_aux:
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
Theorem endpoints_compile_network_epn:
  ∀epn.
   MAP FST (endpoints (endpoint_to_choice$compile_network epn)) = MAP FST (endpoints epn)
Proof
  rw [endpoint_to_choiceTheory.compile_network_def,endpoints_compile_network_epn_aux]
QED


(* split_sel can only remove processes *)
Triviality MEM_partners_endpoint_split_sel:
  ∀(c : chor) p l b x r.
   split_sel p l c = SOME (b,r) ∧
   no_self_comunication c ∧
   MEM x (partners_endpoint (project' p r))
   ⇒ MEM x (partners_endpoint (project' p c))
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
  ∀(c : chor) p x.
    no_self_comunication c ∧
    MEM x (partners_endpoint (project' p c))
    ⇒ MEM x (procsOf c)
Proof
  Induct
  \\ rw [procsOf_def,
         chor_to_endpointTheory.project_def,
         partners_endpoint_def,
         nub'_def]
  \\ (fn (asms,goal) =>
      goal
      |> dest_disj |> fst
      |> (fn t => (ASM_CASES_TAC t \\ fs []) (asms,goal)))
  \\ fs [MEM_FILTER,MEM_nub',no_self_comunication_def]
  >- metis_tac [] >- metis_tac []
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
  ∀l (c : chor) s.
    partners_network (compile_network s c l)
    = FLAT (MAP (\proc. partners_endpoint (project' proc c)) l)
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
   = EVERY I (MAP (λp . ¬MEM p (partners_endpoint (project' p c))) l)
Proof
  Induct \\ rw [chor_to_endpointTheory.compile_network_gen_def,
                endpoint_ok_def,
                endpoints_def]
QED

(* The projected process is not mentioned withing its code
   (because no self-communication is allowed)
*)
Theorem MEM_partners_endpoint_project:
  ∀(c : chor) p. no_self_comunication c ⇒ ¬MEM p (partners_endpoint (project' p c))
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

Theorem projection_reflection_junkcong:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection conf s c (procsOf c)) epn
   ⇒ ∃epn' c' s'.
      (reduction conf)^* epn (compile_network conf epn') ∧
      trans_s (s,c) (s',c') ∧
      junkcong {new_fv s c} (project_choice (new_fv s c) s' c' (procsOf c)) epn'
Proof
  rw [projection_def]
  \\ first_assum (mp_then Any mp_tac from_payload_reflection)
  \\ impl_tac \\ rw []
  >- rw [endpoints_compile_network_epn,
         endpoints_compile_network_chor,
         procsOf_all_distinct]
  >- rw [choice_free_network_compile_network_fv,
         endpoint_to_choiceTheory.compile_network_def]
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
  \\ rw []
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
  \\ qpat_assum ‘(reduction conf)^* epn _’ (mp_then Any (drule_then assume_tac) RTC_SPLIT)
  \\ qspec_then ‘p3'’ drule endpointPropsTheory.qcong_sym
  \\ disch_then (mp_then Any mp_tac endpointPropsTheory.empty_queue_qcong)
  \\ rw [compile_network_empty_q]
  \\ first_x_assum (mp_then Any drule junkcong_trans)
  \\ rw [] \\ drule empty_q_junkcong
  \\ impl_tac
  >- rw [compile_network_fv_empty_q,compile_network_empty_q]
  \\ rw []
  \\ drule_then (qspec_then ‘conf’ assume_tac) empty_q_to_payload
  \\ rpt(goal_assum drule)
QED

Theorem projection_reflection:
  ∀s c epn conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ∧ (reduction conf)^* (projection conf s c (procsOf c)) epn
   ⇒ ∃epn' c' s'.
      (reduction conf)^* epn epn' ∧
      trans_s (s,c) (s',c') ∧
      BISIM_REL (trans conf) (projection conf s' c' (procsOf c)) epn'
Proof
  rw [] >>
  drule_all_then strip_assume_tac projection_reflection_junkcong >>
  goal_assum drule >>
  goal_assum drule >>
  fs[projection_def,endpoint_to_choiceTheory.compile_network_def] >>
  fs[project_choice_def] >>
  drule junkcong_compile_to_payload >>
  disch_then(qspec_then ‘conf’ strip_assume_tac) >>
  match_mp_tac BISIM_SYM >>
  drule_then(qspec_then ‘conf’ assume_tac) junkcong_bisim >>
  match_mp_tac BISIM_TRANS >>
  dxrule_then assume_tac BISIM_SYM >>
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
  \\ rw []
  \\ Cases_on ‘epn’ \\ fs [endpointCongTheory.REPN_def]
  \\ rw [endpoint_to_payloadTheory.compile_network_def,
         payloadCongTheory.REPN_def]
QED

Theorem endpoints_compile_network_payload:
  ∀epn conf.
   MAP FST (endpoints (endpoint_to_payload$compile_network conf epn)) = MAP FST (endpoints epn)
Proof
  Induct \\ rw [endpoint_to_payloadTheory.compile_network_def,
                endpointPropsTheory.endpoints_def,
                payloadLangTheory.endpoints_def]
QED

Theorem endpoints_projection:
  ∀conf s c l. MAP FST (endpoints (projection conf s c l)) = l
Proof
  rw [projection_def,
      endpoints_compile_network_payload,
      endpoints_compile_network_epn,
      endpoints_compile_network_chor]
QED

Theorem projection_empty_q:
  ∀conf s c l. empty_q (projection conf s c l)
Proof
  rw [projection_def,
      endpoint_to_choiceTheory.compile_network_def,
      empty_q_to_payload,
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

val _ = export_theory ()

open preamble

open  projectionTheory projectionProofTheory
      chorSemTheory deadlockFreedomTheory
      choreoUtilsTheory

open comms_ffi_propsTheory

open  smallStepTheory

open  payloadLangTheory payloadCongTheory payloadPropsTheory
      payload_to_cakemlTheory payload_to_cakemlProofTheory

val _ = new_theory "compilationProof";

Overload smSt[local] = “bigSmallEquiv$to_small_st”
Overload smEv[local] = “smallStep$small_eval”
Overload stepr[local] = “smallStep$e_step_reln”

Definition empty_funs_def:
  empty_funs NNil = T
∧ empty_funs (NPar n1 n2) = (empty_funs n1 ∧ empty_funs n2)
∧ empty_funs (NEndpoint p s e) = (s.funs = [])
End

Theorem empty_funs_to_payload:
  ∀epn conf. empty_funs (compile_network conf epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

Theorem empty_funs_to_closure:
  ∀epn. empty_funs epn ⇒ empty_funs (compile_network_alt epn)
Proof
  Induct
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC \\ gs[projection_def,endpoint_to_choiceTheory.compile_network_def]
QED

Theorem empty_funs_projection:
  ∀l c s conf.
    empty_funs (projection conf s c l)
Proof
  simp[projection_def,empty_funs_to_closure,empty_funs_to_payload]
QED

Theorem empty_funs_net_find:
  ∀epn p e.
    empty_funs epn
    ∧ net_find p epn = SOME e
    ⇒ empty_funs e
Proof
  Induct   \\ EVAL_TAC
  \\ rw [] \\ EVAL_TAC
  \\ simp[]
  \\ Cases_on ‘net_find p epn’
  \\ Cases_on ‘net_find p epn'’
  \\ gs[] \\ metis_tac[]
QED

Theorem EP_nodenames_to_closure:
  ∀ep l. fix_endpoint ep
       ⇒ EP_nodenames (compile_endpoint l ep) = EP_nodenames ep
Proof
  Induct   \\ EVAL_TAC
  \\ rw [] \\  simp[SUBSET_OF_INSERT]
  \\ Cases_on ‘ALOOKUP l s’ \\ gs[EP_nodenames_def]
QED

Theorem network_nodenames_to_closure:
  ∀epn.
    fix_network epn
    ⇒ network_nodenames (compile_network_alt epn) = network_nodenames epn
Proof
  Induct
  >- EVAL_TAC
  >- (rw[fix_network_NPar
        , payload_closureTheory.compile_network_alt_def
        , network_nodenames_def])
  >- (EVAL_TAC \\ rw[regexpTheory.LIST_UNION_def,EP_nodenames_to_closure])
QED

Theorem EP_nodenames_to_payload:
  ∀ep. choice_free_endpoint ep ⇒
       EP_nodenames (compile_endpoint ep) = EP_nodenames ep
Proof
  Induct  \\ EVAL_TAC
  \\ rw [] \\ simp[SUBSET_OF_INSERT]
QED

Theorem network_nodenames_to_payload:
  ∀epn conf.
    choice_free_network epn
    ⇒ network_nodenames (compile_network conf epn) = network_nodenames epn
Proof
  Induct  \\ EVAL_TAC \\ rw[EP_nodenames_to_payload]
QED

Theorem EP_nodenames_to_choice:
  ∀e (fv:string). EP_nodenames (compile_endpoint fv e) = EP_nodenames e
Proof
  Induct  \\ EVAL_TAC \\ rw []
  \\ metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,SUBSET_TRANS]
QED

Theorem network_nodenames_to_choice:
  ∀epn fv.
    network_nodenames (compile_network_fv fv epn) = network_nodenames epn
Proof
  Induct  \\ EVAL_TAC \\ rw [EP_nodenames_to_choice]
QED

Triviality set_FILTER_eq_DELETE:
  ∀l p. set (FILTER (λy. p ≠ y) l) = set l DELETE p
Proof
  Induct \\ rw[DELETE_INSERT]
QED

Theorem EP_nodenames_to_endpoint:
 ∀p l c.
   project_ok p l c
   ⇒ EP_nodenames (project' p l c) ⊆ set(procsOf c) DELETE p
Proof
  ho_match_mp_tac chor_to_endpointTheory.project_ind
  \\ rw[chor_to_endpointTheory.project_def,procsOf_def,nub'_def]
  \\ gs[]
  \\ simp[set_FILTER_eq_DELETE,set_nub',DELETE_INSERT]
  \\ simp[Once DELETE_COMM]
  \\ TRY (gs[SUBSET_DEF] \\ Cases_on ‘x = p1’ \\ simp[] \\ NO_TAC)
  >- (Cases_on ‘split_sel p p1 c’ \\ gs[]
      \\ Cases_on ‘split_sel p p1 c'’ \\ gs[SUBSET_DEF]
      \\ Cases_on ‘x’ \\ Cases_on ‘x'’
      \\ dxrule chor_to_endpointProofTheory.split_sel_procsOf
      \\ drule chor_to_endpointProofTheory.split_sel_procsOf
      \\ Cases_on ‘q’ \\ Cases_on ‘q'’ \\ gs[] \\ rw[]
      \\ gs[SUBSET_DEF])
  >- (Cases_on ‘split_sel p p1 c’ \\ gs[]
      \\ Cases_on ‘split_sel p p1 c'’ \\ gs[SUBSET_DEF]
      \\ Cases_on ‘x'’ \\ Cases_on ‘x’
      \\ dxrule chor_to_endpointProofTheory.split_sel_procsOf
      \\ drule chor_to_endpointProofTheory.split_sel_procsOf
      \\ Cases_on ‘q’ \\ Cases_on ‘q'’ \\ gs[] \\ rw[]
      \\ gs[SUBSET_DEF])
  >- (Cases_on ‘ALOOKUP l dn’ \\ gs[]
      \\ Cases_on ‘MEM p x’ \\ gs[])
QED

(* network_nodenames is bounded by procsOf, the main reason it can not be an equality is that
   they might be processes that do not communicate at all *)
Theorem network_nodenames_to_endpoint:
  ∀l c s.
    compile_network_ok s c l
    ⇒ network_nodenames (compile_network s c l) ⊆ set(chorSem$procsOf c)
Proof
  Induct
  >- (EVAL_TAC \\ simp[])
  >- (EVAL_TAC \\ rw[] \\ gs[]
      \\ metis_tac [SUBSET_TRANS,EP_nodenames_to_endpoint,SUBSET_DELETE])
QED

Theorem network_nodenames_projection:
  ∀l s c conf.
    compile_network_ok s c l
    ⇒ network_nodenames (projection conf s c l) ⊆ set (chorSem$procsOf c)
Proof
  rw [projection_def,endpoint_to_choiceTheory.compile_network_def
     , fix_network_compile_network
     , choice_free_network_compile_network_fv
     , network_nodenames_to_closure
     , network_nodenames_to_payload
     , network_nodenames_to_choice
     , network_nodenames_to_endpoint]
QED

Theorem EP_nodenames_projection:
  ∀l s c p conf es ec.
  compile_network_ok s c l ∧
  net_find p (projection conf s c l) = SOME (NEndpoint p es ec)
  ⇒ EP_nodenames ec ⊆ set(procsOf c) DELETE p
Proof
  rw[projection_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_asmsub_rename_tac ‘compile_network_fv fv _’
  \\ ‘fix_network (compile_network conf
                   (compile_network_fv fv (compile_network s c l)))’
     by simp[fix_network_compile_network]
  \\ ‘choice_free_network (compile_network_fv fv (compile_network s c l))’
     by simp[choice_free_network_compile_network_fv]
  \\ rpt (pop_assum mp_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘ec’,‘es’,‘conf’,‘p’,‘c’,‘s’,‘l’]
  \\ Induct \\ EVAL_TAC \\ rw[]
  >- rw[EP_nodenames_to_closure,
        EP_nodenames_to_payload,
        EP_nodenames_to_choice,
        EP_nodenames_to_endpoint]
  >- metis_tac [fix_network_def]
QED

Theorem net_filter_NNil_net_find_NONE:
  ∀epn p q.
    p ≠ q ∧ net_filter q epn = NNil
    ⇒ net_find p epn = NONE
Proof
  Induct \\ EVAL_TAC \\ rw[] \\ simp[net_find_def]
  \\ metis_tac []
QED

Theorem net_find_net_filter:
∀epn p q.
  p ≠ q ⇒ net_find p (net_filter q epn) = net_find p epn
Proof
  Induct \\ EVAL_TAC \\ rw[] \\ simp[net_find_def]
  \\ drule_all net_filter_NNil_net_find_NONE \\ rw[]
QED

Theorem net_has_node_net_filter:
  ∀epn p q.
    p ≠ q ⇒ net_has_node (net_filter p epn) q = net_has_node epn q
Proof
  rw [net_has_node_IS_SOME_net_find,IS_SOME_EXISTS,net_find_net_filter]
QED

Theorem compilation_preservation_junkcong:
  ∀s1 (c1 : chor) s2 c2    (* Chor *)
   conf p pSt1 pCd1 pEPN1  (* Payload *)
   cSt1 vs1 env1 cvs.      (* CakeML *)
   (* projection assumptions *)
   trans_s (s1,c1) (s2,c2) ∧
   compile_network_ok s1 c1 (procsOf c1) ∧
   conf.payload_size > 0   ∧
   no_undefined_vars (s1,c1) ∧
   dvarsOf c1 = [] ∧
   (* The process being consider *)
   pEPN1 = projection conf s1 c1 (procsOf c1) ∧
   net_find p pEPN1  = SOME (NEndpoint p pSt1 pCd1 ) ∧
   cSt1.ffi.oracle = comms_ffi_oracle conf ∧
   cSt1.ffi.ffi_state = (p,pSt1.queues,net_filter p pEPN1) ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr conf pSt1 pCd1 ∧
   env_asm env1 conf cvs ∧
   enc_ok conf env1 (letfuns pCd1) vs1
   ⇒ ∃s3 c3                   (* Chor *)
      cEPN3                   (* Choice *)
      cEPN4 pSt4 pCd4         (* Payload *)
      cSt4  env4 vs4          (* CakeML *)
      env5 sst51 sst52 e5 l5.
      trans_s (s2,c2) (s3,c3) ∧
      junkcong {new_fv s1 c1}
               (project_choice (new_fv s1 c1) s3 c3 (procsOf c1))
               cEPN3 ∧
      compile_rel conf cEPN4 (compile_network_alt (compile_network conf cEPN3)) ∧
      net_find p cEPN4 = SOME (NEndpoint p pSt4 pCd4) ∧
      stepr꙳
        (env1, smSt cSt1, Exp (compile_endpoint conf vs1 pCd1), [])
        (env5, sst51, e5, l5) ∧
      stepr꙳
        (env4, smSt cSt4, Exp (compile_endpoint conf vs4 pCd4), [])
        (env5, sst52, e5, l5) ∧
    ffi_eq conf (SND sst51).ffi_state (SND sst52).ffi_state ∧
    FST sst51 = FST sst52 ∧
    (SND sst51).oracle    = (SND sst52).oracle ∧
    (SND sst51).io_events = (SND sst52).io_events ∧
    cpEval_valid conf p env4 pSt4 pCd4 (net_filter p cEPN4) vs4 cvs cSt4 ∧
    cSt4.ffi.ffi_state = (p,pSt4.queues,net_filter p cEPN4) ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p pSt4 pCd4) ⇒ ffi_has_node nd cSt4.ffi.ffi_state)
Proof
  rw []
  \\ drule_all projection_preservation_junkcong
  \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac ‘net_find p pEPN1’
  \\ rename1 ‘net_find p pEPN3’
  \\ drule_then (qspec_then ‘p’ mp_tac) net_find_IS_SOME_reduction_pres_IMP
  \\ impl_tac >- rw [IS_SOME_EXISTS]
  \\ rw [IS_SOME_EXISTS] \\ drule net_find_NEndpoint
  \\ rw []
  \\ drule network_forward_correctness_reduction
  \\ rpt (disch_then (first_assum o (mp_then Any mp_tac)))
  \\ disch_then (qspecl_then [‘vs1’,‘cvs’,‘env1’] mp_tac)
  \\ impl_tac \\ rw []
  >- rw [Abbr‘pEPN1’,REPN_projection]
  >- rw [net_has_node_IS_SOME_net_find,IS_SOME_EXISTS]
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection,empty_funs_def]
      \\ gs[regexpTheory.LIST_UNION_def])
  >- (rw [ffi_has_node_def]
      \\ irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffRL net_has_node_net_filter))
      \\ conj_tac
      >- (CCONTR_TAC \\ gs[Abbr‘pEPN1’] \\ drule_all EP_nodenames_projection
          \\ rw[SUBSET_DEF] \\ metis_tac [])
      >- (simp[Abbr‘pEPN1’,net_has_node_MEM_endpoints,endpoints_projection]
          \\ drule_all EP_nodenames_projection \\ rw [SUBSET_DEF]))
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
QED

(* TODO: move *)
Theorem net_find_is_some_lemma:
  ∀cs p s c:chor s2 c2:chor conf fv1 fv2.
  IS_SOME(net_find p ((compile_network conf
                      (compile_network_fv fv1
                       (compile_network s c cs))))) =
  IS_SOME(net_find p ((compile_network conf
                      (compile_network_fv fv2
                       (compile_network s2 c2 cs)))))
Proof
  Induct >>
  fs[projection_def,chor_to_endpointTheory.compile_network_gen_def,
     endpoint_to_choiceTheory.compile_network_def,
     endpoint_to_choiceTheory.compile_network_fv_def,
     endpoint_to_payloadTheory.compile_network_def,
     net_find_def
    ] >>
  rw[]
QED

Theorem net_find_projection_IS_SOME:
  ∀cs p s c s1 c2 conf.
  IS_SOME(net_find p (projection conf s c cs)) =
  IS_SOME(net_find p (projection conf s1 c2 cs))
Proof
  rw[net_find_is_some_lemma,projection_def,
     endpoint_to_choiceTheory.compile_network_def]
QED

Theorem compilation_preservation:
  ∀s1 (c1 : chor) s2 c2    (* Chor *)
   conf p pSt1 pCd1 pEPN1  (* Payload *)
   cSt1 vs1 env1.          (* CakeML *)
   trans_s (s1,c1) (s2,c2) ∧
   compile_network_ok s1 c1 (procsOf c1) ∧
   conf.payload_size > 0   ∧
   no_undefined_vars (s1,c1) ∧
   (* new stuff *)
   pEPN1 = projection conf s1 c1 (procsOf c1) ∧
   net_find p pEPN1  = SOME (NEndpoint p pSt1 pCd1 ) ∧
   cSt1.ffi.oracle = comms_ffi_oracle conf ∧
   cSt1.ffi.ffi_state = (p,pSt1.queues,net_filter p pEPN1) ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr pSt1 pCd1 ∧ (* Should be true by construction *)
   sem_env_cor conf pSt1 env1 ∧
   enc_ok conf env1 (letfuns pCd1) vs1
   ⇒ ∃s3 c3             (* Chor *)
      cEPN3             (* Choice *)
      pSt3 pCd3         (* Payload *)
      mc cSt2 env2 vs2. (* CakeML *)
      trans_s (s2,c2) (s3,c3) ∧
      BISIM_REL (trans conf) (projection conf s3 c3 (procsOf c1)) cEPN3 ∧
      net_find p cEPN3 = SOME (NEndpoint p pSt3 pCd3) ∧
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) env1
                        [compile_endpoint conf vs1 pCd1])
        (evaluate (cSt2 with clock := mc) env2
                        [compile_endpoint conf vs2 pCd3])
Proof
  rw []
  \\ drule_all projection_preservation
  \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac ‘net_find p pEPN1’
  \\ qmatch_goalsub_abbrev_tac ‘net_find p pEPN3’
  \\ drule_then (qspec_then ‘p’ mp_tac) net_find_IS_SOME_reduction_pres_IMP
  \\ impl_tac >- rw [IS_SOME_EXISTS]
  \\ rw [IS_SOME_EXISTS] \\ drule net_find_NEndpoint
  \\ rw []
  \\ drule network_forward_correctness_reduction'
  \\ rpt (disch_then (first_assum o (mp_then Any mp_tac)))
  \\ impl_tac \\ rw []
  >- rw [Abbr‘pEPN1’,REPN_projection]
  >- (irule net_wf_ALL_DISTINCT_eq
      \\ rw [Abbr‘pEPN1’,endpoints_projection,procsOf_all_distinct])
  >- (irule empty_q_normalised_network \\ rw [Abbr‘pEPN1’,projection_empty_q])
  >- rw [Abbr‘pEPN1’,projection_empty_q,empty_q_padded]
  >- rw [net_has_node_IS_SOME_net_find,IS_SOME_EXISTS]
  \\ asm_exists_tac
  \\ fs []
QED

Theorem compile_network_fv_net_end:
  ∀l fv s. net_end (compile_network_fv fv (compile_network s chorLang$Nil l))
Proof
  Induct \\ EVAL_TAC
  \\ rw [] \\ pop_assum (ASSUME_TAC o EVAL_RULE)
  \\ rw []
QED

Theorem compile_network_conf_net_end:
  ∀n conf. net_end n ⇒ net_end (compile_network conf n)
Proof
  Induct \\ EVAL_TAC \\ rw []
  \\ pop_assum (ASSUME_TAC o EVAL_RULE)
  \\ Cases_on ‘e’ \\ EVAL_TAC \\ rw []
  \\ pop_assum (ASSUME_TAC o EVAL_RULE)
  \\ rw []
QED

Theorem compilation_deadlock_freedom:
  ∀s1 (c1 : chor)          (* Chor *)
   conf p pSt1 pCd1 pEPN1  (* Payload *)
   cSt1 vs1 env1.          (* CakeML *)
   compile_network_ok s1 c1 (procsOf c1) ∧
   conf.payload_size > 0   ∧
   no_undefined_vars (s1,c1) ∧
   (* new stuff *)
   pEPN1 = projection conf s1 c1 (procsOf c1) ∧
   net_find p pEPN1  = SOME (NEndpoint p pSt1 pCd1 ) ∧
   cSt1.ffi.oracle = comms_ffi_oracle conf ∧
   cSt1.ffi.ffi_state = (p,pSt1.queues,net_filter p pEPN1) ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr pSt1 pCd1 ∧ (* Should be true by construction *)
   sem_env_cor conf pSt1 env1 ∧
   enc_ok conf env1 (letfuns pCd1) vs1
   ⇒ ∃mc cSt2. (* CakeML *)
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) env1
                        [compile_endpoint conf vs1 pCd1])
        (cSt2 with clock := mc,Rval [Conv NONE []])
Proof
  rw []
  \\ imp_res_tac chor_to_endpointProofTheory.compile_network_ok_no_self_comunication
  \\ drule_all chor_deadlock_freedom
  \\ rw []
  \\ drule compilation_preservation_junkcong
  \\ rpt (disch_then drule)
  \\ rw []
  \\ pop_assum drule_all
  \\ rw []
  \\ drule chor_to_endpointProofTheory.trans_s_nil
  \\ rw []
  \\ drule endpointPropsTheory.junkcong_net_end
  \\ disch_then (mp_tac o fst o EQ_IMP_RULE)
  \\ impl_tac >- fs[compile_network_fv_net_end]
  \\ rw []
  \\ drule_then (qspec_then ‘conf’ assume_tac) compile_network_conf_net_end
  \\ drule_then (qspec_then ‘p’ mp_tac) net_end_net_find
  \\ impl_tac >- fs [net_has_node_IS_SOME_net_find]
  \\ rw []
  \\ qpat_x_assum ‘cEval_equiv _ _ _’ (ASSUME_TAC o EVAL_RULE)
  \\ asm_exists_tac \\ fs []
QED

val _ = export_theory ()

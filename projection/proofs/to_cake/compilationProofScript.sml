open preamble

open  projectionTheory projectionProofTheory
      chorSemTheory deadlockFreedomTheory

open  payloadLangTheory payloadCongTheory payloadPropsTheory
      payload_to_cakemlProofTheory

val _ = new_theory "compilationProof";

Theorem compilation_preservation_junkcong:
  ∀s1 (c1 : chor) s2 c2    (* Chor *)
   conf p pSt1 pCd1 pEPN1  (* Payload *)
   cSt1 vs1 env1.          (* CakeML *)
   trans_s (s1,c1) (s2,c2) ∧
   compile_network_ok s1 c1 (procsOf c1) ∧
   conf.payload_size > 0   ∧
   no_undefined_vars (s1,c1) ∧
   no_self_comunication c1  ∧
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
      junkcong {new_fv s1 c1}
               (project_choice (new_fv s1 c1) s3 c3 (procsOf c1))
               cEPN3 ∧
      net_find p (compile_network conf cEPN3) = SOME (NEndpoint p pSt3 pCd3) ∧
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) env1
                        [compile_endpoint conf vs1 pCd1])
        (evaluate (cSt2 with clock := mc) env2
                        [compile_endpoint conf vs2 pCd3])
Proof
  rw []
  \\ drule_all projection_preservation_junkcong
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
   no_self_comunication c1  ∧
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
   no_self_comunication c1  ∧
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

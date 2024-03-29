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

Theorem empty_funs_to_closure':
  ∀epn. empty_funs epn ⇒ empty_funs (compile_network epn)
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

Theorem empty_funs_projection_top:
  ∀l c s conf.
    empty_funs (projection_top conf s c l)
Proof
  simp[projection_top_def,empty_funs_to_closure',empty_funs_to_payload]
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

Theorem network_nodenames_to_closure':
  ∀epn.
    fix_network epn
    ⇒ network_nodenames (compile_network epn) = network_nodenames epn
Proof
  Induct
  >- EVAL_TAC
  >- (rw[fix_network_NPar
        , payload_closureTheory.compile_network_def
        , network_nodenames_def])
  >- (EVAL_TAC \\ rw[regexpTheory.LIST_UNION_def,EP_nodenames_to_closure]
      \\ qmatch_goalsub_abbrev_tac ‘FOLDL f ee l’
      \\ ‘EP_nodenames (FOLDL f ee l) = EP_nodenames ee’
        suffices_by (UNABBREV_ALL_TAC \\ simp[EP_nodenames_to_closure])
      \\ simp[Abbr‘f’] \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘ee’,‘l’]
      \\ Induct \\ gs[])
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

Theorem network_nodenames_projection_top:
  ∀l s c conf.
    compile_network_ok s c l
    ⇒ network_nodenames (projection_top conf s c l) ⊆ set (chorSem$procsOf c)
Proof
  rw [projection_top_def,endpoint_to_choiceTheory.compile_network_def
     , fix_network_compile_network
     , choice_free_network_compile_network_fv
     , network_nodenames_to_closure'
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

Theorem EP_nodenames_projection_top:
  ∀l s c p conf es ec.
  compile_network_ok s c l ∧
  net_find p (projection_top conf s c l) = SOME (NEndpoint p es ec)
  ⇒ EP_nodenames ec ⊆ set(procsOf c) DELETE p
Proof
  rw[projection_top_def,endpoint_to_choiceTheory.compile_network_def]
  \\ qmatch_asmsub_rename_tac ‘compile_network_fv fv _’
  \\ ‘fix_network (compile_network conf
                   (compile_network_fv fv (compile_network s c l)))’
     by simp[fix_network_compile_network]
  \\ ‘choice_free_network (compile_network_fv fv (compile_network s c l))’
     by simp[choice_free_network_compile_network_fv]
  \\ rpt (pop_assum mp_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘ec’,‘es’,‘conf’,‘p’,‘c’,‘s’,‘l’]
  \\ Induct \\ EVAL_TAC \\ rw[]
  >- (qmatch_goalsub_abbrev_tac ‘FOLDL f ee ll’
      \\ ‘EP_nodenames (FOLDL f ee ll) = EP_nodenames ee’
        suffices_by (UNABBREV_ALL_TAC
                     \\ rw[EP_nodenames_to_closure,
                           EP_nodenames_to_payload,
                           EP_nodenames_to_choice,
                           EP_nodenames_to_endpoint])
      \\ simp[Abbr‘f’] \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘ee’,‘ll’]
      \\ Induct \\ gs[])
  >- metis_tac [fix_network_def]
QED

Theorem empty_q_net_find:
  ∀epn p e.
    empty_q epn
    ∧ net_find p epn = SOME e
    ⇒ empty_q e
Proof
  Induct \\ EVAL_TAC \\ rw[]
  >- (gs[] \\ Cases_on ‘net_find p epn’
      \\ gs[] \\ metis_tac [])
  >- simp[empty_q_def]
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


Theorem letrec_network_rcong:
  ∀epn1 epn2.
    epn1 p≅ epn2
    ⇒ (letrec_network epn1 ⇔ letrec_network epn2)
Proof
  ho_match_mp_tac payload_rcong_ind
  \\ rw[letrec_network_def]
  >- (irule PERM_EVERY \\ rw[endpoints_def]
      \\ SIMP_TAC (std_ss++permLib.PERM_SIMPLE_ss) [])
  >- simp[endpoints_def]
QED

Theorem pletrec_vars_ok_to_closure':
  ∀epn p es ec.
  fix_network epn
  ∧ net_find p (compile_network epn) = SOME (NEndpoint p es ec)
  ⇒ pletrec_vars_ok ec
Proof
  Induct
  >- (EVAL_TAC \\ rw[])
  >- (rw[] \\ gs[payload_closureTheory.compile_network_def,net_find_def,fix_network_NPar]
      \\ Cases_on ‘net_find p (compile_network epn)’ \\ gs[] \\ metis_tac[])
  >- (rw[payload_closureTheory.compile_network_def,net_find_def]
      \\ qmatch_goalsub_abbrev_tac ‘FOLDL f ee ll’
      \\ ‘pletrec_vars_ok (FOLDL f ee ll) = pletrec_vars_ok ee’
         by (simp[Abbr‘f’] \\ rpt (pop_assum kall_tac)
             \\ map_every qid_spec_tac [‘ee’,‘ll’]
             \\ Induct \\ gs[])
      \\ simp[] \\ UNABBREV_ALL_TAC \\ pop_assum kall_tac
      \\ gs[fix_network_def,endpoints_def]
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ qmatch_goalsub_abbrev_tac ‘compile_endpoint l e’
      \\ ‘∀s. ALOOKUP l s = SOME vars ⇒ ALL_DISTINCT vars’ by simp[Abbr‘l’]
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘l’,‘e’]
      \\ Induct_on ‘e’
      \\ gs[payload_closureTheory.compile_endpoint_def,fix_endpoint_def]
      \\ rw [all_distinct_nub']
      >- metis_tac[] >- metis_tac[] >- metis_tac[] >- metis_tac[] >- metis_tac[]
      >- (first_x_assum irule \\ rw [] \\ simp [all_distinct_nub'] \\ metis_tac[])
      >- (Cases_on ‘ALOOKUP l s’ \\ gs[]))
QED

Theorem pletrec_vars_ok_to_closure:
  ∀epn p es ec.
  fix_network epn
  ∧ net_find p (compile_network_alt epn) = SOME (NEndpoint p es ec)
  ⇒ pletrec_vars_ok ec
Proof
  Induct
  >- (EVAL_TAC \\ rw[])
  >- (rw[] \\ gs[payload_closureTheory.compile_network_alt_def,net_find_def,fix_network_NPar]
      \\ Cases_on ‘net_find p (compile_network_alt epn)’ \\ gs[] \\ metis_tac[])
  >- (rw[payload_closureTheory.compile_network_alt_def,net_find_def]
      \\ gs[fix_network_def,endpoints_def]
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ qmatch_goalsub_abbrev_tac ‘compile_endpoint l e’
      \\ ‘∀s. ALOOKUP l s = SOME vars ⇒ ALL_DISTINCT vars’ by simp[Abbr‘l’]
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘l’,‘e’]
      \\ Induct_on ‘e’
      \\ gs[payload_closureTheory.compile_endpoint_def,fix_endpoint_def]
      \\ rw [all_distinct_nub']
      >- metis_tac[] >- metis_tac[] >- metis_tac[] >- metis_tac[] >- metis_tac[]
      >- (first_x_assum irule \\ rw [] \\ simp [all_distinct_nub'] \\ metis_tac[])
      >- (Cases_on ‘ALOOKUP l s’ \\ gs[]))
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
   cSt1.eval_state = NONE ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr conf pSt1 pCd1 ∧
   sem_env_cor conf pSt1 env1 cvs ∧
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
  >- (rw [cpEval_valid_def] \\  gs[sem_env_cor_def]
      >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
          \\ rw[Abbr‘pEPN1’,empty_funs_projection,empty_funs_def,funs_cpEval_valid_def])
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection,procsOf_all_distinct]))
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection,procsOf_all_distinct]))
      >- (‘empty_q (NEndpoint p pSt1 pCd1)’
          by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_empty_q]
          \\ gs[empty_q_def,normalised_def,normalise_queues_def]))
  >- (irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffLR letrec_network_rcong))
      \\ irule_at Any net_find_filter_cong
      \\ simp[Abbr‘pEPN1’,REPN_projection]
      \\ rw[projection_def,
            fix_network_compile_network,
            payload_closureProofTheory.letrec_network_compile_network_alt])
  >- (irule pletrec_vars_ok_to_closure \\ gs[Abbr‘pEPN1’,projection_def]
      \\ first_assum (irule_at Any) \\ simp[fix_network_compile_network])
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection,empty_funs_def])
  >- (‘empty_q (NEndpoint p pSt1 pCd1)’
        by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_empty_q]
      \\ gs[empty_q_def,normalised_def,normalise_queues_def])
  >- metis_tac[]
QED

Theorem compilation_preservation_junkcong_top:
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
   pEPN1 = projection_top conf s1 c1 (procsOf c1) ∧
   net_find p pEPN1  = SOME (NEndpoint p pSt1 pCd1 ) ∧
   cSt1.ffi.oracle = comms_ffi_oracle conf ∧
   cSt1.ffi.ffi_state = (p,pSt1.queues,net_filter p pEPN1) ∧
   cSt1.eval_state = NONE ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr conf pSt1 pCd1 ∧
   sem_env_cor conf pSt1 env1 cvs ∧
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
  \\ drule_all projection_top_preservation_junkcong
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
  >- rw [Abbr‘pEPN1’,REPN_projection_top]
  >- rw [net_has_node_IS_SOME_net_find,IS_SOME_EXISTS]
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def]
      \\ gs[regexpTheory.LIST_UNION_def])
  >- (rw [ffi_has_node_def]
      \\ irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffRL net_has_node_net_filter))
      \\ conj_tac
      >- (CCONTR_TAC \\ gs[Abbr‘pEPN1’] \\ drule_all EP_nodenames_projection_top
          \\ rw[SUBSET_DEF] \\ metis_tac [])
      >- (simp[Abbr‘pEPN1’,net_has_node_MEM_endpoints,endpoints_projection_top]
          \\ drule_all EP_nodenames_projection_top \\ rw [SUBSET_DEF]))
  >- (rw [cpEval_valid_def] \\  gs[sem_env_cor_def]
      >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
          \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def,funs_cpEval_valid_def])
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection_top,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection_top]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection_top,procsOf_all_distinct]))
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection_top,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection_top]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection_top,procsOf_all_distinct]))
      >- (‘empty_q (NEndpoint p pSt1 pCd1)’
          by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_top_empty_q]
          \\ gs[empty_q_def,normalised_def,normalise_queues_def]))
  >- (irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffLR letrec_network_rcong))
      \\ irule_at Any net_find_filter_cong
      \\ simp[Abbr‘pEPN1’,REPN_projection_top]
      \\ rw[projection_top_def,
            fix_network_compile_network,
            payload_closureProofTheory.letrec_network_compile_network])
  >- (irule pletrec_vars_ok_to_closure' \\ gs[Abbr‘pEPN1’,projection_top_def]
      \\ first_assum (irule_at Any) \\ simp[fix_network_compile_network])
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def])
  >- (‘empty_q (NEndpoint p pSt1 pCd1)’
        by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_top_empty_q]
      \\ gs[empty_q_def,normalised_def,normalise_queues_def])
  >- metis_tac[]
QED

Theorem compilation_preservation:
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
   cSt1.eval_state = NONE ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr conf pSt1 pCd1 ∧
   sem_env_cor conf pSt1 env1 cvs ∧
   enc_ok conf env1 (letfuns pCd1) vs1
   ⇒ ∃s3 c3                   (* Chor *)
      cEPN3                   (* Choice *)
      cEPN4 pSt4 pCd4         (* Payload *)
      cSt4  env4 vs4          (* CakeML *)
      env5 sst51 sst52 e5 l5.
      trans_s (s2,c2) (s3,c3) ∧
      BISIM_REL (trans conf) (projection conf s3 c3 (procsOf c1)) cEPN4 ∧
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
  \\ drule_all projection_preservation
  \\ rw []
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
  >- (rw [cpEval_valid_def] \\  gs[sem_env_cor_def]
      >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
          \\ rw[Abbr‘pEPN1’,empty_funs_projection,empty_funs_def,funs_cpEval_valid_def])
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection,procsOf_all_distinct]))
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection,procsOf_all_distinct]))
      >- (‘empty_q (NEndpoint p pSt1 pCd1)’
          by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_empty_q]
          \\ gs[empty_q_def,normalised_def,normalise_queues_def]))
  >- (irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffLR letrec_network_rcong))
      \\ irule_at Any net_find_filter_cong
      \\ simp[Abbr‘pEPN1’,REPN_projection]
      \\ rw[projection_def,
            fix_network_compile_network,
            payload_closureProofTheory.letrec_network_compile_network_alt])
  >- (irule pletrec_vars_ok_to_closure \\ gs[Abbr‘pEPN1’,projection_def]
      \\ first_assum (irule_at Any) \\ simp[fix_network_compile_network])
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection,empty_funs_def])
  >- (‘empty_q (NEndpoint p pSt1 pCd1)’
        by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_empty_q]
      \\ gs[empty_q_def,normalised_def,normalise_queues_def])
  >- metis_tac[]
QED

Theorem compilation_preservation_top:
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
   pEPN1 = projection_top conf s1 c1 (procsOf c1) ∧
   net_find p pEPN1  = SOME (NEndpoint p pSt1 pCd1 ) ∧
   cSt1.ffi.oracle = comms_ffi_oracle conf ∧
   cSt1.ffi.ffi_state = (p,pSt1.queues,net_filter p pEPN1) ∧
   cSt1.eval_state = NONE ∧
   (* payload_to_cakeml assumptions *)
   pSt_pCd_corr conf pSt1 pCd1 ∧
   sem_env_cor conf pSt1 env1 cvs ∧
   enc_ok conf env1 (letfuns pCd1) vs1
   ⇒ ∃s3 c3                   (* Chor *)
      cEPN3                   (* Choice *)
      cEPN4 pSt4 pCd4         (* Payload *)
      cSt4  env4 vs4          (* CakeML *)
      env5 sst51 sst52 e5 l5.
      trans_s (s2,c2) (s3,c3) ∧
      BISIM_REL (trans conf) (projection conf s3 c3 (procsOf c1)) cEPN4 ∧
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
  \\ drule_all projection_top_preservation
  \\ rw []
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
  >- rw [Abbr‘pEPN1’,REPN_projection_top]
  >- rw [net_has_node_IS_SOME_net_find,IS_SOME_EXISTS]
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def]
      \\ gs[regexpTheory.LIST_UNION_def])
  >- (rw [ffi_has_node_def]
      \\ irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffRL net_has_node_net_filter))
      \\ conj_tac
      >- (CCONTR_TAC \\ gs[Abbr‘pEPN1’] \\ drule_all EP_nodenames_projection_top
          \\ rw[SUBSET_DEF] \\ metis_tac [])
      >- (simp[Abbr‘pEPN1’,net_has_node_MEM_endpoints,endpoints_projection_top]
          \\ drule_all EP_nodenames_projection_top \\ rw [SUBSET_DEF]))
  >- (rw [cpEval_valid_def] \\  gs[sem_env_cor_def]
      >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
          \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def,funs_cpEval_valid_def])
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection_top,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection_top]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection_top,procsOf_all_distinct]))
      >- (rw[ffi_state_cor_def,ffi_wf_def]
          >- (irule net_wf_filter \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [Abbr‘pEPN1’,endpoints_projection_top,procsOf_all_distinct])
          >- (irule not_net_has_node_net_filter \\ simp[Abbr‘pEPN1’,REPN_projection_top]
              \\ irule net_wf_ALL_DISTINCT_eq
              \\ rw [endpoints_projection_top,procsOf_all_distinct]))
      >- (‘empty_q (NEndpoint p pSt1 pCd1)’
          by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_top_empty_q]
          \\ gs[empty_q_def,normalised_def,normalise_queues_def]))
  >- (irule (SIMP_RULE std_ss [AND_IMP_INTRO] (iffLR letrec_network_rcong))
      \\ irule_at Any net_find_filter_cong
      \\ simp[Abbr‘pEPN1’,REPN_projection_top]
      \\ rw[projection_top_def,
            fix_network_compile_network,
            payload_closureProofTheory.letrec_network_compile_network])
  >- (irule pletrec_vars_ok_to_closure' \\ gs[Abbr‘pEPN1’,projection_top_def]
      \\ first_assum (irule_at Any) \\ simp[fix_network_compile_network])
  >- (last_x_assum (mp_then Any mp_tac empty_funs_net_find)
      \\ rw[Abbr‘pEPN1’,empty_funs_projection_top,empty_funs_def])
  >- (‘empty_q (NEndpoint p pSt1 pCd1)’
        by metis_tac [empty_q_net_find,Abbr‘pEPN1’,projection_top_empty_q]
      \\ gs[empty_q_def,normalised_def,normalise_queues_def])
  >- metis_tac[]
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

(* Not true as stated
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
 *)

val _ = export_theory ()

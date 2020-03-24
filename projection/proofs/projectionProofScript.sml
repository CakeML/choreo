open preamble choreoUtilsTheory chorPropsTheory
     projectionTheory payloadPropsTheory
     endpointPropsTheory


open chorSemTheory endpointLangTheory

open chor_to_endpointTheory
     endpoint_to_choiceTheory
     endpoint_to_payloadTheory
open chor_to_endpointProofTheory
     endpoint_to_choiceProofTheory
     endpoint_to_payloadProofTheory

val _ = new_theory "projectionProof";

val to_choice_preservation =
  endpoint_to_choiceProofTheory.compile_network_preservation;

val to_endpoint_preservation =
  chor_to_endpointProofTheory.compile_network_preservation;

val to_payload_preservation =
  endpoint_to_payloadProofTheory.compile_network_preservation;

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
       first_x_assum(qspec_then `s` mp_tac) >> intLib.COOPER_TAC) >>
  conj_tac >- (spose_not_then strip_assume_tac >> fs[]) >>
  pop_assum kall_tac >>
  `!s'. MEM s' l ==> STRLEN s' < STRLEN(gen_fresh_name (s::l))`
    by(simp[gen_fresh_name_def] >>
       qid_spec_tac `s` >>
       Induct_on `l` >> rw[] >> rw[] >>
       res_tac >>
       first_x_assum(qspec_then `s` mp_tac) >> intLib.COOPER_TAC) >>
  spose_not_then strip_assume_tac >> res_tac >>
  fs[]
QED

(* endpoint_to_choice compilation step generates a choice_free_network *)
Theorem choice_free_network_compile_network_fv:
  ∀epn fv. choice_free_network (compile_network_fv fv epn)
Proof
  Induct \\ rw [choice_free_network_def,compile_network_fv_def]
  \\ Induct_on ‘e’ \\ rw [choice_free_endpoint_def,
                          endpoint_to_choiceTheory.compile_endpoint_def]
QED

Theorem projection_preservation:
  ∀s c s'' c'' conf.
   compile_network_ok s c (procsOf c)
   ∧ conf.payload_size > 0
   ∧ trans_s (s,c) (s'',c'')
   ∧ no_undefined_vars (s,c)
   ∧ no_self_comunication c
   ⇒ ∃s''' c''' epn.
      trans_s (s'',c'') (s''',c''') ∧
      junkcong {new_fv s c}
               (project_choice (new_fv s c) s''' c''' (procsOf c))
               epn ∧
      (reduction conf)^* (projection conf s c (procsOf c))
                         (compile_network conf epn)
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
  \\ qmatch_goalsub_abbrev_tac ‘compile_network conf to_choice’
  \\ irule to_payload_preservation
  \\ fs [Abbr‘to_choice’]
  \\ rw [choice_free_network_compile_network_fv]
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

(* nub' preserves membership *)
Theorem MEM_nub':
  ∀l x. MEM x (nub' l) = MEM x l
Proof
  Induct
  \\ rw [nub'_def]
  \\ Cases_on ‘x=h’ \\ fs [MEM_FILTER]
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

(* TODO: move to chorPropstheory *)
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

(* Makes sure a network has every message queue empty (epn version) *)
Definition empty_q_epn_def:
  empty_q_epn endpointLang$NNil = T
∧ empty_q_epn (NPar n1 n2)     = (empty_q_epn n1 ∧ empty_q_epn n2)
∧ empty_q_epn (NEndpoint _ s _) = (s.queue = [])
End

(* Makes sure a network has every message queue empty (payload version) *)
Definition empty_q_payload_def:
  empty_q_payload payloadLang$NNil = T
∧ empty_q_payload (NPar n1 n2)     = (empty_q_payload n1 ∧ empty_q_payload n2)
∧ empty_q_payload (NEndpoint _ s _) = (s.queue = [])
End

(* If all queues are empty a network is only queue congruent (qcong)
   with itself (epn version)
*)
Theorem empty_queue_qcong_epn:
  ∀epn epn'.
   qcong epn epn' ∧
   empty_q_epn epn
   ⇒ epn' = epn
Proof
  Induct
  \\ ONCE_REWRITE_TAC [endpointPropsTheory.qcong_cases] \\ rw [empty_q_epn_def]
  >- (metis_tac [endpointPropsTheory.qcong_rules,qcong_nil_rel_nil])
  >- (metis_tac [endpointPropsTheory.qcong_rules,qcong_nil_rel_nil])
  >- (drule qcong_par_rel_par_sym \\ rw []
      \\ imp_res_tac endpointPropsTheory.qcong_sym
      \\ fs [])
  >- (drule_then drule endpointPropsTheory.qcong_trans
      \\ disch_then (mp_then Any mp_tac qcong_par_rel_par)
      \\ rw [])
  >- (drule endpointPropsTheory.qcong_sym
      \\ disch_then (mp_then Any mp_tac qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule qcong_IMP_qrel
      \\ rw [] \\ drule qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule qcong_bindings_eq \\ fs [])
  >- (drule_then drule endpointPropsTheory.qcong_trans
      \\ disch_then (mp_then Any mp_tac qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule_then drule endpointPropsTheory.qcong_trans
      \\ rw [] \\ drule qcong_IMP_qrel
      \\ rw [] \\ drule qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule qcong_bindings_eq \\ fs [])
  \\ fs []
QED

(* If all queues are empty a network is only queue congruent (qcong)
   with itself (payload version)
*)
Theorem empty_queue_qcong_payload:
  ∀epn epn'.
   qcong epn epn' ∧
   empty_q_payload epn
   ⇒ epn' = epn
Proof
  Induct
  \\ ONCE_REWRITE_TAC [payloadPropsTheory.qcong_cases] \\ rw [empty_q_payload_def]
  >- metis_tac [payloadPropsTheory.qcong_rules,
                payloadPropsTheory.qcong_nil_rel_nil]
  >- metis_tac [payloadPropsTheory.qcong_rules,
                payloadPropsTheory.qcong_nil_rel_nil]
  >- (drule payloadPropsTheory.qcong_par_rel_par_sym \\ rw []
      \\ imp_res_tac payloadPropsTheory.qcong_sym
      \\ fs [])
  >- (drule_then drule payloadPropsTheory.qcong_trans
      \\ disch_then (mp_then Any mp_tac payloadPropsTheory.qcong_par_rel_par)
      \\ rw [])
  >- (drule payloadPropsTheory.qcong_sym
      \\ disch_then (mp_then Any mp_tac payloadPropsTheory.qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule payloadPropsTheory.qcong_IMP_qrel
      \\ rw [] \\ drule payloadPropsTheory.qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule payloadPropsTheory.qcong_bindings_eq \\ fs [])
  >- (drule_then drule payloadPropsTheory.qcong_trans
      \\ disch_then (mp_then Any mp_tac payloadPropsTheory.qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule_then drule payloadPropsTheory.qcong_trans
      \\ rw [] \\ drule payloadPropsTheory.qcong_IMP_qrel
      \\ rw [] \\ drule payloadPropsTheory.qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule payloadPropsTheory.qcong_bindings_eq \\ fs [])
  \\ fs []
QED

(* projected networks always have empty queues *)
Theorem compile_network_empty_q:
  ∀l s (c : chor). empty_q_epn (compile_network s c l)
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         empty_q_epn_def]
QED

(* projected choice-free networks preserve empty_q_epn *)
Theorem compile_network_fv_empty_q:
  ∀epn fv.
  empty_q_epn epn
  ⇒ empty_q_epn (compile_network_fv fv epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

(* projected payload networks preserve empty_q_* *)
Theorem empty_q_epn_to_payload:
  ∀epn conf. empty_q_epn epn ⇒ empty_q_payload (compile_network conf epn)
Proof
  Induct \\ gen_tac
  \\ EVAL_TAC \\ rw []
  \\ EVAL_TAC
QED

(* If a network is empty_q_epn it can only be junkcong with
   other empty_q_epn networks *)
Theorem empty_q_epn_junkcong:
  ∀epn fv epn'. junkcong fv epn epn' ∧ empty_q_epn epn
  ⇒ empty_q_epn epn'
Proof
  Induct
  \\ ONCE_REWRITE_TAC [junkcong_cases]
  \\ rw [empty_q_epn_def]
  \\ rw [empty_q_epn_def]
  >- metis_tac[empty_q_epn_def,junkcong_nil_rel_nil,junkcong_sym]
  >- metis_tac[empty_q_epn_def,junkcong_nil_rel_nil,junkcong_sym]
  >- (drule junkcong_sym
      \\ disch_then (mp_then Any mp_tac junkcong_par_rel_par)
      \\ rw [] \\ fs [empty_q_epn_def] \\ metis_tac [])
  >- (drule_then drule junkcong_trans
      \\ disch_then (mp_then Any mp_tac junkcong_par_rel_par)
      \\ rw [] \\ fs [empty_q_epn_def] \\ metis_tac [])
  >- metis_tac []
  >- metis_tac []
  >- (drule junkcong_sym
      \\ disch_then (mp_then Any mp_tac junkcong_endpoint_rel_endpoint)
      \\ rw [] \\ rw [empty_q_epn_def]
      \\ drule junkcong_endpoint_queue_eq \\ fs [])
  \\ drule_then (drule_then assume_tac) junkcong_trans
  \\ drule junkcong_endpoint_rel_endpoint
  \\ rw [] \\ rw [empty_q_epn_def]
  \\ drule junkcong_endpoint_queue_eq \\ fs []
QED

Theorem projection_reflection:
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
  >- cheat (* TODO: propagation of invatiants *)
  \\ rw []
  \\ qspecl_then [‘compile_network_fv fv n4’,‘n3’] mp_tac junkcong_reduction_pres
  \\ disch_then (drule_then drule) \\ rw []
  \\ qpat_assum ‘reduction^* p4 _’ (mp_then Any (drule_then assume_tac) RTC_SPLIT)
  \\ first_assum (mp_then Any mp_tac to_payload_preservation)
  \\ disch_then (qspec_then ‘conf’ mp_tac)
  \\ impl_tac
  >- (fs [] \\ irule choice_free_reduction
      \\ metis_tac [choice_free_network_compile_network_fv])
  \\ disch_then (mp_then Any mp_tac qcong_reduction_pres)
  \\ disch_then (qspec_then ‘p3’ mp_tac)
  \\ impl_tac
  >- fs [payloadPropsTheory.qcong_sym]
  \\ rw []
  \\ qpat_assum ‘(reduction conf)^* epn _’ (mp_then Any (drule_then assume_tac) RTC_SPLIT)
  \\ qspec_then ‘p3'’ drule endpointPropsTheory.qcong_sym
  \\ disch_then (mp_then Any mp_tac empty_queue_qcong_epn)
  \\ rw [compile_network_empty_q]
  \\ first_x_assum (mp_then Any drule junkcong_trans)
  \\ rw [] \\ drule empty_q_epn_junkcong
  \\ impl_tac
  >- rw [compile_network_fv_empty_q,compile_network_empty_q]
  \\ rw []
  \\ drule_then (qspec_then ‘conf’ assume_tac) empty_q_epn_to_payload
  \\ drule_then drule empty_queue_qcong_payload \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
QED

val _ = export_theory ()

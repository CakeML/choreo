open preamble choreoUtilsTheory
     projectionTheory endpointPropsTheory

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


Theorem endpoints_compile_network_epn_aux:
  ∀epn fv.
   MAP FST (endpoints (endpoint_to_choice$compile_network_fv fv epn))
   = MAP FST (endpoints epn)
Proof
  Induct
  \\ rw [endpoint_to_choiceTheory.compile_network_fv_def,
         endpoints_def]
QED

Theorem endpoints_compile_network_epn:
  ∀epn.
   MAP FST (endpoints (endpoint_to_choice$compile_network epn)) = MAP FST (endpoints epn)
Proof
  rw [endpoint_to_choiceTheory.compile_network_def,endpoints_compile_network_epn_aux]
QED

Theorem MEM_nub':
  ∀l x. MEM x (nub' l) = MEM x l
Proof
  Induct
  \\ rw [nub'_def]
  \\ Cases_on ‘x=h’ \\ fs [MEM_FILTER]
QED

Triviality MEM_partners_endpoint_split_sel:
  ∀(c : chor) p l b x r.
   split_sel p l c = SOME (b,r) ∧
   project_ok p c ∧
   MEM x (partners_endpoint (project' p r))
   ⇒ MEM x (partners_endpoint (project' p c))
Proof
  Induct
  \\ fs [project_def,partners_endpoint_def,
         split_sel_def]
  \\ rw [partners_endpoint_def]
  >- (Cases_on ‘x = l’ \\ fs [] \\ metis_tac [])
  \\ metis_tac []
QED

Theorem MEM_partners_endpoint_imp_procsOf:
  ∀(c : chor) p x.
    project_ok p c ∧
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
  \\ fs [MEM_FILTER,MEM_nub']
  >- metis_tac [] >- metis_tac []
  >- (EVERY_CASE_TAC \\ fs [partners_endpoint_def]
      >- metis_tac []
      >- metis_tac []
      \\ disj2_tac \\ first_x_assum irule
      \\ imp_res_tac split_sel_project_ok
      \\ asm_exists_tac \\ fs []
      \\ metis_tac [MEM_partners_endpoint_split_sel])
  >- let val d_tac = first_x_assum irule
                     \\ imp_res_tac split_sel_project_ok
                     \\ asm_exists_tac \\ fs []
                     \\ metis_tac [MEM_partners_endpoint_split_sel]
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

Theorem partners_network_compile_network:
  ∀l (c : chor) s.
  compile_network_ok s c l
  ⇒ partners_network (compile_network s c l)
    = FLAT (MAP (\proc. partners_endpoint (project' proc c)) l)
Proof
  Induct
  \\ rw [chor_to_endpointTheory.compile_network_gen_def,
         partners_network_def]
QED

Theorem closed_network_from_chor:
  ∀s (c : chor).
   compile_network_ok s c (procsOf c)
   ⇒ closed_network (compile_network s c (procsOf c))
Proof
  rw [closed_network_def,
      closed_under_def,
      endpoints_compile_network_chor,
      SUBSET_DEF]
  \\ drule_then assume_tac partners_network_compile_network
  \\ fs [] \\ pop_assum (K ALL_TAC)
  \\ fs [MEM_FLAT,MEM_MAP] \\ rveq
  \\ irule MEM_partners_endpoint_imp_procsOf
  \\ fs [compile_network_ok_project_ok]
  \\ first_x_assum (drule_then assume_tac)
  \\ asm_exists_tac \\ fs []
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
      qcong epn' (projection conf s' c' (procsOf c))
Proof
  rw [projection_def]
  \\ first_x_assum (mp_then Any mp_tac from_payload_reflection)
  \\ impl_tac \\ rw []
  >- rw [endpoints_compile_network_epn,
         endpoints_compile_network_chor,
         procsOf_all_distinct]
  >- rw [choice_free_network_compile_network_fv,
         endpoint_to_choiceTheory.compile_network_def]
  \\ fs [endpoint_to_choiceTheory.compile_network_def]
  \\ first_x_assum (mp_then Any mp_tac from_choice_reflection)
  \\ impl_tac \\ rw [gen_fresh_name_same]
  >- rw [endpoints_compile_network_chor,
         procsOf_all_distinct]
  >- rw [closed_network_from_chor]
  \\ cheat
QED


val _ = export_theory ()

open preamble choreoUtilsTheory
     endpointLangTheory endpointSemTheory
     endpointPropsTheory endpointCongTheory
     endpoint_to_payloadTheory
     payloadLangTheory payloadSemTheory
     payloadPropsTheory

val _ = new_theory"payloadCong"


(* Right End Point Network (`REPN`) is a network with only `NEndpoint` on the left
   and either `NNil` or other `REPN` on the right

                NPar________________
                 |                  |
                 |                 NPar_______(...)________
                 |                  |                      |
                NEndpoint p s e    NEndpoint p' s' e'     NNil
*)
Definition REPN_def:
  REPN NNil                        = T
∧ REPN (NEndpoint _ _ _)           = F
∧ REPN (NPar (NEndpoint _ _ _) ep) = REPN ep
∧ REPN _                           = F
End

Definition nfold_def:
  nfold []           = NNil
∧ nfold ((p,s,e)::xs) = NPar (NEndpoint p s e) (nfold xs)
End

Theorem REPN_nfold:
  ∀l. REPN (nfold l)
Proof
  Induct \\ rw [REPN_def,nfold_def]
  \\ PairCases_on ‘h’
  \\ rw [REPN_def,nfold_def]
QED

Theorem endpoints_nfold_id:
  ∀l. endpoints (nfold l) = l
Proof
  Induct \\ rw [endpoints_def,nfold_def]
  \\ PairCases_on ‘h’
  \\ rw [endpoints_def,nfold_def]
QED

Theorem REPN_nfold_endpoint_id:
  ∀n. REPN n ⇒ n = nfold (endpoints n)
Proof
  Induct \\ rw [REPN_def,endpoints_def,nfold_def]
  \\ Cases_on ‘n’
  \\ fs [REPN_def,endpoints_def,nfold_def]
QED

Inductive payload_rcong:
(* Basic congruence rules *)
  (* Symmetric *)
  (∀c. payload_rcong c c)
  (* Reflexive *)
∧ (∀c1 c2.
    payload_rcong c1 c2
    ⇒ payload_rcong c2 c1)
  (* Transitive *)
∧ (∀c1 c2 c3.
    payload_rcong c1 c2
    ∧ payload_rcong c2 c3
    ⇒ payload_rcong c1 c3)
  (* Swap *)
∧ (∀n1 n2 n3.
    payload_rcong (NPar n1 (NPar n2 n3))
              (NPar n2 (NPar n1 n3)))
  (* Structural rules *)
∧ (∀n1 n2 n2'.
    payload_rcong n2 n2'
    ⇒ payload_rcong (NPar n1 n2)
                (NPar n1 n2'))
End

val _ = Parse.add_infix("p≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("p≅",``payload_rcong``);

Theorem payload_rcong_refl  = CONJUNCTS payload_rcong_rules |> el 1
Theorem payload_rcong_sym   = CONJUNCTS payload_rcong_rules |> el 2
Theorem payload_rcong_trans = CONJUNCTS payload_rcong_rules |> el 3
Theorem payload_rcong_swap  = CONJUNCTS payload_rcong_rules |> el 4
Theorem payload_rcong_pair  = CONJUNCTS payload_rcong_rules |> el 5

Theorem REPN_endpoint_NNil:
  ∀n. REPN n ∧ endpoints n = [] ⇒ n = NNil
Proof
  Induct \\  rw [REPN_def]
  \\ Cases_on ‘REPN (NPar n n')’ \\ fs []
  \\ Cases_on ‘n’ \\ fs [REPN_def,endpoints_def]
QED

Theorem REPN_endpoint_NPar:
  ∀n x xs.
  REPN n ∧ endpoints n = (x::xs)
  ⇒ ∃p s e n'. n = NPar (NEndpoint p s e) n'
Proof
  Induct \\  rw [REPN_def,endpoints_def]
  \\ Cases_on ‘n’ \\ fs [REPN_def,endpoints_def]
QED


Theorem PERM_rcong:
  ∀n1 n2.
      REPN n1 ∧ REPN n2 ∧ PERM (endpoints n1) (endpoints n2)
      ⇒ n1 p≅ n2
Proof
  ‘∀l1 l2.
    PERM l1 l2
    ⇒ ∀n1 n2.
       endpoints n1 = l1 ∧ REPN n1 ∧
       endpoints n2 = l2 ∧ REPN n2
       ⇒ n1 p≅ n2’
  suffices_by metis_tac []
  \\ ho_match_mp_tac PERM_IND \\ rw []
  >- metis_tac [payload_rcong_rules,REPN_endpoint_NNil]
  >- (IMP_RES_TAC REPN_endpoint_NPar
      \\ fs [REPN_def,endpoints_def]
      \\ rveq \\ fs []
      \\ metis_tac [payload_rcong_rules])
  >- (IMP_RES_TAC REPN_endpoint_NPar
      \\ fs [REPN_def,endpoints_def]
      \\ rveq \\ fs []
      \\ IMP_RES_TAC REPN_endpoint_NPar
      \\ fs [REPN_def,endpoints_def]
      \\ rveq \\ fs []
      \\ metis_tac [payload_rcong_rules])
  \\ irule payload_rcong_trans
  \\ qexists_tac ‘nfold l1'’
  \\ metis_tac [REPN_nfold,endpoints_nfold_id]
QED

(* If two (starting) networks (`n1`,`n1'`) are congruent then a
   transition with label `t` from any of them will imply there
   exists a transition from the opposite network with the same label `t`
   and the resuting networks `n2` `n2` will also be congruent

               trans conf n1  t n2
  n1-------------------------------------n2
   |                                     |
  θ≅                                    θ≅
   |           trans conf n1' t n2'      |
  n1'------------------------------------n2'

 *)
Theorem payload_rcong_imp_trans:
   ∀n1 n1'.
    n1 p≅ n1'
    ⇒ ∀t.(∀n2'. trans conf n1' t n2' ⇒ ∃n2.  trans conf n1  t n2  ∧ n2  p≅ n2')
       ∧ (∀n2.  trans conf n1  t n2  ⇒ ∃n2'. trans conf n1' t n2' ∧ n2' p≅ n2)
Proof
  let val trans_metis = metis_tac [payload_rcong_rules,trans_rules]
      val asm_payload_cases = (ASSUME_TAC o ONCE_REWRITE_RULE [trans_cases])
      val payload_rcong_tac  =
          fn (asm,g) =>
             let val is_trans = (curry op = "trans") o term_to_string o fst o strip_comb
                 val trans_match = fn t => is_comb t andalso is_trans t
                 val trans_terms = map (snd o strip_comb) (filter trans_match asm)
                 val pairs = map (fn t => (el 2 t,el 4 t)) trans_terms
                 val trans_g = g |> snd o dest_exists
                                 |> fst o dest_conj
                                 |> snd o strip_comb
                                 |> el 2
                 val the_g = subst (map (op |->) pairs) trans_g
             in EXISTS_TAC the_g (asm,g)
             end
      val payload_tac = payload_rcong_tac >> trans_metis
  in
  ho_match_mp_tac payload_rcong_strongind
  \\ rw []
  >- trans_metis >- trans_metis >- trans_metis >- trans_metis
  \\ pop_assum asm_payload_cases \\ rw []
  \\ TRY (qpat_x_assum `trans conf (NPar _ _) _ _` asm_payload_cases \\ rw [])
  \\ res_tac \\ payload_tac
  end
QED

(* A more human readable versin of `payload_rcong_imp_trans` *)
Theorem payload_rcong_trans':
   ∀n1 n2 n1' conf t.
    n1 p≅ n1'
    ∧ trans conf n1 t n2
    ⇒ ∃n2'. trans conf n1' t n2' ∧ n2 p≅ n2'
Proof
  metis_tac [payload_rcong_imp_trans,payload_rcong_rules]
QED

(* An extended RTC version of `payload_rcong_trans'` *)
Theorem payload_rcong_reduction:
   ∀n1 n2 n1' conf.
    n1 p≅ n1'
    ∧ (reduction conf)^* n1 n2
    ⇒ ∃n2'. (reduction conf)^* n1' n2' ∧ n2 p≅ n2'
Proof
  rpt GEN_TAC
  \\ `∀n1 n2. (reduction conf)^* n1 n2
       ⇒ ∀n1'. n1 p≅ n1'
          ⇒ ∃n2'. (reduction conf)^* n1' n2' ∧ n2 p≅ n2'`
     suffices_by metis_tac []
  \\ ho_match_mp_tac RTC_INDUCT \\ rw []
  >- (Q.EXISTS_TAC `n1'` \\ rw [])
  >- (fs [reduction_def]
     \\ IMP_RES_TAC payload_rcong_trans'
     \\ pop_assum (K ALL_TAC)
     \\ RES_TAC
     \\ fs [GSYM reduction_def]
     \\ metis_tac [RTC_RULES])
QED

(* REPN is preserver through endpoint_to_payload.compile_network *)
Theorem compile_endpoint_REPN:
  ∀epn conf. REPN epn ⇒ REPN (compile_network conf epn)
Proof
  Induct \\ rw [compile_network_def,REPN_def,endpointCongTheory.REPN_def]
  \\ Cases_on ‘epn’ \\ fs [REPN_def,endpointCongTheory.REPN_def,compile_network_def]
QED

(* payload_rcong preserves normalised_network,
   since all the states should be the same
*)
Theorem normalised_network_cong:
  ∀n n'.
   n p≅ n'
   ⇒ normalised_network n = normalised_network n'
Proof
  ho_match_mp_tac payload_rcong_ind
  \\ rw [normalised_network_def]
  \\ metis_tac []
QED

(* Rule verison of normalised_network_cong *)
Theorem normalised_network_cong_IMP:
  ∀n n'.
   normalised_network n ∧ n p≅ n'
   ⇒ normalised_network n'
Proof
  metis_tac [normalised_network_cong]
QED

(* The set of all endpoint names in a parallel composition
   is the union of the node names at each sub-network
*)
Theorem net_has_node_NPar:
  ∀n1 n2. net_has_node (NPar n1 n2) = net_has_node n1 ∪ net_has_node n2
Proof
  rw []
  \\ CONV_TAC FUN_EQ_CONV
  \\ simp [net_has_node_def,IN_DEF]
QED

(* payload_rcong preserver all endpoint names *)
Theorem net_has_node_cong:
  ∀n n'.
    n p≅ n'
    ⇒ net_has_node n = net_has_node n'
Proof
  ho_match_mp_tac payload_rcong_ind
  \\ rw [net_has_node_def,net_has_node_NPar]
  \\ ONCE_REWRITE_TAC [UNION_ASSOC]
  \\ rw [UNION_COMM]
QED

(* payload_rcong preserves well-formedness, since only the structure
   is changed not its contents
*)
Theorem net_wf_cong:
  ∀n n'.
    n p≅ n'
    ⇒ net_wf n = net_wf n'
Proof
  ho_match_mp_tac payload_rcong_strongind
  \\ rw [net_wf_def]
  >- (rw [net_has_node_NPar,DISJOINT_SYM]
      \\ metis_tac [])
  \\ drule_then assume_tac net_has_node_cong
  \\ fs []
QED

(* Rule version of net_wf_cong *)
Theorem net_wf_cong_IMP:
  ∀n n'.
    net_wf n ∧ n p≅ n'
    ⇒  net_wf n'
Proof
  metis_tac [net_wf_cong]
QED

(* Finds a specific endpoint by name in the network *)
Definition net_find_def:
  net_find p NNil = NONE
∧ net_find p (NPar n1 n2) = OPTION_CHOICE (net_find p n1)
                                          (net_find p n2)
∧ net_find p (NEndpoint p' s c) = (if p = p'
                                   then SOME (NEndpoint p s c)
                                   else NONE)
End

(* Removes a specific (single) endpoint by name in the network.
   Note that if multiple endpoints with the same name exists
   a call to net_filter will only remove 1
*)
Definition net_filter_def:
  net_filter p NNil = NNil
∧ net_filter p (NEndpoint p' s c) =
    (if p = p' then NNil
     else NEndpoint p' s c)
∧ net_filter p (NPar n1 n2) =
    let l = net_filter p n1
    in if n1 ≠ l
       then if l = NNil then n2
            else NPar l n2
       else NPar n1 (net_filter p n2)
End

(* Show that the combination of net_filter and net_find does not affect any
   the contents of the network and only modifies its structure.

   REPN is only required to simplify the proof by constraining the
   type of networks being consider

 *)
Theorem net_find_filter_cong:
  ∀n p e.
   REPN n ∧
   net_find p n = SOME e
   ⇒ n p≅ NPar e (net_filter p n)
Proof
  Induct
  \\ rw [net_filter_def,net_find_def]
  \\ fs [REPN_def,net_find_def,net_filter_def]
  \\ Cases_on ‘n’ \\ fs [REPN_def,net_find_def,net_filter_def]
  \\ Cases_on ‘p = l’ \\ fs [net_wf_def,payload_rcong_refl]
  \\ metis_tac [payload_rcong_rules]
QED

(* Processes do not disappear after a transition ;) *)
Theorem net_find_IS_SOME_trans_pres:
  ∀conf n L n' p.
    trans conf n L n'
   ⇒ IS_SOME (net_find p n) = IS_SOME (net_find p n')
Proof
  rpt gen_tac
  \\ map_every qid_spec_tac [‘n'’,‘L’,‘n’,‘conf’]
  \\ ho_match_mp_tac trans_ind
  \\ rw [net_find_def]
  \\ qmatch_goalsub_abbrev_tac ‘IS_SOME (OPTION_CHOICE l1 r1) =
                                IS_SOME (OPTION_CHOICE l2 r2)’
  \\ ntac 4 (pop_assum kall_tac)
  \\ Cases_on ‘l1’ \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
  \\ Cases_on ‘l2’ \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
QED

(* Processes do not appear after a transition *)
Theorem net_find_IS_NONE_trans_pres:
  ∀conf n L n' p.
    trans conf n L n'
   ⇒ IS_NONE (net_find p n) = IS_NONE (net_find p n')
Proof
  rpt gen_tac
  \\ map_every qid_spec_tac [‘n'’,‘L’,‘n’,‘conf’]
  \\ ho_match_mp_tac trans_ind
  \\ rw [net_find_def]
  \\ qmatch_goalsub_abbrev_tac ‘(OPTION_CHOICE l1 r1) = NONE ⇔
                                (OPTION_CHOICE l2 r2) = NONE’
  \\ ntac 4 (pop_assum kall_tac)
  \\ Cases_on ‘l1’ \\ fs []
  \\ Cases_on ‘l2’ \\ fs []
QED

(* Rule version of net_find_IS_SOME_trans_pres *)
Theorem net_find_IS_SOME_trans_pres_IMP:
  ∀conf n L n' p.
    trans conf n L n' ∧ IS_SOME (net_find p n)
    ⇒ IS_SOME (net_find p n')
Proof
  metis_tac [net_find_IS_SOME_trans_pres]
QED

(* Rule version of net_find_IS_NONE_trans_pres *)
Theorem net_find_IS_NONE_trans_pres_IMP:
  ∀conf n L n' p.
    trans conf n L n' ∧ IS_NONE (net_find p n)
    ⇒ IS_NONE (net_find p n')
Proof
  metis_tac [net_find_IS_NONE_trans_pres]
QED

(* net_find always returns a single endpoint *)
Theorem net_find_NEndpoint:
  ∀n p x. net_find p n = SOME x ⇒ ∃s c. x = NEndpoint p s c
Proof
  Induct \\ rw [net_find_def]
  \\ Cases_on ‘net_find p n’ \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
  \\ Cases_on ‘net_find p n'’ \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
QED

(* If network n does not have process p in it,
   net_filter returns the same network
*)
Theorem net_find_NONE_net_filter_simp:
∀n p n'.
  net_find p n = NONE
  ⇒ net_filter p n = n ∧
    net_filter p (NPar n n') = NPar n (net_filter p n')
Proof
  rpt gen_tac
  \\ strip_tac
  \\ (fn (asm,g) =>
        sg ‘^(g  |> dest_conj |> fst)’ (asm,g))
  >- (pop_assum mp_tac
      \\ map_every qid_spec_tac [‘p’,‘n’]
      \\ Induct \\ rw [net_filter_def,net_find_def]
      \\ Cases_on ‘net_find p n’ \\ fs [OPTION_CHOICE_def]
      \\ Cases_on ‘net_find p n'’ \\ fs [OPTION_CHOICE_def]
      \\ res_tac
      \\ fs [])
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac [‘n'’,‘p’,‘n’]
  \\ Induct \\ rw [net_find_def]
  \\ fs [net_filter_def]
  \\ Cases_on ‘net_find p n’ \\ fs [OPTION_CHOICE_def]
  \\ Cases_on ‘net_find p n'’ \\ fs [OPTION_CHOICE_def]
  \\ res_tac \\ rw [net_filter_def]
QED

(* If the first network in a parallel composition
   contains a process p, the second one would not be touched.
*)
Theorem net_find_SOME_net_filter_simp:
∀n p x n'.
  net_find p n = SOME x ∧ REPN (NPar n n')
  ⇒ net_filter p (NPar n n') = n'
Proof
  Induct \\ rw [net_filter_def,net_filter_def,REPN_def] \\ rfs []
  \\ fs [net_find_def] \\ rfs [] \\ rveq \\ fs []
QED

(* REPN is preserved by trans *)
Theorem trans_REPN_pres:
  ∀conf n L n'. trans conf n L n' ⇒ (REPN n ⇔ REPN n')
Proof
  rw []
  \\ rpt (pop_assum mp_tac)
  \\ map_every qid_spec_tac [‘n'’,‘L’,‘n’,‘conf’]
  \\ ho_match_mp_tac trans_strongind
  \\ rw [REPN_def]
  \\ qmatch_goalsub_rename_tac ‘REPN (NPar nn _) = _’
  \\ EQ_TAC \\ rw []
  >- (Cases_on ‘nn’ \\ fs [REPN_def]
      \\ drule trans_struct_pres_NEnpoint
      \\ rw [REPN_def] \\ fs [REPN_def])
  \\ Cases_on ‘nn’ \\ fs [REPN_def]
  \\ TRY (fs [Once trans_cases] \\ NO_TAC)
  \\ TRY (drule trans_struct_pres_NPar \\ strip_tac \\ fs [REPN_def] \\ NO_TAC)
  \\ drule trans_struct_pres_NEnpoint
  \\ rw [REPN_def] \\ fs [REPN_def]
QED

(* Rule version of trans_REPN_pres *)
Theorem trans_REPN_pres_IMP:
  ∀conf n L n'. trans conf n L n' ∧ REPN n ⇒ REPN n'
Proof
  metis_tac [trans_REPN_pres]
QED

(* All the cases an LReceive transition can be split using
   net_find and net_filter *)
Theorem net_filter_LReceive_cases:
  ∀n conf n' p s r x d.
  trans conf n (LReceive r d s) n' ∧
  net_find p n = SOME x ∧ REPN n
  ⇒ (∃x'. trans conf x (LReceive r d s) x' ∧
          net_find p n' = SOME x' ∧
          s = p ∧
          net_filter p n = net_filter p n') ∨
    (trans conf (net_filter p n) (LReceive r d s) (net_filter p n') ∧
     net_find p n' = SOME x)
Proof
  Induct \\ rw []
  \\ qpat_assum ‘trans conf _ _ _’
                (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ fs [] \\ rw []
  >- (first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘n’ \\ fs [net_find_def,REPN_def]
      \\ Cases_on ‘p = l’ \\ fs [OPTION_CHOICE_def]
      \\ drule_then assume_tac trans_struct_pres_NEnpoint
      \\ fs [] \\ rveq \\ fs []
      \\ ‘l = s’ by fs [Once trans_cases]
      >- (disj1_tac \\ asm_exists_tac \\ fs [net_find_def,net_filter_def])
      \\ disj2_tac
      \\ rw [OPTION_CHOICE_def,net_find_def,net_filter_def]
      \\ metis_tac [trans_rules])
  >- (first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘net_find p n’ \\ fs [net_find_def,REPN_def]
      >- (first_x_assum drule
          \\ impl_tac >- (Cases_on ‘n’ \\ fs [REPN_def])
          \\ fs [net_find_NONE_net_filter_simp]
          \\ metis_tac [trans_rules])
      \\ rveq \\ fs [] \\ disj2_tac
      \\ ‘REPN (NPar n n2')’
          by (Cases_on ‘n’ \\ fs [REPN_def]
              \\ drule_all trans_REPN_pres_IMP \\ rw [])
      \\ fs[net_find_SOME_net_filter_simp])
  \\ fs [net_find_def] \\ rveq \\ rfs [net_filter_def]
QED

(* All the cases an LSend transition can be split using
   net_find and net_filter *)
Theorem net_filter_LSend_cases:
  ∀n conf n' p s r x d.
  trans conf n (LSend s d r) n' ∧
  net_find p n = SOME x ∧ REPN n
  ⇒ (∃x'. trans conf x (LSend s d r) x' ∧
          net_find p n' = SOME x' ∧
          s = p ∧
          net_filter p n = net_filter p n') ∨
    (trans conf (net_filter p n) (LSend s d r) (net_filter p n') ∧
     net_find p n' = SOME x)
Proof
  Induct \\ rw []
  \\ qpat_assum ‘trans conf _ _ _’
                (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ fs [] \\ rw []
  >- (first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘n’ \\ fs [net_find_def,REPN_def]
      \\ Cases_on ‘p = l’ \\ fs [OPTION_CHOICE_def]
      \\ drule_then assume_tac trans_struct_pres_NEnpoint
      \\ fs [] \\ rveq \\ fs []
      \\ ‘l = s’ by fs [Once trans_cases]
      >- (disj1_tac \\ asm_exists_tac \\ fs [net_find_def,net_filter_def])
      \\ disj2_tac
      \\ rw [OPTION_CHOICE_def,net_find_def,net_filter_def]
      \\ metis_tac [trans_rules])
  >- (first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘net_find p n’ \\ fs [net_find_def,REPN_def]
      >- (first_x_assum drule
          \\ impl_tac >- (Cases_on ‘n’ \\ fs [REPN_def])
          \\ fs [net_find_NONE_net_filter_simp]
          \\ metis_tac [trans_rules])
      \\ rveq \\ fs [] \\ disj2_tac
      \\ ‘REPN (NPar n n2')’
          by (Cases_on ‘n’ \\ fs [REPN_def]
              \\ drule_all trans_REPN_pres_IMP \\ rw [])
      \\ fs[net_find_SOME_net_filter_simp])
  \\ fs [net_find_def] \\ rveq \\ rfs [net_filter_def]
QED

(* All the cases an LTau transition can be split using
   net_find and net_filter *)
Theorem net_filter_LTau_cases:
  ∀n conf n' p s r x d.
  trans conf n LTau n' ∧
  net_find p n = SOME x ∧ REPN n
  ⇒ (trans conf (net_filter p n) LTau (net_filter p n') ∧
     net_find p n' = SOME x) ∨
    (∃x'. trans conf x LTau x' ∧ net_find p n' = SOME x' ∧
          net_filter p n = net_filter p n') ∨
    (∃x' s d r. trans conf x (LSend s d r) x' ∧ net_find p n' = SOME x' ∧
                trans conf (net_filter p n) (LReceive s d r) (net_filter p n')) ∨
    (∃x' s d r. trans conf x (LReceive s d r) x' ∧ net_find p n' = SOME x' ∧
                trans conf (net_filter p n) (LSend s d r) (net_filter p n'))
Proof
  Induct
  \\ rw []
  \\ qpat_x_assum `trans _ _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw [REPN_def] \\ fs [REPN_def]
  \\ qmatch_asmsub_rename_tac ‘REPN (NPar n1 n2)’
  >- (‘REPN n2’ by (Cases_on ‘n1’ \\ fs [REPN_def])
      \\ Cases_on ‘net_find  p n1’
      >- (fs [net_find_def]
          \\ qpat_assum ‘trans _ n1 _ _’ (mp_then Any mp_tac net_find_IS_NONE_trans_pres_IMP)
          \\ disch_then (qspec_then ‘p’ mp_tac)
          \\ rw [net_find_NONE_net_filter_simp]
          \\ drule_all net_filter_LReceive_cases
          \\ rw []
          \\ metis_tac [trans_rules])
      \\ Cases_on ‘n1’ \\ fs [REPN_def,net_find_def]
      \\ rveq \\ fs []
      \\ drule trans_struct_pres_NEnpoint \\ rw []
      \\ rw [net_find_def,net_filter_def]
      \\ metis_tac [trans_rules])
  >- (‘REPN n2’ by (Cases_on ‘n1’ \\ fs [REPN_def])
      \\ Cases_on ‘net_find  p n1’
      >- (fs [net_find_def]
          \\ qpat_assum ‘trans _ n1 _ _’ (mp_then Any mp_tac net_find_IS_NONE_trans_pres_IMP)
          \\ disch_then (qspec_then ‘p’ mp_tac)
          \\ rw [net_find_NONE_net_filter_simp]
          \\ drule_all net_filter_LSend_cases
          \\ rw []
          \\ metis_tac [trans_rules])
      \\ Cases_on ‘n1’ \\ fs [REPN_def,net_find_def]
      \\ rveq \\ fs []
      \\ drule trans_struct_pres_NEnpoint \\ rw []
      \\ rw [net_find_def,net_filter_def]
      \\ metis_tac [trans_rules])
  >- (‘REPN n2’ by (Cases_on ‘n1’ \\ fs [REPN_def])
      \\ Cases_on ‘net_find  p n1’
      \\ fs [net_find_def]
      >- (disj1_tac
          \\ drule_then (qspec_then ‘p’ mp_tac) net_find_IS_NONE_trans_pres_IMP
          \\ rw [net_find_NONE_net_filter_simp]
          \\ metis_tac [trans_rules])
      \\ Cases_on ‘n1’ \\ fs [REPN_def,net_find_def]
      \\ rveq \\ fs []
      \\ drule trans_struct_pres_NEnpoint \\ rw []
      \\ rw [net_find_def,net_filter_def]
      \\ metis_tac [trans_rules])
  \\ ‘REPN n2’ by (Cases_on ‘n1’ \\ fs [REPN_def])
  \\ Cases_on ‘net_find  p n1’
  \\ fs [net_find_def]
  >- (first_x_assum drule_all \\ rw []
      \\ metis_tac [net_find_NONE_net_filter_simp,trans_rules])
  \\ ‘REPN (NPar n1 n2')’
      by (Cases_on ‘n1’ \\ fs [REPN_def]
          \\ metis_tac [trans_REPN_pres_IMP])
  \\ rveq \\ fs [net_find_SOME_net_filter_simp]
QED

(* Arbitrary reordering of network using net_find and net_filter *)
Theorem net_find_filter_trans:
  ∀conf n L n' p.
   trans conf n L n' ∧
   REPN n ∧
   IS_SOME (net_find p n) ∧
   conf.payload_size > 0
   ⇒ trans conf (NPar (THE (net_find p n )) (net_filter p n )) L
                (NPar (THE (net_find p n')) (net_filter p n'))
Proof
   rw []
   \\ drule_all_then assume_tac net_find_IS_SOME_trans_pres_IMP
   \\ fs [IS_SOME_EXISTS,net_find_def]
   \\ ntac 4 (pop_assum mp_tac)
   \\ map_every qid_spec_tac [‘x'’,‘x’,‘p’]
   \\ simp [AND_IMP_INTRO]
   \\ pop_assum mp_tac
   \\ map_every qid_spec_tac [‘n'’,‘L’,‘n’,‘conf’]
   \\ ho_match_mp_tac trans_strongind
   \\ rw [REPN_def]
   (* Receive *)
   >- (Cases_on ‘n’ \\ fs [REPN_def,net_find_def]
       \\ drule_then assume_tac trans_struct_pres_NEnpoint
       \\ fs [] \\ rveq \\ fs []
       \\ Cases_on ‘p = l’ \\ fs [OPTION_CHOICE_def]
       \\ rveq \\ fs [net_find_def,net_filter_def]
       >- metis_tac [trans_rules]
       \\ drule_all net_filter_LReceive_cases
       \\ rw []
       \\ metis_tac [trans_rules])
   (* Send *)
   >- (Cases_on ‘n’ \\ fs [REPN_def,net_find_def]
       \\ drule_then assume_tac trans_struct_pres_NEnpoint
       \\ fs [] \\ rveq \\ fs []
       \\ Cases_on ‘p = l’ \\ fs [OPTION_CHOICE_def]
       \\ rveq \\ fs [net_find_def,net_filter_def]
       >- metis_tac [trans_rules]
       \\ drule_all net_filter_LSend_cases
       \\ rw []
       \\ metis_tac [trans_rules])
   >- (Cases_on ‘net_find p n’
       \\ Cases_on ‘n’ \\ fs [REPN_def,net_find_def]
       \\ rveq \\ fs []
       \\ drule trans_struct_pres_NEnpoint
       \\ rw [] \\ fs [net_filter_def]
       \\ fs [net_find_def,OPTION_CHOICE_def]
       \\ rveq \\ fs []
       \\ metis_tac [trans_rules])
   \\ reverse (Cases_on ‘net_find p n1’)
   \\ Cases_on ‘n1’ \\ fs [REPN_def,net_find_def]
   \\ rveq \\ fs [net_filter_def]
   >- metis_tac [trans_rules]
   \\ first_x_assum drule_all
   \\ rw []
   \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [trans_cases])
   \\ fs [] \\ metis_tac [trans_rules]
QED

(* Arbitrary reordering of network using net_find and net_filter *)
Theorem net_find_filter_reduction:
  ∀conf n n' p.
   (reduction conf)⃰ n n' ∧
   REPN n ∧
   IS_SOME (net_find p n) ∧
   conf.payload_size > 0
   ⇒ (reduction conf)⃰ (NPar (THE (net_find p n )) (net_filter p n ))
                       (NPar (THE (net_find p n')) (net_filter p n'))
Proof
  rw []
  \\ pop_assum (fn t => ntac 2 (pop_assum mp_tac) \\ assume_tac t)
  \\ simp [AND_IMP_INTRO]
  \\ last_x_assum mp_tac
  \\ map_every qid_spec_tac [‘n'’,‘n’]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw []
  \\ irule (RTC_RULES  |> SPEC_ALL  |> CONJUNCT2)
  \\ fs [reduction_def]
  \\ metis_tac [trans_REPN_pres_IMP,
                net_find_IS_SOME_trans_pres_IMP,
                net_find_filter_trans]
QED

(* net_has_node implies net_find wil find something *)
Theorem net_has_node_IS_SOME_net_find:
  ∀n p. net_has_node n p = IS_SOME (net_find p n)
Proof
  Induct \\ rw [net_has_node_def,net_find_def]
  \\ Cases_on ‘net_has_node n p’
  \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
  \\ rfs []
  \\ Cases_on ‘net_has_node n' p’
  \\ fs [IS_SOME_EXISTS,OPTION_CHOICE_def]
  \\ rfs []
  \\ Cases_on ‘net_find p n’ \\ fs []
QED

(* normalised_network can be re-arranged using net_filter and net_find *)
Theorem normalised_network_net_find_filter:
  ∀n p e.
  net_find p n = SOME e ∧ REPN n ⇒
  normalised_network n = normalised_network (NPar e (net_filter p n))
Proof
  rw []
  \\ drule_all net_find_filter_cong
  \\ fs [normalised_network_cong]
QED

(* Then endpoints left in the network after a call to net_filter
   are a subset of the original ones
*)
Theorem net_filter_SUBSET:
  ∀n p. net_has_node (net_filter p n) ⊆ net_has_node n
Proof
  rw [SUBSET_DEF,IN_DEF]
  \\ Induct_on ‘n’ \\ fs [net_has_node_def,net_filter_def]
  \\ rw [] \\ fs [net_has_node_def]
QED

(* net_wf still holds after removing any process *)
Theorem net_wf_filter:
  ∀n p. net_wf n ⇒ net_wf (net_filter p n)
Proof
  Induct \\ rw [net_filter_def,net_wf_def]
  >- (ONCE_REWRITE_TAC [DISJOINT_SYM]
      \\ irule DISJOINT_SUBSET
      \\ qexists_tac ‘net_has_node n’
      \\ fs [DISJOINT_SYM]
      \\ fs [net_filter_SUBSET])
  \\ irule DISJOINT_SUBSET
  \\ qexists_tac ‘net_has_node n'’
  \\ fs []
  \\ fs [net_filter_SUBSET]
QED

(* net_filter removes all endpoint named p from well-formed networks *)
Theorem not_net_has_node_net_filter:
  ∀n p. net_wf n ∧ REPN n ⇒ ¬ net_has_node (net_filter p n) p
Proof
  Induct \\ rw [net_wf_def,net_has_node_def,net_filter_def,DISJOINT_ALT,IN_DEF,REPN_def]
  \\ Cases_on ‘n’ \\ fs [REPN_def,net_filter_def]
  \\ TRY (first_x_assum irule)
  \\ Cases_on ‘p = l’ \\ fs [net_has_node_def]
QED

val _ = export_theory ()

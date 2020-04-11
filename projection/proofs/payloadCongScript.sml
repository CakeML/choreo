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

val _ = export_theory ()

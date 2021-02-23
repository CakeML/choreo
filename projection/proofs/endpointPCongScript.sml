open preamble choreoUtilsTheory endpointLangTheory
     pchor_to_endpointTheory
     endpointSemTheory endpointPropsTheory
     endpointCongTheory
     chorSemTheory pchorSemTheory

val _ = new_theory"endpointPCong"

val pchor = “c : pchor”

val epn_rcong_sym   =  epn_rcong_sym;
val epn_rcong_refl  =  epn_rcong_refl;
val epn_rcong_trans =  epn_rcong_trans;
val epn_rcong_swap  =  epn_rcong_swap;
val epn_rcong_npair =  epn_rcong_pair;

(* Projected networks identity over `network_procs` *)
Theorem network_procs_pchor_compile_id:
  ∀s c l. network_procs (compile_network s ^pchor l) = l
Proof
  rw [] >> Induct_on `l`
  \\ rw [network_procs_def,
         pchor_to_endpointTheory.compile_network_gen_def]
QED

(* Two projected (using `compile_network`) networks are congruent as long as
   the list of projected process are permutable
*)
Theorem PERM_rcong_pchor_compile_network:
  ∀l l' s c. PERM l l'
   ⇒ compile_network s ^pchor l θ≅ compile_network s ^pchor l'
Proof
  rpt GEN_TAC
  \\ `∀l l'. PERM l l' ⇒ compile_network s c l θ≅ compile_network s c l'`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac PERM_IND
  \\ rw [pchor_to_endpointTheory.compile_network_gen_def
        ,epn_rcong_rules]
  >- (MAP_EVERY Q.ABBREV_TAC
       [ `s1 = <|bindings := pchor_to_endpoint$projectS x s;
                 queue    := projectQ' x [] c |>`
       , `n1 = (project' x c)`
       , `s2 = <|bindings := pchor_to_endpoint$projectS y s;
                 queue    := projectQ' y [] c |>`
       , `n2 = (project' y c)`
       , `n3 = compile_network s ^pchor l`
       , `n4 = compile_network s ^pchor l'`]
     \\ ho_match_mp_tac epn_rcong_trans
     \\ Q.EXISTS_TAC `NPar (NEndpoint y s2 n2) (NPar (NEndpoint x s1 n1) n3)`
     \\ rw [epn_rcong_rules])
  >- (metis_tac [epn_rcong_trans])
QED

(* Projected networks are always REPN *)
Theorem pchor_REPN_compile_network:
  ∀s c l. REPN (compile_network s ^pchor l)
Proof
  Induct_on `l` >> rw [REPN_def,pchor_to_endpointTheory.compile_network_gen_def]
QED

(* Every element in a projected partial choreography is a projection
   of state and endpoint for an specific process

   PS: this is obvious, but it's convenient to have
 *)
Theorem pchor_compile_network_MEM_elem:
   ∀p s e c s' l.
    MEM (p,s',e) (endpoints (compile_network s ^pchor l))
    ⇒ s' = <|bindings := pchor_to_endpoint$projectS p s;
             queue    := projectQ' p [] ^pchor |>
      ∧ e = project' p ^pchor
Proof
  rpt GEN_TAC
  \\ Induct_on `l`
  \\ rw [MEM,pchor_to_endpointTheory.compile_network_gen_def,endpoints_def]
  \\ fs []
QED

(* One can pull (using congruence) any element of a projected network
   to be the top-most endpoint
*)
Theorem pchor_compile_network_pull:
   ∀p s e s' c l ep.
    ALL_DISTINCT l
    ∧ MEM (p,s,e) (endpoints (compile_network s' ^pchor l))
    ∧ ep = compile_network s' ^pchor (FILTER ($≠ p) l)
    ⇒ compile_network s' ^pchor l θ≅ NPar (NEndpoint p s e) ep
Proof
  rw []
  \\ Induct_on `l` \\ rw []
  >- fs [pchor_to_endpointTheory.compile_network_gen_def,endpoints_def,MEM]
  >- (fs [pchor_to_endpointTheory.compile_network_gen_def,endpoints_def,MEM] \\ fs []
     \\ Q.ABBREV_TAC `h_ep =
           NEndpoint h <| bindings := pchor_to_endpoint$projectS h s';
                          queue    := projectQ' h [] c |> (project' h ^pchor)`
     \\ ho_match_mp_tac epn_rcong_trans
     \\ Q.EXISTS_TAC `NPar h_ep
                           (NPar (NEndpoint p s e)
                           (compile_network s' ^pchor (FILTER (λy. p ≠ y) l)))`
     \\ rw [Abbr `h_ep`, epn_rcong_swap]
     \\ ho_match_mp_tac epn_rcong_npair
     \\ rw [])
  >- (fs [pchor_to_endpointTheory.compile_network_gen_def,endpoints_def,MEM] \\ fs []
     \\ `¬MEM h l ⇒ FILTER ($≠ h) l = l`
        by (rpt (pop_assum (K ALL_TAC))
           \\ Induct_on `l`
           \\ rw [MEM_FILTER,FILTER])
     \\ metis_tac [epn_rcong_refl,pchor_compile_network_MEM_elem])
QED

(* Any network that is congruent with a projected network, can be
   expressed as a projection (using `compile_network`)
*)
Theorem pchor_compile_network_rcong:
   ∀s c l ep. compile_network s ^pchor l θ≅ ep ∧ ALL_DISTINCT l
    ⇒ ep = compile_network s ^pchor (network_procs ep)
Proof
  Induct_on `ep`
  >- (rw [pchor_to_endpointTheory.compile_network_gen_def,network_procs_def])
  >- (rw []
     \\ `REPN (compile_network s ^pchor l)`
        by rw [pchor_REPN_compile_network]
     \\ IMP_RES_TAC rcong_REPN
     \\ IMP_RES_TAC REPN_NPar_isNEndpoint
     \\ rw []
     \\ IMP_RES_TAC rcong_PERM_enpoints
     \\ `MEM (p,s',e) (endpoints (NPar (NEndpoint p s' e) ep'))`
        by rw [endpoints_def]
     \\ `MEM (p,s',e) (endpoints (compile_network s c l))`
         by metis_tac [PERM_MEM_EQ]
     \\ Q.ABBREV_TAC `l' = compile_network s c (FILTER ($≠ p) l)`
     \\ `NPar (NEndpoint p s' e) l' θ≅ compile_network s c l`
        by (rw [Abbr `l'`] >> metis_tac [pchor_compile_network_pull,epn_rcong_sym])
     \\ `NPar (NEndpoint p s' e) l' θ≅ NPar (NEndpoint p s' e) ep'`
        by (rw [Abbr `l'`] >> metis_tac [epn_rcong_trans])
     \\ `l' θ≅ ep'`
        by (rw [Abbr `l'`] >> metis_tac [epn_rcong_NPar,rcong_REPN])
     \\ rw [pchor_to_endpointTheory.compile_network_gen_def,network_procs_def,
            pchor_compile_network_MEM_elem]
     \\ IMP_RES_TAC pchor_compile_network_MEM_elem
     \\ UNABBREV_ALL_TAC
     \\ metis_tac [FILTER_ALL_DISTINCT])
 >- (rw []
    \\ `REPN (compile_network s' c l)` by rw [pchor_REPN_compile_network]
    \\ IMP_RES_TAC rcong_REPN
    \\ fs [REPN_def])
QED

(* See ‘chor_PERM_compile_network_trans’ (above) for a nice explanation *)
Theorem pchor_PERM_compile_network_trans:
   ∀s c (c' : pchor) t l1 l2.
    PERM l1 l2
    ∧ ALL_DISTINCT l1
    ∧ trans (compile_network s ^pchor l1) t (compile_network s c' l1)
    ⇒ trans (compile_network s ^pchor l2) t (compile_network s c' l2)
Proof
    rw []
    \\ `compile_network s c l1 θ≅ compile_network s c l2`
       by rw [PERM_rcong_pchor_compile_network]
    \\ IMP_RES_TAC epn_rcong_trans'
    \\ IMP_RES_TAC network_procs_trans
    \\ IMP_RES_TAC pchor_compile_network_rcong
    \\ rfs [network_procs_pchor_compile_id]
    \\ rw []
QED

(* An RTC variant of `PERM_pchor_compile_network_trans`, way more relevant and useful *)
Theorem PERM_pchor_compile_network_reduction:
   ∀s c (c' : pchor) l1 l2.
    PERM l1 l2
    ∧ ALL_DISTINCT l1
    ∧ reduction^* (compile_network s ^pchor l1) (compile_network s c' l1)
    ⇒ reduction^* (compile_network s ^pchor l2) (compile_network s c' l2)
Proof
    rw []
    \\ `compile_network s c l1 θ≅ compile_network s c l2`
       by rw [PERM_rcong_pchor_compile_network]
    \\ IMP_RES_TAC epn_rcong_reduction
    \\ IMP_RES_TAC network_procs_reduction
    \\ IMP_RES_TAC pchor_compile_network_rcong
    \\ rfs [network_procs_pchor_compile_id]
    \\ rw []
QED

(* `com` instance of `PERM_pchor_compile_network_reduction` with more
   specific assumptions
*)
Theorem pchor_compile_network_COM:
  ∀s ^pchor p x q y l.
   PERM (procsOf (Com  p x q y c)) l
   ∧ p ≠ q
   ∧ reduction^* (compile_network s (Com  p x q y c) (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
                 (compile_network s               c  (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
   ⇒ reduction^* (compile_network s (Com  p x q y c) l) (compile_network s c l)
Proof
    rw []
    \\ Q.ABBREV_TAC `l' = p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l`
    \\ `ALL_DISTINCT l`
       by metis_tac [ALL_DISTINCT_PERM,pchorSemTheory.procsOf_all_distinct]
    \\ `ALL_DISTINCT l'`
       by rw [Abbr `l'`,ALL_DISTINCT,MEM_FILTER,FILTER_ALL_DISTINCT]
    \\ `MEM p l ∧ MEM q l`
       by (`MEM p (procsOf (Com  p x q y c)) ∧ MEM q (procsOf (Com  p x q y c))`
          by rw [MEM,pchorSemTheory.procsOf_def,nub'_def]
          \\ metis_tac [MEM_PERM])
    \\ `PERM l' l`
       by (ho_match_mp_tac PERM_ALL_DISTINCT
          \\ rw [Abbr `l'`]
          \\ Cases_on `p ≠ x'` \\ Cases_on `q ≠ x'`
          \\ rw [MEM_FILTER])
    \\ metis_tac [PERM_pchor_compile_network_reduction]
QED

(* `Sel` instance of `PERM_pchor_compile_network_reduction` with more
   specific assumptions
*)
Theorem pchor_compile_network_SEL:
  ∀s ^pchor p b q l.
   PERM (procsOf (Sel  p b q c)) l
   ∧ p ≠ q
   ∧ reduction^* (compile_network s (Sel p b q c) (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
                 (compile_network s            c  (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
   ⇒ reduction^* (compile_network s (Sel p b q c) l) (compile_network s c l)
Proof
    rw []
    \\ Q.ABBREV_TAC `l' = p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l`
    \\ `ALL_DISTINCT l`
       by metis_tac [ALL_DISTINCT_PERM,pchorSemTheory.procsOf_all_distinct]
    \\ `ALL_DISTINCT l'`
       by rw [Abbr `l'`,ALL_DISTINCT,MEM_FILTER,FILTER_ALL_DISTINCT]
    \\ `MEM p l ∧ MEM q l`
       by (`MEM p (procsOf (Sel  p b q c)) ∧ MEM q (procsOf (Sel p b q c))`
          by rw [MEM,pchorSemTheory.procsOf_def,nub'_def]
          \\ metis_tac [MEM_PERM])
    \\ `PERM l' l`
       by (ho_match_mp_tac PERM_ALL_DISTINCT
          \\ rw [Abbr `l'`]
          \\ Cases_on `p ≠ x` \\ Cases_on `q ≠ x`
          \\ rw [MEM_FILTER])
    \\ metis_tac [PERM_pchor_compile_network_reduction]
QED

val _ = export_theory ()

open preamble endpointLangTheory bakery_to_endpointTheory
              endpointSemanticsTheory endpointPropsTheory
              semBakeryTheory;

val _ = new_theory"endpointCong"

(* Given a network, returns all the process identifiers
   (note it can give duplicated results
*)
val network_procs_def = Define`
  network_procs NNil = []
∧ network_procs (NPar n1 n2) = network_procs n1 ++ network_procs n2
∧ network_procs (NEndpoint p s e) = [p]
`;

(* Projected networks identity over `network_procs` *)
val network_procs_compile_id = Q.store_thm("network_procs_compile_id",
  `∀s c l. network_procs (compile_network s c l) = l`,
  rw [] >> Induct_on `l`
  \\ rw [network_procs_def,compile_network_gen_def]
);

(* Right End Point Network (`REPN`) is a network with only `NEndpoint` on the left
   and either `NNil` or other `REPN` on the right

                NPar________________
                 |                  |
                 |                 NPar_______(...)________
                 |                  |                      |
                NEndpoint p s e    NEndpoint p' s' e'     NNil
*)
val REPN_def = Define `
  REPN NNil                        = T
∧ REPN (NEndpoint _ _ _)           = F
∧ REPN (NPar (NEndpoint _ _ _) ep) = REPN ep
∧ REPN _                           = F
`;

(* A particular kind of congruence that only allows swaps to the right *)
val (epn_rcong_rules, epn_rcong_ind, epn_rcong_cases) = Hol_reln `
(* Basic congruence rules *)
  (* Symmetric *)
  (∀c. epn_rcong c c)
  (* Reflexive *)
∧ (∀c1 c2.
    epn_rcong c1 c2
    ⇒ epn_rcong c2 c1)
  (* Transitive *)
∧ (∀c1 c2 c3.
    epn_rcong c1 c2
    ∧ epn_rcong c2 c3
    ⇒ epn_rcong c1 c3)
  (* Swap *)
∧ (∀n1 n2 n3.
    epn_rcong (NPar n1 (NPar n2 n3))
              (NPar n2 (NPar n1 n3)))
  (* Structural rules *)
∧ (∀n1 n2 n2'.
    epn_rcong n2 n2'
    ⇒ epn_rcong (NPar n1 n2)
                (NPar n1 n2'))
`;

val _ = Parse.add_infix("θ≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("θ≅",``epn_rcong``);

val _ = zip ["epn_rcong_refl", "epn_rcong_sym", "epn_rcong_trans"
            ,"epn_rcong_swap", "epn_rcong_pair"]
            (CONJUNCTS epn_rcong_rules) |> map save_thm;

val epn_rcong_sym   =  theorem "epn_rcong_sym";
val epn_rcong_refl  =  theorem "epn_rcong_refl";
val epn_rcong_trans =  theorem "epn_rcong_trans";
val epn_rcong_swap  =  theorem "epn_rcong_swap";
val epn_rcong_npair =  theorem "epn_rcong_pair";

(* Two projected (using `compile_network`) networks are congruent as long as
   the list of projected process are permutable
*)
val PERM_rcong_compile_network = Q.store_thm("PERM_rcong_compile_network",
  `∀l l' s c. PERM l l' ⇒ compile_network s c l θ≅ compile_network s c l'`,
  rpt GEN_TAC
  \\ `∀l l'. PERM l l' ⇒ compile_network s c l θ≅ compile_network s c l'`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac PERM_IND
  \\ rw [compile_network_gen_def,epn_rcong_rules]
  >- (MAP_EVERY Q.ABBREV_TAC
       [ `s1 = <|bindings := projectS x s; queue := []|>`
       , `n1 = (project' x c)`
       , `s2 = <|bindings := projectS y s; queue := []|>`
       , `n2 = (project' y c)`
       , `n3 = compile_network s c l`
       , `n4 = compile_network s c l'`]
     \\ ho_match_mp_tac epn_rcong_trans
     \\ Q.EXISTS_TAC `NPar (NEndpoint y s2 n2) (NPar (NEndpoint x s1 n1) n3)`
     \\ rw [epn_rcong_rules])
  >- (metis_tac [epn_rcong_trans])
);

(* If two (starting) networks (`n1`,`n1'`) are congruent then a
   transition with label `t` from any of them will imply there
   exists a transition from the opposite network with the same label `t`
   and the resuting networks `n2` `n2` will also be congruent

               trans n1  t n2
  n1-------------------------------------n2
   |                                     |
  θ≅                                    θ≅
   |           trans n1' t n2'           |
  n1'------------------------------------n2'

*)
val epn_rcong_imp_trans = Q.store_thm("epn_rcong_imp_trans",
  `∀n1 n1'.
    n1 θ≅ n1'
    ⇒ ∀t.(∀n2'. trans n1' t n2' ⇒ ∃n2.  trans n1  t n2  ∧ n2 θ≅ n2')
       ∧ (∀n2.  trans n1  t n2  ⇒ ∃n2'. trans n1' t n2' ∧ n2' θ≅ n2)`,
  let val trans_metis = metis_tac [epn_rcong_rules,endpointSemanticsTheory.trans_rules]
      val asm_epn_cases = (ASSUME_TAC o ONCE_REWRITE_RULE [endpointSemanticsTheory.trans_cases])
      val epn_rcong_tac  =
          fn (asm,g) =>
             let val is_trans = (curry op = "trans") o term_to_string o fst o strip_comb
                 val trans_match = fn t => is_comb t andalso is_trans t
                 val trans_terms = map (snd o strip_comb) (filter trans_match asm)
                 val pairs = map (fn t => (el 1 t,el 3 t)) trans_terms
                 (* val _ = map (print_term o fst) pairs *)
                 (* val _ = map (print_term o snd) pairs *)
                 val trans_g = g |> snd o dest_exists
                                 |> fst o dest_conj
                                 |> snd o strip_comb
                                 |> el 1
                 val the_g = subst (map (op |->) pairs) trans_g
             in EXISTS_TAC the_g (asm,g)
             end
      val epn_tac = epn_rcong_tac >> trans_metis
  in
  ho_match_mp_tac (theorem"epn_rcong_strongind")
  \\ rw []
  >- trans_metis >- trans_metis >- trans_metis >- trans_metis
  \\ pop_assum asm_epn_cases >> rw []
  \\ TRY (qpat_x_assum `trans (NPar _ _) _ _` asm_epn_cases \\ rw [])
  \\ res_tac >> epn_tac
  end
);

(* A more human readable versin of `epn_rcong_imp_trans` *)
val epn_rcong_trans' = Q.store_thm("epn_rcong_trans'",
  `∀n1 n2 n1' t.
    n1 θ≅ n1'
    ∧ trans n1 t n2
    ⇒ ∃n2'. trans n1' t n2' ∧ n2 θ≅ n2'`,
  metis_tac [epn_rcong_imp_trans,epn_rcong_rules]
);

(* An extended RTC version of `epn_rcong_trans'` *)
val epn_rcong_reduction = Q.store_thm("epn_rcong_reduction",
  `∀n1 n2 n1'.
    n1 θ≅ n1'
    ∧ reduction^* n1 n2
    ⇒ ∃n2'. reduction^* n1' n2' ∧ n2 θ≅ n2'`,
  rpt GEN_TAC
  \\ `∀n1 n2. reduction^* n1 n2
       ⇒ ∀n1'. n1 θ≅ n1'
          ⇒ ∃n2'. reduction^* n1' n2' ∧ n2 θ≅ n2'`
     suffices_by metis_tac []
  \\ ho_match_mp_tac RTC_INDUCT \\ rw []
  >- (Q.EXISTS_TAC `n1'` \\ rw [])
  >- (fs [reduction_def]
     \\ IMP_RES_TAC epn_rcong_trans'
     \\ pop_assum (K ALL_TAC)
     \\ RES_TAC
     \\ fs [GSYM reduction_def]
     \\ metis_tac [RTC_RULES])
);

(* If a network is REPN and has no processes in it the is NNil *)
val network_procs_NNil = Q.store_thm("network_procs_NNil",
  `∀n. REPN n ∧ network_procs n = [] ⇒ n = NNil`,
  Induct_on `n`
  >- rw []
  >- (Cases_on `n`
     \\ Cases_on `n'`
     \\ rw [REPN_def,network_procs_def])
  >- rw [REPN_def,network_procs_def]
);

(* Projected networks are always REPN *)
val REPN_compile_network = Q.store_thm("REPN_compile_network",
  `∀s c l. REPN (compile_network s c l)`,
  Induct_on `l` >> rw [REPN_def,compile_network_gen_def]
);

(* Structural `REPN` reduction over `NPar` to the right *)
val REPN_NPar = Q.store_thm("REPN_NPar",
  `∀c c'. REPN (NPar c c') ⇒ REPN c'`,
  Cases_on `c` >> rw [REPN_def]
);

(* Structural `REPN` reduction over `NPar` to the left *)
val REPN_NPar_isNEndpoint = Q.store_thm("REPN_NPar_isNEndpoint",
  `∀c c'. REPN (NPar c c') ⇒ ∃ p s e. c = NEndpoint p s e`,
  Cases_on `c` >> rw [REPN_def]
);

(* endpoint network congruence preserves `REPN` *)
val rcong_REPN = Q.store_thm("rcong_REPN",
  `∀c c'. c θ≅ c' ⇒ (REPN c ⇔ REPN c')`,
  ho_match_mp_tac epn_rcong_ind
  \\ rw []
  >- (EQ_TAC
     \\ rw []
     \\ IMP_RES_TAC REPN_NPar
     \\ IMP_RES_TAC REPN_NPar
     \\ IMP_RES_TAC REPN_NPar_isNEndpoint
     \\ rw [REPN_def])
  >- (Cases_on `n1` \\ rw [REPN_def])
);

(* endpoint network congruence preserves all t
   he contents (endpoints) of the network
*)
val rcong_PERM_enpoints = Q.store_thm("rcong_PERM_enpoints",
  `∀ep ep'. ep θ≅ ep' ⇒ PERM (endpoints ep) (endpoints ep')`,
  ho_match_mp_tac epn_rcong_ind
  \\ rw []
  >- metis_tac [PERM_SYM,PERM_TRANS]
  >- metis_tac [PERM_SYM,PERM_TRANS]
  >- rw [endpoints_def,PERM_SWAP_L_AT_FRONT]
  >- rw [endpoints_def,PERM_APPEND_IFF]
);

(* `epnList` constructs a network from a list of endpoints (as pairs) *)
val epnList_def = Define`
  epnList [] = NNil
∧ epnList ((p,s,e)::l) = NPar (NEndpoint p s e) (epnList l)
`;

(* `epnList` networks are always REPN *)
val epnList_REPN = Q.store_thm("epnList_REPN",
  `∀l. REPN (epnList l)`,
  Induct_on `l` \\ rw [REPN_def,epnList_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw [REPN_def,epnList_def]
);

(* `epnList o endpoints = id` *)
val epnList_id = Q.store_thm("epnList_id",
  `∀l. l = endpoints (epnList l)`,
  Induct_on `l` \\ rw [endpoints_def,epnList_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw [endpoints_def,epnList_def]
);

(* IF two REPN networks have the same contents THEN they are congruent *)
val REPN_PERM_rcong = Q.store_thm("REPN_PERM_rcong",
  `∀ep ep'.
    PERM (endpoints ep) (endpoints ep')
    ∧ REPN ep ∧ REPN ep'
    ⇒ ep θ≅ ep'`,
  rpt GEN_TAC
  \\ `∀l l'. PERM l l'
       ⇒ ∀ep ep'. l = endpoints ep
          ∧ l' = endpoints ep'
          ∧ REPN ep ∧ REPN ep'
          ⇒ ep θ≅ ep'`
     suffices_by metis_tac []
  \\ ho_match_mp_tac PERM_IND
  \\ let val epn_cases = Cases_on `ep` \\ Cases_on `ep'`
     \\ fs [endpoints_def,epn_rcong_refl,REPN_def]
     \\ IMP_RES_TAC REPN_NPar_isNEndpoint
     \\ IMP_RES_TAC REPN_NPar
     \\ fs [endpoints_def]
     in rw [] >- epn_cases
     >- (epn_cases
        \\ first_x_assum (ASSUME_TAC o Q.SPECL [`n0`,`n0'`])
        \\ rfs [epn_rcong_npair])
     >- (epn_cases \\ Cases_on `n0` \\ Cases_on `n0'`
        \\ fs [endpoints_def,epn_rcong_refl,REPN_def]
        \\ IMP_RES_TAC REPN_NPar_isNEndpoint
        \\ IMP_RES_TAC REPN_NPar
        \\ fs [endpoints_def]
        \\ first_x_assum (ASSUME_TAC o Q.SPECL [`n0''`,`n0`])
        \\ rfs []
        \\ metis_tac [epn_rcong_rules])
     >- (qpat_x_assum `∀x y. _ ⇒ _` (ASSUME_TAC o Q.SPECL [`epnList l'`,`ep'`])
        \\ qpat_x_assum `∀x y. _ ⇒ _` (ASSUME_TAC o Q.SPECL [`ep`,`epnList l'`])
        \\ fs [epnList_id,epnList_REPN]
        \\ RES_TAC
        \\ metis_tac [epn_rcong_trans])
     end
);

(* IF two REPN networks are congruent and have the same left side,
   their right side must be congruent
*)
val epn_rcong_NPar = Q.store_thm("epn_rcong_NPar",
  `∀n1 n2 n3. NPar n1 n2 θ≅ NPar n1 n3
    ∧ REPN (NPar n1 n2)
    ∧ REPN (NPar n1 n3)
    ⇒ n2 θ≅ n3`,
   rw []
   \\ IMP_RES_TAC REPN_NPar_isNEndpoint
   \\ fs []
   \\ rpt (qpat_x_assum `_ = _` (K ALL_TAC))
   \\ IMP_RES_TAC rcong_PERM_enpoints
   \\ fs [endpoints_def]
   \\ IMP_RES_TAC REPN_NPar
   \\ IMP_RES_TAC REPN_PERM_rcong
);

(* Every element in a projected choreography is a projection of
   state and endpoint for an specific process

   PS: this is obvious, but it's convenient to have
*)
val compile_network_MEM_elem = Q.store_thm("compile_network_MEM_elem",
  `∀p s e c s' l.
    MEM (p,s',e) (endpoints (compile_network s c l))
    ⇒ s' = <|bindings := projectS p s; queue := []|>
      ∧ e = project' p c`,
  rpt GEN_TAC
  \\ Induct_on `l`
  \\ rw [MEM,compile_network_gen_def,endpoints_def]
  \\ fs []
);

(* One can pull (using congruence) any element of a projected network
   to be the top-most endpoint
*)
val compile_network_pull = Q.store_thm("compile_network_pull",
  `∀p s e s' c l ep.
    ALL_DISTINCT l
    ∧ MEM (p,s,e) (endpoints (compile_network s' c l))
    ∧ ep = compile_network s' c (FILTER ($≠ p) l)
    ⇒ compile_network s' c l θ≅ NPar (NEndpoint p s e) ep`,
  rw []
  \\ Induct_on `l` \\ rw []
  >- fs [compile_network_gen_def,endpoints_def,MEM]
  >- (fs [compile_network_gen_def,endpoints_def,MEM] \\ fs []
     \\ Q.ABBREV_TAC `h_ep = NEndpoint h <|bindings := projectS h s'; queue := []|> (project' h c)`
     \\ ho_match_mp_tac epn_rcong_trans
     \\ Q.EXISTS_TAC `NPar h_ep
                           (NPar (NEndpoint p s e)
                           (compile_network s' c (FILTER (λy. p ≠ y) l)))`
     \\ rw [Abbr `h_ep`, epn_rcong_swap]
     \\ ho_match_mp_tac epn_rcong_npair
     \\ rw [])
  >- (fs [compile_network_gen_def,endpoints_def,MEM] \\ fs []
     \\ `¬MEM h l ⇒ FILTER ($≠ h) l = l`
        by (rpt (pop_assum (K ALL_TAC))
           \\ Induct_on `l`
           \\ rw [MEM_FILTER,FILTER])
     \\ metis_tac [epn_rcong_refl,compile_network_MEM_elem])
);

(* Any network that is congruent with a projected network, can be
   expressed as a projection (using `compile_network`)
*)
val compile_network_rcong = Q.store_thm("compile_network_rcong",
  `∀s c l ep. compile_network s c l θ≅ ep ∧ ALL_DISTINCT l
    ⇒ ep = compile_network s c (network_procs ep)`,
  Induct_on `ep`
  >- (rw [compile_network_gen_def,network_procs_def])
  >- (rw []
     \\ `REPN (compile_network s c l)`
        by rw [REPN_compile_network]
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
        by (rw [Abbr `l'`] >> metis_tac [compile_network_pull,epn_rcong_sym])
     \\ `NPar (NEndpoint p s' e) l' θ≅ NPar (NEndpoint p s' e) ep'`
        by (rw [Abbr `l'`] >> metis_tac [epn_rcong_trans])
     \\ `l' θ≅ ep'`
        by (rw [Abbr `l'`] >> metis_tac [epn_rcong_NPar,rcong_REPN])
     \\ rw [compile_network_gen_def,network_procs_def,compile_network_MEM_elem]
     \\ IMP_RES_TAC compile_network_MEM_elem
     \\ UNABBREV_ALL_TAC
     \\ metis_tac [FILTER_ALL_DISTINCT])
 >- (rw []
    \\ `REPN (compile_network s' c l')` by rw [REPN_compile_network]
    \\ IMP_RES_TAC rcong_REPN
    \\ fs [REPN_def])
);

(* Networks preserve the number of process over transitions *)
val network_procs_trans = Q.store_thm("network_procs_trans",
  `∀ep t ep'. trans ep t ep' ⇒ network_procs ep' = network_procs ep`,
  ho_match_mp_tac endpointSemanticsTheory.trans_ind
  \\ rw [network_procs_def]
);

val network_procs_reduction = Q.store_thm("network_procs_reduction",
  `∀ep ep'. reduction^* ep ep' ⇒ network_procs ep' = network_procs ep`,
  ho_match_mp_tac RTC_INDUCT
  \\ rw [reduction_def]
  \\ IMP_RES_TAC network_procs_trans
);

(* A transitions between projected networks with list of process `l1`
   implies the same transition can be made between projected networks
   with a list of processes `l2` as long as `l2` is a permutation of `l1`
   (`PERM l1 l2`)


                             trans with t
  compile_network s c l1----------------------compile_network s c' l1'
         |            |                              |
        θ≅           PERM                           θ≅
         |            |      trans with t            |
  compile_network s c l2----------------------compile_network s c' l2'

  PS: I believe this particular form is useless since there is no
      step of a choreography that can be done in one network transition
      `trans (compile_network s c l1) t (compile_network s c' l1)`
      however I'm including it for completeness
*)
val PERM_compile_network_trans = Q.store_thm("PERM_compile_network_trans",
  `∀s c c' t l1 l2.
    PERM l1 l2
    ∧ ALL_DISTINCT l1
    ∧ trans (compile_network s c l1) t (compile_network s c' l1)
    ⇒ trans (compile_network s c l2) t (compile_network s c' l2)`,
    rw []
    \\ `compile_network s c l1 θ≅ compile_network s c l2`
       by rw [PERM_rcong_compile_network]
    \\ IMP_RES_TAC epn_rcong_trans'
    \\ IMP_RES_TAC network_procs_trans
    \\ IMP_RES_TAC compile_network_rcong
    \\ rfs [network_procs_compile_id]
    \\ rw []
);


(* An RTC variant of `PERM_compile_network_trans`, way more relevant and useful *)
val PERM_compile_network_reduction = Q.store_thm("PERM_compile_network_reduction",
  `∀s c c' l1 l2.
    PERM l1 l2
    ∧ ALL_DISTINCT l1
    ∧ reduction^* (compile_network s c l1) (compile_network s c' l1)
    ⇒ reduction^* (compile_network s c l2) (compile_network s c' l2)`,
    rw []
    \\ `compile_network s c l1 θ≅ compile_network s c l2`
       by rw [PERM_rcong_compile_network]
    \\ IMP_RES_TAC epn_rcong_reduction
    \\ IMP_RES_TAC network_procs_reduction
    \\ IMP_RES_TAC compile_network_rcong
    \\ rfs [network_procs_compile_id]
    \\ rw []
);

(* `Com` instance of `PERM_compile_network_reduction` with more
   specific assumptions
*)
val compile_network_COM = Q.store_thm("compile_network_COM",
 `∀s c p x q y l.
   PERM (procsOf (Com  p x q y c)) l
   ∧ p ≠ q
   ∧ reduction^* (compile_network s (Com  p x q y c) (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
                 (compile_network s               c  (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
   ⇒ reduction^* (compile_network s (Com  p x q y c) l) (compile_network s c l)`,
    rw []
    \\ Q.ABBREV_TAC `l' = p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l`
    \\ `ALL_DISTINCT l`
       by metis_tac [ALL_DISTINCT_PERM,procsOf_all_distinct]
    \\ `ALL_DISTINCT l'`
       by rw [Abbr `l'`,ALL_DISTINCT,MEM_FILTER,FILTER_ALL_DISTINCT]
    \\ `MEM p l ∧ MEM q l`
       by (`MEM p (procsOf (Com  p x q y c)) ∧ MEM q (procsOf (Com  p x q y c))`
          by rw [MEM,procsOf_def,nub'_def]
          \\ metis_tac [MEM_PERM])
    \\ `PERM l' l`
       by (ho_match_mp_tac PERM_ALL_DISTINCT
          \\ rw [Abbr `l'`]
          \\ Cases_on `p ≠ x'` \\ Cases_on `q ≠ x'`
          \\ rw [MEM_FILTER])
    \\ metis_tac [PERM_compile_network_reduction]
);

(* `Sel` instance of `PERM_compile_network_reduction` with more
   specific assumptions
*)
val compile_network_SEL = Q.store_thm("compile_network_SEL",
 `∀s c p b q l.
   PERM (procsOf (Sel  p b q c)) l
   ∧ p ≠ q
   ∧ reduction^* (compile_network s (Sel p b q c) (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
                 (compile_network s            c  (p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l))
   ⇒ reduction^* (compile_network s (Sel p b q c) l) (compile_network s c l)`,
    rw []
    \\ Q.ABBREV_TAC `l' = p::q::FILTER (λx. p ≠ x ∧ q ≠ x) l`
    \\ `ALL_DISTINCT l`
       by metis_tac [ALL_DISTINCT_PERM,procsOf_all_distinct]
    \\ `ALL_DISTINCT l'`
       by rw [Abbr `l'`,ALL_DISTINCT,MEM_FILTER,FILTER_ALL_DISTINCT]
    \\ `MEM p l ∧ MEM q l`
       by (`MEM p (procsOf (Sel  p b q c)) ∧ MEM q (procsOf (Sel p b q c))`
          by rw [MEM,procsOf_def,nub'_def]
          \\ metis_tac [MEM_PERM])
    \\ `PERM l' l`
       by (ho_match_mp_tac PERM_ALL_DISTINCT
          \\ rw [Abbr `l'`]
          \\ Cases_on `p ≠ x` \\ Cases_on `q ≠ x`
          \\ rw [MEM_FILTER])
    \\ metis_tac [PERM_compile_network_reduction]
);

val _ = export_theory ()

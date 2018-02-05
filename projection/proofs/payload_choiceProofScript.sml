open preamble payloadLangTheory payloadSemanticsTheory payloadPropsTheory payload_choiceTheory

val _ = new_theory "payload_choiceProof";

val compile_network_preservation_send = Q.store_thm("compile_network_preservation_send",
  `∀p1 p2 q1 d q2 conf fv.
    trans conf p1 (LSend q1 d q2) p2
    ==> trans conf (compile_network_fv fv p1) (LSend q1 d q2) (compile_network_fv fv p2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def]
  >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[]);

val compile_network_preservation_receive = Q.store_thm("compile_network_preservation_receive",
  `∀p1 p2 q1 d q2 conf fv.
    trans conf p1 (LReceive q1 d q2) p2
    ==> trans conf (compile_network_fv fv p1) (LReceive q1 d q2) (compile_network_fv fv p2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def]
  >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[]);

val add_state_def = Define `
  (add_state p v d NNil = NNil)
  /\ (add_state p v d (NEndpoint q s e) =
      if p = q then NEndpoint q (s with bindings := s.bindings |+ (v,d)) e
      else NEndpoint q s e
     )
  /\ (add_state p v d (NPar n1 n2) = NPar (add_state p v d n1) (add_state p v d n2))
`

val junkcong_add_state_free_vars = Q.store_thm("junkcong_add_state_free_vars",
  `!n v fv p d. ~MEM v (free_var_names_network n) /\
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  Induct
  >> rpt strip_tac
  >- rw[add_state_def,junkcong_refl]
  >- (fs[free_var_names_network_def]
      >> rpt (first_x_assum drule >> strip_tac)
      >> fs[add_state_def]
      >> match_mp_tac junkcong_par >> simp[])
  >- (rw[add_state_def,junkcong_refl]
      >> match_mp_tac junkcong_add_junk
      >> fs[free_var_names_network_def]));

val free_names_are_names_endpoint = Q.store_thm("free_names_are_names_endpoint",
  `!e v. MEM v (free_var_names_endpoint e) ==> MEM v (var_names_endpoint e)`,
  Induct >> rpt strip_tac
  >> fs[var_names_endpoint_def,free_var_names_endpoint_def,MEM_FILTER]);

val free_names_are_names = Q.store_thm("free_names_are_names",
  `!n v. MEM v (free_var_names_network n) ==> MEM v (var_names_network n)`,
  Induct >> rpt strip_tac
  >> fs[var_names_network_def,free_var_names_network_def,free_names_are_names_endpoint]);

val junkcong_add_state_free_vars = Q.store_thm("junkcong_add_state_free_vars",
  `!n v fv p d. ~MEM v (free_var_names_network n) /\
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  Induct
  >> rpt strip_tac
  >- rw[add_state_def,junkcong_refl]
  >- (fs[free_var_names_network_def]
      >> rpt (first_x_assum drule >> strip_tac)
      >> fs[add_state_def]
      >> match_mp_tac junkcong_par >> simp[])
  >- (rw[add_state_def,junkcong_refl]
      >> match_mp_tac junkcong_add_junk
      >> fs[free_var_names_network_def]));

val junkcong_add_state = Q.store_thm("junkcong_add_state",
  `!n v fv p d. ~MEM v (var_names_network n) /\
   v ∈ fv
  ==> junkcong fv n (add_state p v d n)`,
  metis_tac[junkcong_add_state_free_vars,free_names_are_names]);

(*
fun largest_match avd t1 t2 =
  case dest_term t1 of
    VAR(n,_) =>
    if HOLset.member(avd,n) then ([],[])
    else match_term t1 t2
  | COMB(trator,trand) =>
    if is_comb t2 then
      let val (tms1,tys1) = largest_match avd trator (rator t2)
          val (tms2,tys2) = largest_match avd trand (rand t2)
      in (tms1@tms2,tys1@tys2) end
    else ([],[])
  | LAMB(arg,body) =>
    if is_abs t2 then
      ([],[]) (*todo*)
    else
      ([],[])
  | _ => ([],[])

fun fudge_match avd t1 t2 =
  case dest_term t1 of
    VAR(n,_) =>
    ([],[])
  | COMB(trator,trand) =>
    if is_comb t2 then
      case (term_eq trator (rator t2),term_eq trand (rand t2)) of
          (T,T) => ([],[])
        | (F,F) => 
          let val tys = match_type (type_of t1) (type_of t2)
          in
            ([inst tys t1|->t2],tys)
          end
        | (T,F) => 
      let val (tms1,tys1) = fudge_match avd trator (rator t2)
          val (tms2,tys2) = fudge_match avd trand (rand t2)
      in (tms1@tms2,tys1@tys2) end
    else
      let val tys = match_type (type_of t1) (type_of t2)
      in
        ([inst tys t1|->t2],tys)
      end
  | _ =>
    if term_eq t1 t2 then ([],[]) else
    let val tys = match_type (type_of t1) (type_of t2)
      in
        ([inst tys t1|->t2],tys)
    end

fun mk_largest_match t1 t2 =
  let val (tms,tys) = largest_match (HOLset.empty String.compare) t1 t2 in
    t1 |> inst tys |> subst tms
  end


fun partial_match_mp_tac thm : tactic =
  let
    val lconsts =
        HOLset.intersection (FVL [concl thm] empty_tmset, hyp_frees thm)
    val hyptyvars = HOLset.listItems (hyp_tyvars thm)
    val (gvs, imp) = strip_forall (concl thm)    
  in
    fn (A,g) =>
       let
         val (ant, conseq) =
             with_exn dest_imp imp (ERR "MATCH_MP_TAC" "Not an implication")
         val (cvs, con) = strip_forall conseq
         val th1 = SPECL cvs (UNDISCH (SPECL gvs thm))
         val (vs, evs) = partition (C Term.free_in con) gvs
         val th2 = uncurry DISCH (itlist efn evs (ant, th1))
         val (vs, gl) = strip_forall g       
         val ins = largest_match (HOLset.empty String.compare) con gl
         val ith = INST_TY_TERM ins th2
         val fins = fudge_match (concl ith) g
         val 
  end 
  *)         

val compile_network_endpoints = Q.store_thm("compile_network_endpoints",
  `!fv n. MAP FST (endpoints(compile_network_fv fv n)) = MAP FST (endpoints n)`,
  Induct_on `n` >> rw[endpoints_def,compile_network_fv_def]);

val compile_network_endpoints = Q.store_thm("compile_network_endpoints",
  `!fv n. MAP FST (endpoints(compile_network_fv fv n)) = MAP FST (endpoints n)`,
  Induct_on `n` >> rw[endpoints_def,compile_network_fv_def]);

val not_MEM_add_state = Q.store_thm("not_MEM_add_state",
  `!n q fv d. ¬MEM q (MAP FST (endpoints n)) ==> add_state q fv d n = n`,
  Induct >> rw[endpoints_def,add_state_def]);

val compile_network_preservation_int_choice_T = Q.store_thm(
  "compile_network_preservation_int_choice_T",
  `∀n1 n2 q1 d q2 fv conf.
    conf.payload_size > 0 /\
    ALL_DISTINCT (MAP FST (endpoints n1)) /\
    trans conf n1 (LIntChoice q1 T q2) n2
    ==> list_trans conf (compile_network_fv fv n1)
                   [LTau;LSend q1 [6w;1w] q2]
                   (add_state q1 fv [1w] (compile_network_fv fv n2))
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `_ > 0` mp_tac
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (qmatch_goalsub_abbrev_tac `Let _ _ _ a1`
      >> qexists_tac `NEndpoint p1
                        (s with bindings := s.bindings
                                              |+ (fv,
                                                  (K [1w])(MAP (THE o FLOOKUP s.bindings) [])))
                        a1`
      >> conj_tac
      >- (match_mp_tac trans_let >> simp[])
      >> simp[]
      >> unabbrev_all_tac
      >> PURE_ONCE_REWRITE_TAC [DROP_0 |> GEN_ALL |> ISPEC ``[1w:8 word]`` |> GSYM]
      >> match_mp_tac trans_send_last_payload >> fs[FLOOKUP_UPDATE])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum drule >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_l])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum(qspec_then `q1` (drule o CONTRAPOS))
      >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_r]));

val compile_network_preservation_int_choice_F = Q.store_thm(
  "compile_network_preservation_int_choice_F",
  `∀n1 n2 q1 d q2 fv conf.
    conf.payload_size > 0 /\
    ALL_DISTINCT (MAP FST (endpoints n1)) /\
    trans conf n1 (LIntChoice q1 F q2) n2
    ==> list_trans conf (compile_network_fv fv n1)
                   [LTau;LSend q1 [6w;0w] q2]
                   (add_state q1 fv [0w] (compile_network_fv fv n2))
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `_ > 0` mp_tac
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (qmatch_goalsub_abbrev_tac `Let _ _ _ a1`
      >> qexists_tac `NEndpoint p1
                        (s with bindings := s.bindings
                                              |+ (fv,
                                                  (K [0w])(MAP (THE o FLOOKUP s.bindings) [])))
                        a1`
      >> conj_tac
      >- (match_mp_tac trans_let >> simp[])
      >> simp[]
      >> unabbrev_all_tac
      >> PURE_ONCE_REWRITE_TAC [DROP_0 |> GEN_ALL |> ISPEC ``[0w:8 word]`` |> GSYM]
      >> match_mp_tac trans_send_last_payload >> fs[FLOOKUP_UPDATE])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum drule >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_l])
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> imp_res_tac sender_is_endpoint
      >> imp_res_tac endpoint_names_trans >> fs[compile_network_endpoints]
      >> rfs[] >> first_x_assum(qspec_then `q1` (drule o CONTRAPOS))
      >> strip_tac
      >> fs[compile_network_endpoints,not_MEM_add_state]
      >> metis_tac[trans_par_r]));

val compile_network_preservation_ext_choice_T = Q.store_thm("compile_network_preservation_ext_choice_T",
  `∀n1 n2 q1 d q2 fv conf.
    conf.payload_size > 0 /\
    ALL_DISTINCT (MAP FST (endpoints n1)) /\
    trans conf n1 (LExtChoice q1 T q2) n2
    ==> trans conf (compile_network_fv fv n1)
                   (LReceive q1 [6w;1w] q2)
                   (compile_network_fv fv n2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `_ > 0` mp_tac
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (match_mp_tac trans_enqueue >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_l >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_r >> first_x_assum ACCEPT_TAC));

val compile_network_preservation_ext_choice_F = Q.store_thm("compile_network_preservation_ext_choice_T",
  `∀n1 n2 q1 d q2 fv conf.
    conf.payload_size > 0 /\
    ALL_DISTINCT (MAP FST (endpoints n1)) /\
    trans conf n1 (LExtChoice q1 F q2) n2
    ==> trans conf (compile_network_fv fv n1)
                   (LReceive q1 [6w;0w] q2)
                   (compile_network_fv fv n2)
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `_ > 0` mp_tac
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
        list_trans_def]
  >- (match_mp_tac trans_enqueue >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_l >> first_x_assum ACCEPT_TAC)
  >- (first_x_assum (qspec_then `fv` assume_tac)
      >> rfs[endpoints_def,ALL_DISTINCT_APPEND]
      >> match_mp_tac trans_par_r >> first_x_assum ACCEPT_TAC));

val trans_var_names_mono = Q.store_thm("trans_var_names_mono",
  `!conf n1 alpha n2 fv.
    trans conf n1 alpha n2
    /\ MEM fv (var_names_network n2) ==> MEM fv (var_names_network n1)`,
  rpt strip_tac
  >> qpat_x_assum `MEM _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[var_names_network_def,var_names_endpoint_def]);

val MEM_free_vars_compile_endpoint = Q.store_thm("MEM_free_vars_compile_endpoint",
  `!p fv. ~MEM fv (var_names_endpoint p) ==>
          MEM fv (free_var_names_endpoint (compile_endpoint fv p)) = MEM fv (free_var_names_endpoint p)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_endpoint_def,compile_endpoint_def,MEM_FILTER]
  >> fs[var_names_endpoint_def] >> metis_tac[free_names_are_names_endpoint]);

val MEM_free_vars_compile_network = Q.store_thm("MEM_free_vars_compile_network",
  `!n fv. ~MEM fv (var_names_network n) ==>
          MEM fv (free_var_names_network (compile_network_fv fv n)) = MEM fv (free_var_names_network n)`,
  Induct >> rpt strip_tac
  >> rw[free_var_names_network_def,compile_network_fv_def,MEM_FILTER]
  >> fs[var_names_network_def,MEM_free_vars_compile_endpoint]);

val compile_endpoint_support = Q.store_thm("compile_endpoint_support",
  `!e fv. MEM fv (free_var_names_endpoint (compile_endpoint fv e))
   ==> MEM fv (free_var_names_endpoint e)
  `,
  Induct >> rpt strip_tac
  >> fs[compile_endpoint_def,free_var_names_endpoint_def,MEM_FILTER]
  >> every_case_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]);

val compile_network_support = Q.store_thm("compile_network_support",
  `!n fv. MEM fv (free_var_names_network (compile_network_fv fv n))
   ==> MEM fv (free_var_names_network n)
  `,
  Induct >> rpt strip_tac
  >> fs[compile_network_fv_def,free_var_names_network_def,
        compile_endpoint_support]);

(* TODO: move *)
val junkcong_add_junk'' = Q.store_thm("junkcong_add_junk''",
  `∀p s q e v fvs d.
     v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e) ⇒
     junkcong fvs (NEndpoint p (s with queue := q) e)
     (NEndpoint p (s with <|bindings := s.bindings |+ (v,d); queue := q|>) e)`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = s with queue := q`
  >> `s.bindings = a1.bindings` by(unabbrev_all_tac >> simp[])
  >> fs[junkcong_add_junk]);

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀n1 n2 q1 d q2 fv conf.
    conf.payload_size > 0 /\
    ALL_DISTINCT (MAP FST (endpoints n1)) /\
    ¬MEM fv (var_names_network n1) /\
    trans conf n1 LTau n2
    ==> ?n3. (reduction conf)^* (compile_network_fv fv n1) n3 /\
             junkcong {fv} (compile_network_fv fv n2) n3
  `,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum `_ > 0` mp_tac
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> qpat_x_assum `¬MEM _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`,`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* com-l *)
     (imp_res_tac compile_network_preservation_send
      >> imp_res_tac compile_network_preservation_receive
      >> rpt(first_x_assum(qspec_then `fv` assume_tac))
      >> imp_res_tac trans_com_l
      >> fs[GSYM reduction_def,compile_network_fv_def]
      >> metis_tac[RTC_SINGLE,junkcong_refl])
  >- (* com-r *)
     (imp_res_tac compile_network_preservation_send
      >> imp_res_tac compile_network_preservation_receive
      >> rpt(first_x_assum(qspec_then `fv` assume_tac))
      >> imp_res_tac trans_com_r
      >> fs[GSYM reduction_def,compile_network_fv_def]
      >> metis_tac[RTC_SINGLE,junkcong_refl])
  >- (* com-choice-l *)
     (Cases_on `b`
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def]
          >> imp_res_tac compile_network_preservation_int_choice_T
          >> imp_res_tac compile_network_preservation_ext_choice_T
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_l
          >> qpat_x_assum `trans _ (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_l >> disch_then(qspec_then `compile_network_fv fv n1'` assume_tac)
          >> fs[GSYM reduction_def]
          >> Q.ISPEC_THEN `reduction conf` imp_res_tac RTC_SINGLE
          >> imp_res_tac RTC_RTC
          >> asm_exists_tac >> simp[]
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
          >- MATCH_ACCEPT_TAC junkcong_refl)
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def]
          >> imp_res_tac compile_network_preservation_int_choice_F
          >> imp_res_tac compile_network_preservation_ext_choice_F
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_l
          >> qpat_x_assum `trans _ (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_l >> disch_then(qspec_then `compile_network_fv fv n1'` assume_tac)
          >> fs[GSYM reduction_def]
          >> Q.ISPEC_THEN `reduction conf` imp_res_tac RTC_SINGLE
          >> imp_res_tac RTC_RTC
          >> asm_exists_tac >> simp[]
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
          >- MATCH_ACCEPT_TAC junkcong_refl))
  >- (* com-choice-l *)
     (Cases_on `d` (* TODO: why not b? *)
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def]
          >> imp_res_tac compile_network_preservation_int_choice_T
          >> imp_res_tac compile_network_preservation_ext_choice_T
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_r
          >> qpat_x_assum `trans _ (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_r >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
          >> fs[GSYM reduction_def]
          >> Q.ISPEC_THEN `reduction conf` imp_res_tac RTC_SINGLE
          >> imp_res_tac RTC_RTC
          >> asm_exists_tac >> simp[]
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- MATCH_ACCEPT_TAC junkcong_refl
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
         )
      >- (fs[endpoints_def,ALL_DISTINCT_APPEND,compile_network_fv_def]
          >> imp_res_tac compile_network_preservation_int_choice_F
          >> imp_res_tac compile_network_preservation_ext_choice_F
          >> rpt(first_x_assum(qspec_then `fv` assume_tac))
          >> fs[list_trans_def]
          >> imp_res_tac trans_com_r
          >> qpat_x_assum `trans _ (compile_network_fv _ _) LTau _` assume_tac
          >> drule trans_par_r >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
          >> fs[GSYM reduction_def]
          >> Q.ISPEC_THEN `reduction conf` imp_res_tac RTC_SINGLE
          >> imp_res_tac RTC_RTC
          >> asm_exists_tac >> simp[]
          >> match_mp_tac junkcong_par
          >> conj_tac
          >- MATCH_ACCEPT_TAC junkcong_refl
          >- (match_mp_tac junkcong_add_state_free_vars >> fs[var_names_network_def,reduction_def]
              >> metis_tac[MEM_free_vars_compile_network,trans_var_names_mono,free_names_are_names])
         )
     )
  >- (* dequeue-last-payload *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac RTC_SINGLE >> imp_res_tac trans_dequeue_last_payload
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* dequeue-intermediate-payload *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac RTC_SINGLE >> imp_res_tac trans_dequeue_intermediate_payload
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* extchoice-l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint a1 a2 a3) _`
      >> qexists_tac `NEndpoint a1 (a2 with bindings:= s.bindings |+ (fv,[1w])) a3` >> unabbrev_all_tac
      >> conj_tac
      >- (Q.ISPEC_THEN `reduction conf` (match_mp_tac o CONJUNCT2) RTC_RULES
          >> imp_res_tac trans_dequeue_last_payload
          >> pop_assum(qspec_then `fv` (assume_tac o CONV_RULE SWAP_FORALL_CONV))
          >> pop_assum(qspec_then `[]` assume_tac)
          >> qmatch_goalsub_abbrev_tac `Receive _ _ [] a1`
          >> qmatch_goalsub_abbrev_tac `NEndpoint _ a2 (compile_endpoint _ _)`
          >> qexists_tac `NEndpoint p2 a2 a1` >> unabbrev_all_tac
          >> conj_tac >- fs[reduction_def]
          >> match_mp_tac RTC_SINGLE
          >> fs[reduction_def] >> match_mp_tac trans_if_true
          >> fs[FLOOKUP_UPDATE])
      >- (match_mp_tac junkcong_add_junk''
          >> fs[free_var_names_endpoint_def,var_names_network_def,var_names_endpoint_def]
          >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))
  >- (* extchoice-r *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint a1 a2 a3) _`
      >> qexists_tac `NEndpoint a1 (a2 with bindings:= s.bindings |+ (fv,[0w])) a3` >> unabbrev_all_tac
      >> conj_tac
      >- (Q.ISPEC_THEN `reduction conf` (match_mp_tac o CONJUNCT2) RTC_RULES
          >> imp_res_tac trans_dequeue_last_payload
          >> pop_assum(qspec_then `fv` (assume_tac o CONV_RULE SWAP_FORALL_CONV))
          >> pop_assum(qspec_then `[]` assume_tac)
          >> qmatch_goalsub_abbrev_tac `Receive _ _ [] a1`
          >> qmatch_goalsub_abbrev_tac `NEndpoint _ a2 (compile_endpoint _ _)`
          >> qexists_tac `NEndpoint p2 a2 a1` >> unabbrev_all_tac
          >> conj_tac >- fs[reduction_def]
          >> match_mp_tac RTC_SINGLE
          >> fs[reduction_def] >> match_mp_tac trans_if_false
          >> fs[FLOOKUP_UPDATE])
      >- (match_mp_tac junkcong_add_junk''
          >> fs[free_var_names_endpoint_def,var_names_network_def,var_names_endpoint_def]
          >> metis_tac[MEM_free_vars_compile_endpoint,free_names_are_names_endpoint]))
  >- (* trans_if_true *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac RTC_SINGLE >> imp_res_tac trans_if_true
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_if_false *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac RTC_SINGLE >> imp_res_tac trans_if_false
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_let *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def]
      >> qmatch_goalsub_abbrev_tac `junkcong _ a1 _`
      >> qexists_tac `a1` >> unabbrev_all_tac
      >> conj_tac
      >- (match_mp_tac RTC_SINGLE >> imp_res_tac trans_let
          >> fs[reduction_def])
      >- MATCH_ACCEPT_TAC junkcong_refl)
  >- (* trans_par_l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def,var_names_network_def]
      >> first_x_assum drule
      >> (impl_tac >> fs[ALL_DISTINCT_APPEND,endpoints_def])
      >> strip_tac
      >> drule reduction_par_l >> disch_then(qspec_then `compile_network_fv fv n2'` assume_tac)
      >> asm_exists_tac >> simp[] >> match_mp_tac junkcong_par
      >> fs[junkcong_refl])
  >- (* trans_par_l *)
     (fs[compile_network_def,compile_network_fv_def,compile_endpoint_def,add_state_def,
         list_trans_def,var_names_network_def]
      >> first_x_assum drule
      >> (impl_tac >> fs[ALL_DISTINCT_APPEND,endpoints_def])
      >> strip_tac
      >> drule reduction_par_r >> disch_then(qspec_then `compile_network_fv fv n1` assume_tac)
      >> asm_exists_tac >> simp[] >> match_mp_tac junkcong_par
      >> fs[junkcong_refl])
  );

val _ = export_theory ()

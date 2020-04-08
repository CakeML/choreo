open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib
     payload_to_cakemlProofTheory;

val _ = new_theory "chorLibProg";

val _ = translation_extends "basisProg";

fun get_fun_name trm =
  lookup_v_thm trm |> concl |> rator |> rand |> rand

fun get_con_name s =
  get_cons_names() |>
  filter (fn (_,(tm,_)) => s = stringSyntax.fromHOLstring tm) |>
  map fst |> hd

val _ = ml_prog_update (open_module "ChorLib");

val _ = append_decs
  “[Dlet unknown_loc (Pvar "toList")
     (Fun "arr"
       (App Opapp
         [App Opapp
           [Var(Long "List" (Short "tabulate"));
            App Aw8length [Var(Short "arr")]];
          Fun "index"
            (App Aw8sub [Var(Short "arr"); Var(Short "index")])
         ]
       ));
    Dlet unknown_loc (Pvar "fromList")
     (Fun "l"
       (Let (SOME "arr")
          (App Aw8alloc
             [App Opapp [Var(Long "List" (Short "length")); Var(Short "l")];
              Lit(Word8 0w)])
          (Let NONE
             (App Opapp
                [App Opapp
                  [Var(Long "List" (Short "mapi"));
                   Fun "index"
                     (Fun "elem"
                       (App Aw8update [Var (Short "arr"); Var(Short "index"); Var(Short "elem")]
                       )
                     )
                  ];
                 Var(Short "l")
                ])
             (Var (Short "arr"))
          )
       )
     )
   ]”

val append_e = ``Var (Short "@")``

local
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, append_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
in
  val append_eval_thm =
    prove(mk_imp(lemma |> concl |> rand, goal),
          rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
          \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
end

val _ = ml_prog_update (add_Dlet append_eval_thm "append" [])

val _ = ml_prog_update (close_module NONE);

Definition base_conf_def:
  base_conf =
  <| length := ^(get_fun_name ``LENGTH``);
     null := ^(get_fun_name ``NULL``);
     take := ^(get_fun_name ``mllist$take``);
     drop := ^(get_fun_name ``mllist$drop``);
     toList := Long "ChorLib" (Short "toList");
     fromList := Long "ChorLib" (Short "fromList");
     concat := ^(get_fun_name ``FLAT``);
     append := Long "ChorLib" (Short "append");
     cons := Short "::";
     nil := Short "[]"
   |>
End

Theorem Eval_VarE:
  nsLookup env.v var = SOME v ∧
  Eval env (Var var) A ⇒
  A v
Proof
  rw[ml_translatorTheory.Eval_def,ml_progTheory.eval_rel_alt,terminationTheory.evaluate_def] >>
  rfs[] >>
  pop_assum(qspec_then ‘ARB’ mp_tac) >> rw[] >> first_x_assum ACCEPT_TAC
QED

val env = get_env(get_ml_prog_state());

Triviality take_drop_eqns:
  take = combin$C TAKE ∧ drop = combin$C DROP
Proof
  rw[FUN_EQ_THM,mllistTheory.take_def,mllistTheory.drop_def]
QED

Triviality evaluate_rev_v_refs:
  ∀ck v env exp s s' res env' exp' v v' v''.
  evaluate (s with clock := ck) env [exp] = (s with clock := ck,Rval [v']) ∧
  do_opapp [rev_v; v] = SOME (env,exp) ∧
  do_opapp [v'; v''] = SOME (env',exp') ∧
  evaluate (s with clock := ck) env' [exp'] = (s',res)
  ⇒
  s'.refs = s.refs
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rw[ListProgTheory.rev_v_def,semanticPrimitivesTheory.do_opapp_def] >>
  fs[Once semanticPrimitivesTheory.find_recfun_def] >> rveq >>
  rpt(qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac) >>
  rw[terminationTheory.evaluate_def] >> rw[] >>
  fs[] >> rveq >>
  last_x_assum mp_tac >>
  simp[Once terminationTheory.evaluate_def] >>
  strip_tac >>
  last_x_assum mp_tac >>
  EVAL_TAC >>
  rw[semanticPrimitivesTheory.can_pmatch_all_def] >> rw[] >>
  qpat_x_assum ‘evaluate_match _ _ _ _  _ = _’ mp_tac >>
  simp[terminationTheory.evaluate_def] >>
  rw[CaseEq "match_result",CaseEq "option",CaseEq "prod", CaseEq "result",astTheory.pat_bindings_def] >> rw[] >>
  fs[CaseEq "bool"] >> rveq >> fs[] >>
  fs[CaseEq "prod",CaseEq "option",CaseEq "result"] >> rveq >> fs[] >>
  rveq >> fs[] >>
  Cases_on ‘v’ >> fs[terminationTheory.pmatch_def] >>
  rename1 ‘Conv stmp vss’ >> Cases_on ‘stmp’ >> fs[terminationTheory.pmatch_def] >>
  fs[CaseEq "option",CaseEq "prod", CaseEq "result",CaseEq "bool"] >> rveq >> fs[] >>
  Cases_on ‘vss’ >> fs[terminationTheory.pmatch_def] >>
  fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >> fs[terminationTheory.pmatch_def] >>
  rveq >> fs[] >> rveq >> fs[] >>
  fs[semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  rveq >> fs[] >>
  qpat_x_assum ‘evaluate _ _ [Fun _ _] = _’ mp_tac >>
  rw[terminationTheory.evaluate_def] >> fs[evaluateTheory.dec_clock_def] >>
  rveq >> fs[] >>
  first_x_assum(qspec_then ‘ck - 2’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then(qspecl_then [‘s’,‘s'’,‘res’] mp_tac) >>
  pop_assum (assume_tac o GSYM) >>
  simp[] >>
  disch_then match_mp_tac >>
  rename1 ‘nsBind _ vv (nsBind _ vvv _)’ >>
  qexists_tac ‘vvv’ >> qexists_tac ‘vv’ >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
  EVAL_TAC >>
  rw[namespacePropsTheory.nsAppend_nsEmpty |> REWRITE_RULE [namespaceTheory.nsEmpty_def]]
QED

Theorem reverse_no_change_refs:
  ∀ck v env exp s s' res.
  do_opapp [reverse_v; v] = SOME (env,exp) ∧
  evaluate (s with clock := ck) env [exp] = (s',res) ⇒
  s'.refs = s.refs
Proof
  rw[ListProgTheory.reverse_v_def,semanticPrimitivesTheory.do_opapp_def] >> pop_assum mp_tac >>
  rw[terminationTheory.evaluate_def] >> rw[] >>
  fs[CaseEq "prod",CaseEq "option",CaseEq "result",CaseEq "bool"] >> rveq >> fs[] >> rveq >> fs[] >>
  qpat_x_assum ‘nsLookup _ _ = _’ mp_tac >> EVAL_TAC >> strip_tac >> rveq >> fs[] >>
  fs[ListProgTheory.rev_v_def,semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  rveq >> fs[] >>
  fs[terminationTheory.evaluate_def] >> rveq >> fs[] >> rveq >> fs[evaluateTheory.dec_clock_def] >>
  match_mp_tac evaluate_rev_v_refs >>
  fs[ListProgTheory.rev_v_def,semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[Once terminationTheory.evaluate_def] >>
  goal_assum drule
QED

Triviality length_aux_no_change_refs:
  ∀ck v env exp s s' res env' exp' v v' v''.
  evaluate (s with clock := ck) env [exp] = (s with clock := ck,Rval [v']) ∧
  do_opapp [length_aux_v; v] = SOME (env,exp) ∧
  do_opapp [v'; v''] = SOME (env',exp') ∧
  evaluate (s with clock := ck) env' [exp'] = (s',res)
  ⇒
  s'.refs = s.refs
Proof
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rw[ListProgTheory.length_aux_v_def,semanticPrimitivesTheory.do_opapp_def] >>
  fs[Once semanticPrimitivesTheory.find_recfun_def] >> rveq >>
  rpt(qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac) >>
  rw[terminationTheory.evaluate_def] >> rw[] >>
  fs[] >> rveq >>
  last_x_assum mp_tac >>
  simp[Once terminationTheory.evaluate_def] >>
  strip_tac >>
  last_x_assum mp_tac >>
  EVAL_TAC >>
  rw[semanticPrimitivesTheory.can_pmatch_all_def] >> rw[] >>
  qpat_x_assum ‘evaluate_match _ _ _ _  _ = _’ mp_tac >>
  simp[terminationTheory.evaluate_def] >>
  rw[CaseEq "match_result",CaseEq "option",CaseEq "prod", CaseEq "result",astTheory.pat_bindings_def,semanticPrimitivesTheory.do_app_def] >> rw[] >>
  fs[CaseEq "bool"] >> rveq >> fs[] >>
  fs[CaseEq "prod",CaseEq "option",CaseEq "result"] >> rveq >> fs[] >>
  rveq >> fs[] >>
  Cases_on ‘v’ >> fs[terminationTheory.pmatch_def] >>
  rename1 ‘Conv stmp vss’ >> Cases_on ‘stmp’ >> fs[terminationTheory.pmatch_def] >>
  fs[CaseEq "option",CaseEq "prod", CaseEq "result",CaseEq "bool"] >> rveq >> fs[] >>
  Cases_on ‘vss’ >> fs[terminationTheory.pmatch_def] >>
  fs[quantHeuristicsTheory.LIST_LENGTH_1] >> rveq >> fs[terminationTheory.pmatch_def] >>
  rveq >> fs[] >> rveq >> fs[] >>
  fs[semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  rveq >> fs[] >> fs[CaseEq "v",CaseEq"lit"] >> rveq >> fs[] >>
  qpat_x_assum ‘evaluate _ _ [Fun _ _] = _’ mp_tac >>
  rw[terminationTheory.evaluate_def] >> fs[evaluateTheory.dec_clock_def] >>
  rveq >> fs[] >>
  first_x_assum(qspec_then ‘ck - 2’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then(qspecl_then [‘s’,‘s'’,‘res’] mp_tac) >>
  pop_assum (assume_tac o GSYM) >>
  simp[] >>
  disch_then match_mp_tac >>
  rename1 ‘nsBind _ vv (nsBind _ vvv _)’ >>
  qexists_tac ‘vvv’ >> qexists_tac ‘vv’ >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
  EVAL_TAC >>
  rw[namespacePropsTheory.nsAppend_nsEmpty |> REWRITE_RULE [namespaceTheory.nsEmpty_def]]
QED

Theorem length_no_change_refs:
  ∀ck v env exp s s' res.
  do_opapp [length_v; v] = SOME (env,exp) ∧
  evaluate (s with clock := ck) env [exp] = (s',res) ⇒
  s'.refs = s.refs
Proof
  rw[ListProgTheory.length_v_def,semanticPrimitivesTheory.do_opapp_def] >> pop_assum mp_tac >>
  rw[terminationTheory.evaluate_def] >> rw[] >>
  fs[CaseEq "prod",CaseEq "option",CaseEq "result",CaseEq "bool"] >> rveq >> fs[] >> rveq >> fs[] >>
  qpat_x_assum ‘nsLookup _ _ = _’ mp_tac >> EVAL_TAC >> strip_tac >> rveq >> fs[] >>
  fs[ListProgTheory.length_aux_v_def,semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  rveq >> fs[] >>
  fs[terminationTheory.evaluate_def] >> rveq >> fs[] >> rveq >> fs[evaluateTheory.dec_clock_def] >>
  match_mp_tac length_aux_no_change_refs >>
  fs[ListProgTheory.length_aux_v_def,semanticPrimitivesTheory.do_opapp_def, Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[Once terminationTheory.evaluate_def] >>
  goal_assum drule
QED

Theorem env_asm_base_conf:
  env_asm ^env base_conf
Proof
  rw[env_asm_def,GSYM take_drop_eqns] >>
  TRY(rename1 ‘has_v _ base_conf.append’ >>
      simp[has_v_def,base_conf_def] >>
      CONV_TAC(STRIP_QUANT_CONV(RATOR_CONV(RAND_CONV(LHS_CONV EVAL)))) >>
      simp[mlbasicsProgTheory.append_v_thm] >>
      NO_TAC) >>
  TRY(rename1 ‘has_v _.v _ _’ >>
      (fn (h,g) =>
         mp_tac(lookup_v_thm (rand g) |>
                INST_TYPE [alpha |-> “:word8”] |>
                Q.INST [‘env’|->[ANTIQUOTE env],
                        ‘a’|->‘WORD8’] |>
                DISCH_ALL)
                (h,g)) >>
      simp[has_v_def,base_conf_def] >>
      impl_keep_tac >- EVAL_TAC >>
      strip_tac >> goal_assum drule >>
      imp_res_tac Eval_VarE >>
      NO_TAC) >>
  TRY(rename1 ‘has_v _.c _ _’ >>
      rw[base_conf_def,in_module_def,has_v_def] >>
      EVAL_TAC >> NO_TAC) >>
  TRY(rename1 ‘in_module  _’ >>
      rw[base_conf_def,in_module_def] >> NO_TAC) >>
  TRY(rename1 ‘base_conf.toList’ >>
      CONV_TAC(STRIP_QUANT_CONV(RATOR_CONV(RAND_CONV(LHS_CONV EVAL)))) >>
      rw[fetch "-" "ChorLib_toList_v_def",semanticPrimitivesTheory.do_opapp_def] >>
      ntac 8 (simp[Once terminationTheory.evaluate_def,semanticPrimitivesTheory.do_app_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[ListProgTheory.tabulate_1_v_def,semanticPrimitivesTheory.do_opapp_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      simp[REV_DEF] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = do_con_check _ _ _’ >>
      ‘a1’ by(unabbrev_all_tac >> EVAL_TAC) >>
      simp[] >>
      pop_assum kall_tac >>
      unabbrev_all_tac >>
      PURE_TOP_CASE_TAC >> pop_assum mp_tac >>
      CONV_TAC(RATOR_CONV(RAND_CONV EVAL)) >> simp[] >>
      disch_then(SUBST_ALL_TAC o GSYM) >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[ListProgTheory.tabulate_aux_v_def,semanticPrimitivesTheory.do_opapp_def] >>
      simp[Once semanticPrimitivesTheory.find_recfun_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      qpat_abbrev_tac ‘accv = Conv (SOME (TypeStamp "[]" _)) _’ >>
      ‘∃acc. LIST_TYPE WORD8 acc accv ∧ LENGTH acc ≤ LENGTH l ∧ Litv(IntLit 0) = Litv(IntLit(&LENGTH acc))’
        by(qexists_tac ‘[]’ >> rw[Abbr ‘accv’,ml_translatorTheory.LIST_TYPE_def]) >>
      pop_assum SUBST_ALL_TAC >>
      ‘l = REVERSE acc ++ DROP (LENGTH acc) l’
        by(Cases_on ‘acc’ >> fs[Abbr ‘accv’,ml_translatorTheory.LIST_TYPE_def]) >>
      pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
      qpat_x_assum ‘Abbrev _’ kall_tac >>
      rpt(pop_assum mp_tac) >>
      MAP_EVERY qid_spec_tac [‘ll’,‘s1’,‘accv’] >>
      Induct_on ‘LENGTH l - LENGTH acc’ >-
        (rw[] >> drule_all_then strip_assume_tac LESS_EQUAL_ANTISYM >>
         ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
         simp[semanticPrimitivesTheory.do_app_def] >>
         ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[semanticPrimitivesTheory.do_if_def,integerTheory.int_ge,semanticPrimitivesTheory.Boolv_def,semanticPrimitivesTheory.opb_lookup_def] >>
         ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[Once terminationTheory.evaluate_def] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[DROP_LENGTH_TOO_LONG] >>
         Q.ISPEC_THEN ‘WORD8’ assume_tac (GEN_ALL ListProgTheory.reverse_v_thm) >>
         fs[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def] >>
         first_x_assum drule >>
         disch_then(qspec_then ‘s1.refs’ mp_tac) >>
         strip_tac >>
         dxrule ml_translatorTheory.evaluate_empty_state_IMP >>
         strip_tac >>
         simp[] >>
         Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
         simp[evaluateTheory.dec_clock_def] >>
         fs[ml_progTheory.eval_rel_def] >>
         qexists_tac ‘ck1’ >>
         simp[] >>
         simp[semanticPrimitivesTheory.state_component_equality] >>
         drule_then drule reverse_no_change_refs >> fs[]) >>
      rw[] >>
      qpat_x_assum ‘SUC _ = _’ (assume_tac o GSYM) >> fs[] >>
      ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
      simp[semanticPrimitivesTheory.do_app_def] >>
      ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_if_def,integerTheory.int_ge,semanticPrimitivesTheory.Boolv_def,semanticPrimitivesTheory.opb_lookup_def] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[Once terminationTheory.evaluate_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_opapp_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      simp[semanticPrimitivesTheory.do_app_def] >>
      ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_app_def] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      simp[semanticPrimitivesTheory.do_con_check_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[Once terminationTheory.evaluate_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.build_conv_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 2 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 4 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_opapp_def,Once semanticPrimitivesTheory.find_recfun_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      ‘LENGTH l - LENGTH(EL (LENGTH acc) l::acc) = v’ by simp[] >>
      pop_assum(assume_tac o GSYM) >>
      first_x_assum drule >>
      disch_then drule >>
      disch_then(qspec_then ‘(Conv (SOME (TypeStamp "::" 1)) [Litv (Word8 (EL (LENGTH acc) l)); accv])’ mp_tac) >>
      impl_keep_tac >- (fs[ml_translatorTheory.LIST_TYPE_def]) >>
      strip_tac >>
      fs[] >>
      fs[integerTheory.INT] >>
      qexists_tac ‘ck1’ >> qexists_tac ‘ck2’ >>
      qexists_tac ‘lv’ >>
      simp[Once DROP_EL_CONS] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,ADD1] >>
      qpat_x_assum ‘_ = _ ’ (assume_tac o GSYM) >> simp[] >>
      rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
      EVAL_TAC >>
      rw[namespacePropsTheory.nsAppend_nsEmpty |> REWRITE_RULE [namespaceTheory.nsEmpty_def]] >>
      NO_TAC) >>
  TRY(rename1 ‘base_conf.fromList’ >>
      CONV_TAC(STRIP_QUANT_CONV(RATOR_CONV(RAND_CONV(LHS_CONV EVAL)))) >>
      rw[fetch "-" "ChorLib_fromList_v_def",semanticPrimitivesTheory.do_opapp_def] >>
      ntac 8 (simp[Once terminationTheory.evaluate_def,semanticPrimitivesTheory.do_app_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      Q.ISPEC_THEN ‘WORD8’ assume_tac (GEN_ALL(ListProgTheory.length_v_thm)) >>
      fs[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def] >>
      first_x_assum drule >> disch_then(qspec_then ‘s1.refs’ strip_assume_tac) >>
      dxrule ml_translatorTheory.evaluate_empty_state_IMP >> strip_tac >>
      fs[ml_progTheory.eval_rel_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck11’ >>
      simp[evaluateTheory.dec_clock_def] >>
      dxrule evaluatePropsTheory.evaluate_set_clock >> impl_tac >- simp[] >>
      disch_then(qspec_then ‘0’ mp_tac) >> simp[] >> strip_tac >>
      rename1 ‘evaluate (_ with clock := ck1)’ >>
      drule evaluatePropsTheory.evaluate_add_to_clock >>
      impl_tac >- simp[] >>
      simp[] >> strip_tac >>
      Q.REFINE_EXISTS_TAC ‘ck1 + ck11’ >>
      simp[] >>
      fs[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
      ‘refs' = []’
        by(drule_then drule length_no_change_refs >> fs[]) >>
      rveq >> fs[] >>
      simp[semanticPrimitivesTheory.store_alloc_def] >>
      ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[ListProgTheory.mapi_1_v_def,semanticPrimitivesTheory.do_opapp_def] >>
      ntac 2 (pop_assum kall_tac) >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      ntac 10 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_opapp_def,ListProgTheory.mapi_v_def,
           Once semanticPrimitivesTheory.find_recfun_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      pop_assum kall_tac >>
      ‘∃index. index = 0:num’ by simp[] >>
      ‘Litv (IntLit 0) = Litv (IntLit(&index))’ by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      ‘REPLICATE (LENGTH l) 0w = TAKE index l ++ REPLICATE (LENGTH l - index) 0w’
        by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      ‘∃tlv. LIST_TYPE WORD8 (DROP index l) tlv ∧ lv = tlv’ by simp[] >>
      pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [Once thm]) >>
      ‘index ≤ LENGTH l’ by simp[] >>
      qpat_x_assum ‘_ = _’ kall_tac >>
      rpt(pop_assum mp_tac) >>
      MAP_EVERY qid_spec_tac [‘lv’,‘s1’,‘tlv’] >>
      Induct_on ‘LENGTH l - index’ >-
        (rw[] >> drule_all_then strip_assume_tac LESS_EQUAL_ANTISYM >>
         rveq >>
         fs[DROP_LENGTH_TOO_LONG] >>
         ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
         fs[ml_translatorTheory.LIST_TYPE_def] >> rveq >>
         simp[semanticPrimitivesTheory.can_pmatch_all_def,
              terminationTheory.pmatch_def] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def,
              astTheory.pat_bindings_def] >>
         simp[Once terminationTheory.evaluate_def] >>
         simp[semanticPrimitivesTheory.do_con_check_def] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[semanticPrimitivesTheory.build_conv_def] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[terminationTheory.evaluate_def] >>
         qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
         pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
         disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
         rveq >>
         simp[] >>
         simp[semanticPrimitivesTheory.state_component_equality]) >>
      rw[] >>
      qpat_x_assum ‘SUC _ = _’ (assume_tac o GSYM) >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      fs[DROP_EL_CONS] >>
      fs[ml_translatorTheory.LIST_TYPE_def] >> rveq >>
      simp[semanticPrimitivesTheory.can_pmatch_all_def,
           terminationTheory.pmatch_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.same_type_def,semanticPrimitivesTheory.same_ctor_def,
           astTheory.pat_bindings_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[Once terminationTheory.evaluate_def,astTheory.pat_bindings_def,
          terminationTheory.pmatch_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 8 (simp[Once terminationTheory.evaluate_def]) >>
      simp[semanticPrimitivesTheory.do_opapp_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      ntac 6 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      fs[ml_translatorTheory.WORD_def] >>
      simp[semanticPrimitivesTheory.do_app_def] >>
      simp[semanticPrimitivesTheory.store_lookup_def,EL_APPEND_EQN] >>
      simp[semanticPrimitivesTheory.store_assign_def,EL_APPEND_EQN,
           semanticPrimitivesTheory.store_v_same_type_def] >>
      simp[LUPDATE_APPEND] >>
      simp[LUPDATE_def] >>
      ntac 5 (simp[Once terminationTheory.evaluate_def]) >>
      simp[semanticPrimitivesTheory.do_con_check_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      ntac 6 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_app_def] >>
      ntac 3 (simp[Once terminationTheory.evaluate_def]) >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[Once terminationTheory.evaluate_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      simp[semanticPrimitivesTheory.do_opapp_def] >>
      simp[Once semanticPrimitivesTheory.find_recfun_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[Once terminationTheory.evaluate_def] >>
      Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
      simp[evaluateTheory.dec_clock_def] >>
      simp[semanticPrimitivesTheory.opn_lookup_def] >>
      first_x_assum(qspecl_then [‘l’,‘index + 1’] mp_tac) >>
      impl_tac >- fs[] >>
      disch_then drule >> disch_then drule >>
      impl_tac >- fs[] >>
      disch_then(qspec_then ‘s1’ strip_assume_tac) >>
      qexists_tac ‘ck1’ >> qexists_tac ‘ck2'’ >>
      pop_assum mp_tac >>
      simp[SimpL “$==>”,CaseEq"prod",CaseEq"option",CaseEq "result",PULL_EXISTS] >>
      rpt strip_tac >>
      pop_assum mp_tac >>
      simp[SimpL “$==>”,Once terminationTheory.evaluate_def] >>
      qpat_abbrev_tac ‘a1 = nsLookup _ _’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
      disch_then(assume_tac o CONV_RULE(RHS_CONV EVAL)) >>
      rveq >>
      simp[] >>
      strip_tac >> rveq >>
      simp[CaseEq"prod",CaseEq"option",CaseEq "result",PULL_EXISTS] >>
      simp[SimpR “$/\”,Once terminationTheory.evaluate_def] >>
      simp[SimpR “$/\”,namespaceTheory.nsOptBind_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate as1 ae1’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate as2 ae2’ >>
      ‘ae1 = ae2 ∧ as1 = as2’
        by(unabbrev_all_tac >> EVAL_TAC >>
           simp[] >>
           simp[integerTheory.INT |> REWRITE_RULE[ADD1]] >>
           simp[semanticPrimitivesTheory.state_component_equality] >>
           simp[TAKE_EL_SNOC] >>
           rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
           rw[]) >>
      fs[] >>
      unabbrev_all_tac >>
      EVAL_TAC >> simp[] >> NO_TAC)
QED

val _ = export_theory ();

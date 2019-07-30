open HolKernel boolLib Parse bossLib;
open evaluateTheory
     terminationTheory
     evaluatePropsTheory
     ml_progTheory
     ml_translatorTheory;

val _ = new_theory "evaluate_tools";

Theorem evaluate_generalise:
  ∀ (cSt: 'ffi semanticPrimitives$state) env exp ck1 ck2 refs' u. 
      evaluate (empty_state with <|clock := ck1; refs := cSt.refs|>) env
           [exp] =
         (empty_state with <|clock := ck2; refs := cSt.refs ++ refs'|>,
          Rval [u])
    ⇒ ∀mc. evaluate (cSt with clock := ck1 + mc) env [exp]
                = (cSt with <|clock := ck2 + mc;
                               refs := cSt.refs ++ refs'|>,
                   Rval [u])
Proof
  rpt strip_tac >>
  ‘evaluate (cSt with clock := ck1) env [exp]
                  = (cSt with <|clock := ck2;
                                 refs := cSt.refs ++ refs'|>,
                     Rval[u])’
    suffices_by (qspecl_then [‘cSt with clock := ck1’,
                              ‘env’, ‘[exp]’,
                              ‘cSt with <|clock := ck2;
                                 refs := cSt.refs ++ refs'|>’,
                              ‘Rval [u]’, ‘mc’]
                              assume_tac evaluate_add_to_clock >>
                 fs[]) >>
  qabbrev_tac ‘s  = empty_state with <|clock := ck1;
                                      refs   := cSt.refs|>’ >>
  qabbrev_tac ‘s' = empty_state with <|clock := ck2;
                                      refs   := cSt.refs ++ refs'|>’ >>
  qabbrev_tac ‘e = [exp]’ >>
  qabbrev_tac ‘r = Rval [u] :(v list, v) result’ >>
  ‘(evaluate s env e = (s',r)) ∧ (s'.ffi = s.ffi) ∧
    (∀outcome. r ≠ Rerr (Rabort (Rffi_error outcome))) ⇒
    ∀t : 'ffi semanticPrimitives$state.
        (t.clock = s.clock) ∧ (t.refs = s.refs) ⇒
        (evaluate t env e =
        (t with <|clock := s'.clock; refs := s'.refs|>,r))’
    by metis_tac[evaluate_ffi_intro] >>
  rfs[Abbr ‘s'’, Abbr ‘s’, Abbr ‘r’]
QED

Theorem do_opapp_translate:
  ∀ cfv hf ha cav ta tb (cSt: 'ffi semanticPrimitives$state).
    (ta --> tb) hf cfv                     ∧
    ta ha cav
    ⇒ ∃cfa_env cfa_exp.
        do_opapp [cfv; cav] = SOME (cfa_env,cfa_exp) ∧
        ∃ bc1 bc2 drefs crv.
          tb (hf ha) crv ∧
          ∀x dc.
            x = bc1 + dc
            ⇒ evaluate (cSt with clock := x) cfa_env [cfa_exp]
              = (cSt with <|clock := bc2 + dc;
                          refs := cSt.refs ++ drefs|>,
                  Rval [crv])
Proof
  rpt strip_tac >>
  fs[Arrow_def,AppReturns_def] >>
  last_x_assum (qspecl_then [‘ha’, ‘cav’] assume_tac) >>
  rfs[] >>
  ‘∃ cfa_env cfa_exp.
    do_opapp [cfv; cav] = SOME (cfa_env,cfa_exp)’
    by metis_tac[] >>
  MAP_EVERY qexists_tac [‘cfa_env’, ‘cfa_exp’] >>
  simp[] >>
  rpt strip_tac >>
  first_x_assum (qspec_then ‘cSt.refs’ assume_tac) >>
  rfs[eval_rel_def] >>
  rename [‘evaluate (empty_state with <|clock := bc1; refs := cSt.refs|>)
          cfa_env [cfa_exp] =
            (empty_state with <|clock := bc2; refs := cSt.refs ++ drefs|>,
              Rval [crv])’] >>
  MAP_EVERY qexists_tac [‘bc1’,‘bc2’,‘drefs’,‘crv’] >>
  metis_tac[evaluate_generalise]
QED

Theorem evaluate_translate:
  ∀ cfid hf caid ha tA tB (cSt: 'ffi semanticPrimitives$state) cEnv.
    (∃cfv. nsLookup cEnv.v cfid = SOME cfv ∧
          (tA --> tB) hf cfv)                 ∧
    (∃cav. nsLookup cEnv.v caid = SOME cav ∧
          tA ha cav)                          ⇒
    ∃bc1 bc2 drefs crv.
      tB (hf ha) crv ∧
      ∀dc.
        evaluate (cSt with clock := bc1 + dc) cEnv
          [App Opapp [Var cfid; Var caid]]
        = (cSt with <|clock := dc + bc2;
                          refs := cSt.refs ++ drefs|>,
                  Rval [crv])
Proof
  rpt strip_tac >>
  rw[evaluate_def] >>
  drule_then (Q.ISPECL_THEN [‘ha’, ‘cav’, ‘cSt’] strip_assume_tac) do_opapp_translate >>
  rfs[] >>
  rename [‘∀dc.
            evaluate (cSt with clock := bc1 + dc) cfa_env [cfa_exp] =
            (cSt with <|clock := bc2 + dc; refs := cSt.refs ++ drefs|>,
             Rval [crv])’] >>
  MAP_EVERY qexists_tac [‘SUC bc1’,‘bc2’,‘drefs’,‘crv’] >>
  rw[dec_clock_def,arithmeticTheory.ADD1]
QED

Theorem evaluate_translate_lit:
  ∀ cfid hf cal ha tA tB (cSt: 'ffi semanticPrimitives$state) cEnv.
    (∃cfv. nsLookup cEnv.v cfid = SOME cfv ∧
          (tA --> tB) hf cfv)                 ∧
    tA ha (Litv cal)                           ⇒
    ∃bc1 bc2 drefs crv.
      tB (hf ha) crv ∧
      ∀dc.
        evaluate (cSt with clock := bc1 + dc) cEnv
          [App Opapp [Var cfid; Lit cal]]
        = (cSt with <|clock := dc + bc2;
                          refs := cSt.refs ++ drefs|>,
                  Rval [crv])
Proof
  rpt strip_tac >>
  rw[evaluate_def] >>
  drule_then (Q.ISPECL_THEN [‘ha’, ‘Litv cal’, ‘cSt’] strip_assume_tac) do_opapp_translate >>
  rfs[] >>
  rename [‘∀dc.
            evaluate (cSt with clock := bc1 + dc) cfa_env [cfa_exp] =
            (cSt with <|clock := bc2 + dc; refs := cSt.refs ++ drefs|>,
             Rval [crv])’] >>
  MAP_EVERY qexists_tac [‘SUC bc1’,‘bc2’,‘drefs’,‘crv’] >>
  rw[dec_clock_def,arithmeticTheory.ADD1]
QED

Theorem evaluate_ltwo_translate:
  ∀ cfid hf caid1 caid2 ha hb tA tB tC (cSt: 'ffi semanticPrimitives$state) cEnv.
    (∃cfv. nsLookup cEnv.v cfid = SOME cfv ∧
          (tA --> tB --> tC) hf cfv)            ∧
    (∃cav1. nsLookup cEnv.v caid1 = SOME cav1 ∧
          tA ha cav1)                           ∧                          
    (∃cav2. nsLookup cEnv.v caid2 = SOME cav2 ∧
          tB hb cav2)                          ⇒
    ∃bc1 bc2 drefs crv.
      tC (hf ha hb) crv ∧
      ∀dc.
        evaluate (cSt with clock := bc1 + dc) cEnv
          [App Opapp [App Opapp[Var cfid; Var caid1]; Var caid2]]
        = (cSt with <|clock := dc + bc2;
                          refs := cSt.refs ++ drefs|>,
                  Rval [crv])
Proof
  rpt strip_tac >>
  rw[evaluate_def] >>
  drule_then (Q.ISPECL_THEN [‘ha’, ‘cav1’, ‘cSt’] strip_assume_tac) do_opapp_translate >>
  rfs[] >>
  rename [‘∀dc.
          evaluate (cSt with clock := bc1 + dc) cfa_env1 [cfa_exp1] =
          (cSt with <|clock := bc2 + dc; refs := cSt.refs ++ drefs1|>,
           Rval [crv1])’] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + SUC bc1'’ >>
  rw[arithmeticTheory.ADD1,dec_clock_def] >>
  ASM_SIMP_TAC bossLib.bool_ss [] >>
  qpat_x_assum ‘∀dc. _’ (K ALL_TAC) >>
  ntac 5 (last_x_assum (K ALL_TAC)) >>
  first_x_assum (K ALL_TAC) >>
  drule_then (Q.ISPECL_THEN [‘hb’, ‘cav2’, ‘cSt with refs := cSt.refs ++ drefs1’]
                            strip_assume_tac) do_opapp_translate >>
  rfs[] >>
  rename1 ‘∀dc.
          evaluate (cSt with <|clock := Abc1 + dc; refs := cSt.refs ++ drefs1|>) cfa_env2 [cfa_exp2] =
          (cSt with <|clock := Abc2 + dc; refs := cSt.refs ++ drefs1 ++ drefs2|>,
           Rval [crv2])’ >>
  Q.REFINE_EXISTS_TAC ‘Abc1 + SUC bc1'’ >>
  rw[arithmeticTheory.ADD1,dec_clock_def] >>
  MAP_EVERY qexists_tac [‘0’,‘Abc2 + bc2’,‘drefs1 ++ drefs2’,‘crv2’] >>
  rw[]
QED


val _ = export_theory ();
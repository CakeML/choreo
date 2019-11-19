open HolKernel boolLib Parse bossLib;
open evaluateTheory
     terminationTheory
     evaluatePropsTheory
     ml_progTheory
     ml_translatorTheory;

val _ = new_theory "evaluate_tools";

(* Projecting evaluation in empty_state (with arbitrary dynamic memory state) to evaluation in
   any state (with the same dynamic memory state) *)
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

(* Applying translated function in arbitrary state to produce correct result *)
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


val _ = export_theory ();
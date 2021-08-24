open HolKernel boolLib Parse bossLib;
open evaluateTheory
     terminationTheory
     evaluatePropsTheory
     ml_progTheory
     ml_translatorTheory;

val _ = new_theory "evaluate_tools";

(* Version of evaluate_ffi_etc_intro without existentials *)
Theorem evaluate_ffi_etc_intro_aux:
  evaluate s0 env xs = (s1, res) /\
  (!outcome. res <> Rerr (Rabort (Rffi_error outcome))) /\
  s1.ffi = s0.ffi /\
  s1.next_type_stamp = s0.next_type_stamp /\
  s1.next_exn_stamp = s0.next_exn_stamp /\
  s0.eval_state = NONE /\
  res <> Rerr (Rabort Rtype_error) /\
  s.refs = s0.refs
  ==>
  evaluate (s with clock := s0.clock) env xs =
    (s with <| refs := s1.refs; clock := s1.clock |>, res)
Proof
  rw []
  \\ dxrule_then (qspec_then `s.ffi` mp_tac) (CONJUNCT1 evaluate_ffi_intro)
  \\ rw []
  \\ dxrule (CONJUNCT1 evaluate_set_next_stamps)
  \\ simp []
  \\ disch_then (qspec_then `s.next_type_stamp` mp_tac o CONJUNCT1)
  \\ rw []
  \\ dxrule (CONJUNCT1 evaluate_set_next_stamps)
  \\ simp []
  \\ disch_then (qspec_then `s.next_exn_stamp` mp_tac o CONJUNCT2)
  \\ rw []
  \\ dxrule (CONJUNCT1 eval_no_eval_simulation)
  \\ simp []
  \\ disch_then (qspec_then `s.eval_state` mp_tac)
  \\ rw []
  \\ dxrule_then irule (Q.prove (`(evaluate a x y = b) /\ a = c /\ b = d
    ==> evaluate c x y = d`, rw []))
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED


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
  drule_then (qspec_then ‘cSt’ mp_tac) (GEN_ALL evaluate_ffi_etc_intro_aux) >>
  impl_tac >- (UNABBREV_ALL_TAC >> simp[empty_state_def]) >>
  rfs[Abbr ‘s'’, Abbr ‘s’, Abbr ‘r’]
QED

(* Applying translated function in arbitrary state to produce correct result *)
Theorem do_opapp_translate_general:
  ∀ cfv hf (ha : α) cav (ta : α -> v -> bool) (tb : β -> v -> bool).
    (ta --> tb) hf cfv ∧
    ta ha cav
    ⇒ ∃cfa_env cfa_exp.
        do_opapp [cfv; cav] = SOME (cfa_env,cfa_exp) ∧
        ∀(cSt: γ semanticPrimitives$state).
        ∃bc1 bc2 drefs crv.
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

Theorem do_opapp_translate_general_prop:
  ∀ cfv hf (ha : α) cav (ta : α -> v -> bool) (tb : β -> v -> bool)
    (cSt: γ semanticPrimitives$state).
    (ta --> tb) hf cfv                     ∧
    ta ha cav
    ⇒ ∃cfa_env cfa_exp.
        do_opapp [cfv; cav] = SOME (cfa_env,cfa_exp) ∧
        ∃bc1 bc2 drefs crv.
          tb (hf ha) crv ∧
          ∀x dc.
            x = bc1 + dc
            ⇒ evaluate (cSt with clock := x) cfa_env [cfa_exp]
              = (cSt with <|clock := bc2 + dc;
                          refs := cSt.refs ++ drefs|>,
                  Rval [crv])
Proof
  rw[] >>
  drule_all_then strip_assume_tac do_opapp_translate_general >>
  rw[] >> metis_tac[]
QED

Theorem do_opapp_translate = INST_TYPE [beta |-> Type ‘:'ffi’] do_opapp_translate_general_prop

val _ = export_theory ();

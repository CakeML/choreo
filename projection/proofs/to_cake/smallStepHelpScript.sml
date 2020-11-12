open HolKernel Parse boolLib bossLib;

open relationTheory pairTheory bigSmallEquivTheory smallStepTheory

val _ = new_theory "smallStepHelp";

Overload stepr = “e_step_reln”
Overload ";;" = “Let NONE”
val _ = temp_set_fixity ";;" (Infixl 500)

Theorem nsOptBind_NONE[simp]:
  nsOptBind NONE x env = env
Proof
  simp[namespaceTheory.nsOptBind_def]
QED

Theorem small_eval_prefix:
  ∀s env  e c cenv' s' env' e' c' r.
    stepr^* (env,s,Exp e,c) (env',s',Exp e',c') ∧
    small_eval env' s' e' c' r
    ⇒
    small_eval env s e c r
Proof
  rpt gen_tac >> PairCases_on ‘r’ >>
  rename [‘_ ∧ small_eval env1 s1 e1 cs1 ((rfs2,s2), res2) ⇒ _’] >>
  Cases_on ‘res2’
  >- (simp[small_eval_def] >> metis_tac[RTC_CASES_RTC_TWICE]) >>
  rename [‘Rerr err’] >> Cases_on ‘err’ >> simp[small_eval_def] >>
  metis_tac[RTC_CASES_RTC_TWICE]
QED

Theorem LetNONE_subexpr2[simp]:
  e1 ;; e2 ≠ e2
Proof
  map_every qid_spec_tac [‘e1’, ‘e2’] >> Induct_on ‘e2’ >> simp[]
QED

Theorem estep_eq_empty_cs:
  e_step (env0,st0,ev0,cs) = Estep (env,st,ev,[]) ∧
  cs ≠ [] ∧ LAST cs = (Clet NONE () e2, env') ⇒
  ∃v0. ev0 = Val v0 ∧ ev = Exp e2 ∧ env = env' ∧ st = st0 ∧
       cs = [(Clet NONE () e2, env')]

Proof
  Cases_on ‘ev0’ >> simp[e_step_def, push_def, AllCaseEqs(), return_def]
  >- (Cases_on ‘cs’ >> simp[application_def, AllCaseEqs(), return_def]) >>
  Cases_on ‘cs’ >>
  gvs[continue_def, AllCaseEqs(), return_def, push_def] >>
  gvs[application_def, AllCaseEqs(), return_def] >> rw[] >> gs[]
QED

Theorem application_augment_conts:
  application opn env0 st0 vs cs0 = Estep (env,st,ev,cs) ⇒
  application opn env0 st0 vs (cs0 ++ csb) = Estep (env,st,ev,cs ++ csb)
Proof
  simp[application_def, AllCaseEqs(), PULL_EXISTS, return_def, push_def]
QED

Theorem stepr_augment_conts:
  stepr (env0, st0, ev0, cs0) (env, st, ev, cs) ⇒
  stepr (env0, st0, ev0, cs0 ++ csb) (env, st, ev, cs ++ csb)
Proof
  simp[e_step_reln_def] >> Cases_on ‘ev0’ >>
  simp[e_step_def, AllCaseEqs(), PULL_EXISTS, push_def, return_def] >>
  rw[] >> gs[application_augment_conts] >>
  Cases_on ‘cs0’ >>
  gvs[continue_def, AllCaseEqs(), return_def, push_def,
      application_augment_conts]
QED

Theorem smallstep_augment_conts:
  ∀env0 st0 ev0 cs0 env st ev cs.
    stepr꙳ (env0, st0, ev0, cs0) (env, st, ev, cs) ⇒
    stepr꙳ (env0, st0, ev0, cs0 ++ csb) (env, st, ev, cs ++ csb)
Proof
  Induct_on ‘RTC’ >> simp[FORALL_PROD] >> rw[] >>
  rename [‘stepr (env0,(r0,ffi0),ev0,cs0) (env1,(r1,ffi1),ev1,cs1)’] >>
  irule (cj 2 RTC_RULES) >> first_assum (irule_at Any) >>
  simp[stepr_augment_conts]
QED

Theorem smallstep_drop_conts:
  stepr꙳ (env0, st0, ev0, []) (env, st, ev, []) ⇒
  stepr꙳ (env0, st0, ev0, cs) (env, st, ev, cs)
Proof
  strip_tac >> drule_then assume_tac smallstep_augment_conts >> gs[]
QED

(* converse is not true; imagine an e2 that loops to itself after an initial
   evaluation of e1.  Then being able to get an e2,st pair by starting at
   (e1;;e2) doesn't guarantee you can get there by just evaluating e1 on its
   own
 *)
Theorem break_smallstep_LetNONE:
  stepr꙳ (env0, st0, Exp e1, []) (env, st, Val v, []) ⇒
  stepr꙳ (env0, st0, Exp (e1 ;; e2), []) (env0, st, Exp e2, [])
Proof
  strip_tac >> irule (cj 2 RTC_RULES) >>
  simp[e_step_reln_def, e_step_def, push_def] >>
  drule_then (qspec_then ‘[(Clet NONE () e2,env0)]’ assume_tac)
             smallstep_augment_conts >> gs[] >>
  irule (cj 2 RTC_RULES_RIGHT1) >> first_assum (irule_at Any) >>
  simp[e_step_reln_def, e_step_def, continue_def]
QED

val _ = export_theory();

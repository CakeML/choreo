Theory deadlockFreedom
Ancestors choreoUtils chorSem chorProps chorTypeProps chorType chorLang typeSN envSem richerLang


Definition chorEnvsn_def:
  chorEnvsn Γ s = (∀ p. envsn (localise Γ p) (localise s p))
End

Theorem chorEnvsn_localise_fdom:
  ∀ p. chorEnvsn Γ Δ ⇒ FDOM (localise Γ p) ⊆ FDOM (localise Δ p)
Proof
  rw[chorEnvsn_def, envsn_fdom]
QED

Theorem richerLang_localise_sn:
  chorEnvsn Γ s ∧ typecheck (localise Γ p) e t ⇒
  (∃ cl v. eval_exp cl (localise s p) e = Value v ∧ sn_v t v) ∨
  ∃ cl exn. eval_exp cl (localise s p) e = Exn exn
Proof
  rw[] >>
  drule sn_lemma >> strip_tac >>
  fs[sn_e_def, chorEnvsn_def] >>
  ‘envsn (localise Γ p) (localise s p)’ by metis_tac[] >>
  metis_tac[envsn_g_submap, DRESTRICT_SUBMAP, sn_exec_def]        
QED

Theorem chor_progress_lemma:
  ∀c s. chorTypecheckOK Γ Θ c ∧ chorEnvtype Γ s ∧ chorEnvsn Γ s ⇒
        ∃τ l s' c'. trans (s,c) (τ,l) (s',c') ∨ ¬not_finish c
Proof
  Cases >> rw [] >>
  drule chortype_no_self_communication >> 
  drule chortype_no_undefined_vars >> rpt strip_tac >>
  first_x_assum $ drule_all_then $ strip_assume_tac >~
  [‘IfThen v p c1 c2’, ‘(s, IfThen v p c1 c2)’]
  >- (Cases_on `FLOOKUP s (v,p) = SOME (BoolV T)`
     >- metis_tac [trans_if_true]
     \\ Cases_on `FLOOKUP s (v,p)`
      >- fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘x = (BoolV F)’
      >- metis_tac [trans_if_false]
      >> metis_tac [not_BoolV, trans_if_exn]) >~
  [‘Com p1 v1 p2 v2’]
  >- (rename1 ‘Com p1 v1 p2 v2’
     \\ `∃d. FLOOKUP s' (v1,p1) = SOME d`
             by fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘d’ 
      \\ metis_tac [trans_com, trans_com_exn, no_self_comunication_def]) >~
  [‘Let v p e c’, ‘(s,Let v p e c)’]
  >- (gvs[chorTypecheckOK_let_thm] >> drule richerLang_localise_sn >> strip_tac >>      
      ‘free_vars e ⊆ FDOM (localise s p)’ by metis_tac[typecheck_env_fv, chortype_localise_fdom, SUBSET_TRANS] >>
      first_x_assum $ drule_all_then $ strip_assume_tac >>
      metis_tac[trans_letval, trans_letexn])
  (* Selection *)
  >- metis_tac [trans_sel,no_self_comunication_def]
  (* Recursion *)
  \\ metis_tac [trans_fix]
QED

Theorem chor_progress:
  ∀ c. chorTypecheckOK FEMPTY Θ c ⇒
         ∃τ l s' c'. trans (FEMPTY,c) (τ,l) (s',c') ∨ ¬not_finish c
Proof
  rpt strip_tac >> drule_then irule chor_progress_lemma >>
  rw[chorEnvsn_def, chorEnvtype_def, envsn_def, envtype_def, localise_def]
QED

Theorem envsn_localise_update:
  envsn (localise Γ p) (localise s p) ∧ sn_v ty v ⇒
  ∀ vn p'. envsn (localise (Γ |+ ((vn,p'),ty)) p) (localise (s |+ ((vn,p'),v)) p)
Proof
  rw[envsn_def, localise_flookup] >> Cases_on ‘(s',p) = (vn, p')’ >>
  gvs[FLOOKUP_SIMP] >> metis_tac[]
QED
Theorem chorEnvsn_update:
  chorEnvsn Γ s ∧ sn_v t v ⇒
  ∀vn p. chorEnvsn (Γ |+ ((vn,p),t)) (s |+ ((vn,p),v))
Proof
  rw[chorEnvsn_def] >> metis_tac[envsn_localise_update]
QED
Theorem fmap_update_duplicate:
  FLOOKUP f x = SOME v ⇒ f = f |+ (x,v)
Proof
  rw[] >> irule (iffRL fmap_eq_flookup) >>
  metis_tac[FLOOKUP_SIMP]
QED
Theorem chorEnvsn_state_update:
  FLOOKUP Γ (vn,p) = SOME ty ∧ sn_v ty v ∧ chorEnvsn Γ s ⇒
  chorEnvsn Γ (s |+ ((vn,p), v))
Proof
  metis_tac[chorEnvsn_def, chorEnvsn_update, fmap_update_duplicate]
QED
Theorem chorEnvtype_state_update:
  FLOOKUP Γ (vn,p) = SOME ty ∧ value_type v ty ∧ chorEnvtype Γ s ⇒
  chorEnvtype Γ (s |+ ((vn,p), v))
Proof
  metis_tac[chorEnvtype_def, chortype_update, fmap_update_duplicate]
QED

(*
Theorem chor_preservation:
  ∀ c Θ Γ s. not_finish c ∧ chorEnvsn Γ s ∧ chorEnvtype Γ s ∧ chorTypecheckOK Γ Θ c ⇒
             (∃ s' c' τ l Γ'. trans (s,c) (τ,l) (s',c') ⇒
                              chorEnvtype Γ' s' ∧ chorEnvsn Γ' s' ∧ chorTypecheckOK Γ' Θ c')
Proof
  metis_tac[chorEnvtype_def, envtype_def, localise_flookup, valuetype_EQ_strT, trans_com, value_type_StrV, sn_v_strT, chorEnvsn_state_update, chorEnvtype_state_update]
QED
*)

(* cause we may have trans (s,Nil) _ _ in a goal *)
Theorem trans_not_finish:
  trans (s,c) (τ,l) (s',c') ⇔ not_finish c
Proof
  cheat
QED

Theorem typecheck_eval_value_type_and_sn:
  ∀ G e t c E ev. typecheck G e t ∧ eval_exp c E e = Value ev ∧ envtype G E ∧ envsn G E ⇒
                  value_type ev t ∧ sn_v t ev
Proof
  rw[]
  >- (drule type_soundness >>
      disch_then (qspec_then ‘c’ strip_assume_tac) >>
      first_x_assum $ drule_all_then $ strip_assume_tac >> gvs[])
  >> ‘sn_exec t E e’ by metis_tac[sn_lemma, sn_e_def, envsn_g_submap, DRESTRICT_SUBMAP] >>
  metis_tac[sn_exec_def, eval_exp_value_exn_false, clock_eval_exp_unique]
QED

(*

Issues with cases: collapses basic rules and swap, async rules, so don't know
the form of c'. Have to use induction for swap, async rules anyways.

Finished: all base cases except trans_fix.
        
Didn't finish: recursion, swap, async trans rules.

       For recursion:
       1. chorTypecheckOK Γ' Θ (dsubst c dn (Fix dn c)) is undefined;
       2. fix_if cannot be proved. From IH we know ∃Γ' ... ,
          but in order to prove goal we want Γ' to be Γ, cause Γ is the place
          where the non-recursive branch was typed.
          - This can be solved by requiring if s'=s then we have Γ'=Γ.

       For swap:
       - if swap: we have two ∃Γ' as the results of
         applying IHs of two branches, but we need to type c' in one Γ'.
         We can merge Γ1, Γ2 to be Γ', and it is feasible: Typing for
         current transition tells us c1, c2 can be typed in the same Γ,
         so they do not have contradictory use of free variables. But we
         need 2) here cause Γ1, Γ2 are for c1', c2'.
         
       - Or IH cannot be used directly, e.g. for com/let swap, IH talks about another
         swap transition from (s,c). We need more results to connect the typing for
         swap transition from (s,c) and the typing for current transition from (s,c).

         Such auxiliary lemmas can be, e.g. for com swap:
         - 1) chorTypecheckOK Γ1 Θ c ∧ chorTypecheckOK Γ2 Θ c ⇒
           DRESTRICT Γ1 (free_variables c) = DRESTRICT Γ2 (free_variables c);
         - 2) fv(c)@p1,p2 = fv(c')@p1,p2 after swap;
         - 3) s ' fv(c)@p1,p2 = s' '  fv(c')@p1,p2 after swap.
        
*)
Theorem chor_preservation_lemma:
  ∀ c Θ Γ s τ l s' c'. not_finish c ∧ chorEnvsn Γ s ∧ chorEnvtype Γ s ∧ chorTypecheckOK Γ Θ c ∧ trans (s,c) (τ,l) (s',c') ⇒
                       ∃ Γ'. chorEnvsn Γ' s' ∧ chorEnvtype Γ' s' ∧ chorTypecheckOK Γ' Θ c'
Proof
  Induct_on ‘trans’ >> rw[]
  >- metis_tac[chorEnvsn_update, chortype_update, chorTypecheckOK_com_thm, sn_v_def, value_type_StrV]
  >- metis_tac[chorTypecheckOK_nil]
  >- metis_tac[chorTypecheckOK_sel_thm]
  >- metis_tac[chorTypecheckOK_let_thm, chorEnvtype_def, chorEnvsn_def, typecheck_eval_value_type_and_sn, chorEnvsn_update, chortype_update]
  >- metis_tac[chorTypecheckOK_nil]
  >- metis_tac[chorTypecheckOK_if_thm]
  >- metis_tac[chorTypecheckOK_if_thm]
  >- metis_tac[chorTypecheckOK_nil]
  >- (gvs[trans_not_finish, chorTypecheckOK_if_thm] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >>
      cheat (* cannot prove if swap; IH too weak *) )
  >- (gvs[trans_not_finish, chorTypecheckOK_com_thm] >> cheat
     (* cannot prove com swap; IH unrelated? *))
  >- ( (* sel swap *) gvs[trans_not_finish, chorTypecheckOK_sel_thm]>> metis_tac[])
  >- (gvs[trans_not_finish, chorTypecheckOK_let_thm] >> cheat
     (* cannot prove let swap; same issue with com swap *))
  >- (gvs[trans_not_finish, chorTypecheckOK_com_thm] >> cheat)
  >> cheat
QED

(*
Theorem chor_termination:
  ∀ c s. not_finish c ∧ chorEnvsn Γ s ∧ chorEnvtype Γ s ∧ chorTypecheckOK Γ Θ c ⇒
         ∃ c' s'. ¬not_finish c' ∧ RTC (\x y. ∃l. trans x l y) (s,c) (s’,c’)
Proof
  Induct_on ‘c’ >> cheat
QED
*)

val _ = export_theory ()

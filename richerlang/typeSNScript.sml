open HolKernel Parse boolLib bossLib;

open richerLangTheory envSemTheory optionTheory finite_mapTheory pred_setTheory;

val _ = new_theory "typeSN";


Definition sn_v_def:
  (sn_v intT (IntV n) ⇔ T) ∧
  (sn_v strT (StrV s) ⇔ T) ∧
  (sn_v boolT (BoolV b) ⇔ T) ∧
  (sn_v (fnT t1 t2) (Clos s e E) ⇔
     ∀ v. sn_v t1 v ⇒ (∃ cl v'. eval_exp cl (E|+(s,v)) e = Value v' ∧ sn_v t2 v') ∨
                      (∃ cl exn. eval_exp cl (E|+(s,v)) e = Exn exn)) ∧
  (sn_v (pairT t1 t2) (PairV v1 v2) ⇔ sn_v t1 v1 ∧ sn_v t2 v2) ∧
  (sn_v (sumT t1 t2) (SumLV v) ⇔ sn_v t1 v) ∧
  (sn_v (sumT t1 t2) (SumRV v) ⇔ sn_v t2 v) ∧
  (sn_v _ _ ⇔ F)
Termination
  WF_REL_TAC ‘inv_image (measure type_size) FST’
End

Definition envsn_def:
  envsn G E ⇔
    ∀ s ty. FLOOKUP G s = SOME ty ⇒ (∃ v. FLOOKUP E s = SOME v ∧ sn_v ty v)
End

Definition sn_exec_def:
  sn_exec t E e ⇔ (∃ cl v. eval_exp cl E e = Value v ∧ sn_v t v) ∨
                  ∃ cl exn. eval_exp cl E e = Exn exn
End

Definition sn_e_def:
  sn_e G t e ⇔ ∀ E. envsn (DRESTRICT G (free_vars e)) E ⇒ sn_exec t E e
End

Theorem envsn_fdom:
  envsn G E ⇒ FDOM G ⊆ FDOM E
Proof
  rw[envsn_def, SUBSET_DEF, TO_FLOOKUP] >> metis_tac[option_CLAUSES]
QED

Theorem envsn_g_domsub_update:
  envsn (G \\ s) E ∧ sn_v ty v ⇒
  envsn (G |+ (s,ty)) (E |+ (s,v))
Proof
  rw[envsn_def] >> Cases_on ‘s = s'’ >> gvs[FLOOKUP_SIMP, DOMSUB_FLOOKUP_NEQ]
QED

Theorem envsn_fdom_subset:
  envsn G E ⇒ FDOM G ⊆ FDOM E
Proof
  rw[envsn_def, SUBSET_DEF, TO_FLOOKUP] >> metis_tac[option_CLAUSES]
QED

(* utils *)
Theorem flookup_submap_rev:
  f ⊑ g ∧ k ∈ FDOM f ∧ FLOOKUP g k = SOME v ⇒ FLOOKUP f k = SOME v
Proof
  rw[FLOOKUP_DEF, SUBMAP_DEF]
QED

Theorem envsn_e_submap:
  envsn G E ∧ E' ⊑ E ∧ FDOM G ⊆ FDOM E' ⇒ envsn G E'
Proof
  rw[envsn_def] >> ‘s ∈ FDOM E'’ by gvs[FLOOKUP_DEF, SUBSET_DEF] >>
  rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >>
  metis_tac[flookup_submap_rev]
QED

Theorem envsn_e_submap2:
  envsn G E ∧ E ⊑ E' ⇒ envsn G E'
Proof
  metis_tac[envsn_def, FLOOKUP_SUBMAP]
QED

(* utils *)
Theorem subset_inter_same:
  A ∩ C ⊆ B ⇒ A ∩ C ⊆ B ∩ C
Proof
  rw[INTER_DEF, SUBSET_DEF]
QED

(* utils *)
Theorem subset_inter_same2:
  B ⊆ C ⇒ A ∩ B ⊆ A ∩ C
Proof
  rw[INTER_DEF, SUBSET_DEF]
QED

Theorem envsn_g_submap:
  envsn G E ∧ G' ⊑ G ⇒ envsn G' E
Proof
  rw[envsn_def, SUBMAP_FLOOKUP_EQN]
QED

Theorem envsn_update:
  envsn G E ∧ sn_v t v ⇒ envsn (G|+(s,t)) (E|+(s,v))
Proof
  rw[envsn_def] >> Cases_on ‘s = s'’ >> gvs[FLOOKUP_SIMP]
QED

Theorem envsn_g_domsub:
  envsn (G \\ x) E ⇒ envsn (G \\ x) (E \\ x)
Proof
  rw[envsn_def, DOMSUB_FLOOKUP_THM]
QED

(* utils *)
Theorem drestrict_not_in:
  x ∉ A ⇒ FLOOKUP (DRESTRICT f A) x = NONE
Proof
  rw[FLOOKUP_DRESTRICT]
QED

Theorem sn_v_intT:
  ∀ v. sn_v intT v ⇔
         ∃ n. v = IntV n
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem sn_v_strT:
  ∀ v. sn_v strT v ⇔
         ∃ s. v = StrV s
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem sn_v_boolT:
  ∀ v. sn_v boolT v ⇔
         ∃ b. v = BoolV b
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem sn_v_pairT:
  ∀ v t1 t2. sn_v (pairT t1 t2) v ⇔
               ∃ v1 v2. v = (PairV v1 v2) ∧ sn_v t1 v1 ∧ sn_v t2 v2
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem sn_v_fnT:
  ∀ v t1 t2. sn_v (fnT t1 t2) v ⇒
             ∃ s e E. v = Clos s e E ∧
                      (∀ v0. sn_v t1 v0 ⇒ (∃ cl v'. eval_exp cl (E|+(s,v0)) e = Value v' ∧ sn_v t2 v') ∨
                                          (∃ cl exn. eval_exp cl (E|+(s,v0)) e = Exn exn))
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem sn_v_sumT:
  ∀ v t1 t2. sn_v (sumT t1 t2) v ⇒
             ∃ v0. (v = SumLV v0 ∧ sn_v t1 v0) ∨ v = SumRV v0 ∧ sn_v t2 v0
Proof
  Cases_on ‘v’ >> gvs[sn_v_def]
QED

Theorem bop_sn_lemma:
  ∀ bop v1 v2 ty. sn_v t1 v1 ∧ sn_v t2 v2 ∧ boptype bop t1 t2 ty ⇒
                  (∃ v. eval_bop bop v1 v2 = Value v ∧ sn_v ty v) ∨
                  (∃ exn. eval_bop bop v1 v2 = Exn exn)
Proof
  rw[boptype_cases] >> gvs[sn_v_intT, sn_v_strT, sn_v_boolT, PULL_EXISTS, eval_bop_def, binIop_def, binSop_def, AllCaseEqs(), sn_v_def]
QED

Theorem uop_sn_lemma:
  ∀ uop v ty. sn_v t1 v ∧ uoptype uop t1 ty ⇒
              (∃ v'. eval_uop uop v = Value v' ∧ sn_v ty v') ∨
              (∃ e. eval_uop uop v = Exn e)
Proof
  rw[uoptype_cases]
  >- ( (* NOT *) gvs[sn_v_boolT, PULL_EXISTS, eval_uop_def, result_bind_def])
  >- ( (* NumOf *) gvs[sn_v_strT, PULL_EXISTS, eval_uop_def, result_bind_def] >> Cases_on ‘string_to_int2 s’ >> simp[sn_v_def])
  >> gvs[sn_v_intT, sn_v_pairT, PULL_EXISTS, eval_uop_def, result_bind_def, sn_v_def]
QED

(* utils *)
Theorem drestrict_diff_update:
  x ∈ A ⇒ DRESTRICT f (A DIFF {x}) |+ (x,v) = DRESTRICT f A |+ (x,v)
Proof
  rw[] >> metis_tac[STRONG_DRESTRICT_FUPDATE, DELETE_DEF, DRESTRICT_FUPDATE]
QED

Theorem sn_lemma:
  ∀ G e t. typecheck G e t ⇒ sn_e G t e
Proof
  Induct_on ‘typecheck’ >> rw[sn_e_def, sn_v_def, eval_exp_def] >> gvs[AllCaseEqs(), PULL_EXISTS, result_bind_eq_value, sn_exec_def] >> rpt (first_x_assum $ drule_all_then $ strip_assume_tac)
  >- (rw[eval_exp_def] >> gvs[AllCaseEqs(), FLOOKUP_SIMP, envsn_def]) >~
  [‘Fn s e’, ‘fnT dt rt’]
  >- (rw[eval_exp_def] >> simp[sn_v_def] >> rpt strip_tac >> first_x_assum irule >>
      ‘FDOM (DRESTRICT G (free_vars e DIFF {s})) ⊆ FDOM (DRESTRICT E (free_vars e))’ suffices_by metis_tac[envsn_g_domsub_update, DOMSUB_FUPDATE, DRESTRICT_DOMSUB, DELETE_DEF, DRESTRICT_SUBMAP, envsn_e_submap] >>
      metis_tac[FDOM_DRESTRICT, subset_inter_same, envsn_fdom_subset, DIFF_SUBSET, subset_inter_same2, SUBSET_TRANS]) >~
  [‘Fn s e’, ‘fnT dt rt’, ‘s ∉ free_vars e’]
  >- (rw[eval_exp_def] >> simp[sn_v_def] >> rpt strip_tac >> first_x_assum irule >>
      ‘envsn (DRESTRICT G (free_vars e)) (DRESTRICT E (free_vars e))’ suffices_by metis_tac[SUBMAP_FUPDATE_FLOOKUP, drestrict_not_in, envsn_e_submap2] >>
      metis_tac[diff_eq_same, FDOM_DRESTRICT, DRESTRICT_SUBMAP, envsn_fdom_subset, subset_inter_same, envsn_e_submap]) >~
  [‘typecheck G ge boolT’]
  >- (rw[eval_exp_def] >>
      ‘envsn (DRESTRICT G (free_vars ge)) E ∧ envsn (DRESTRICT G (free_vars e')) E ∧ envsn (DRESTRICT G (free_vars e'')) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac)
      >- (Cases_on ‘v''’ >> gvs[sn_v_def] >> disj1_tac >> qexists ‘cl+cl'+cl''’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
      >- (disj2_tac >> qexists ‘cl''’ >> simp[])
      >- (Cases_on ‘v'’ >> gvs[sn_v_def] >> Cases_on ‘b’
          >- (disj2_tac >> qexists ‘cl''+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
          >> disj1_tac >> qexists ‘cl''+cl’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
      >- (disj2_tac >> qexists ‘cl''’ >> simp[])
      >- (Cases_on ‘v'’ >> gvs[sn_v_def] >> Cases_on ‘b’
          >- (disj1_tac >> qexists ‘cl''+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
          >> disj2_tac >> qexists ‘cl''+cl’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
      >- (disj2_tac >> qexists ‘cl''’ >> simp[])
      >- (Cases_on ‘v’ >> gvs[sn_v_def] >> disj2_tac >> qexists ‘cl+cl'+cl''’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[] >> metis_tac[])
      >> disj2_tac >> qexists ‘cl''’ >> simp[])
     >>~- ([‘envsn (DRESTRICT G ∅) E’], rw[eval_exp_def, sn_v_def]) >~
  [‘boptype bop t1 t2’]
  >- (‘envsn (DRESTRICT G (free_vars e)) E ∧ envsn (DRESTRICT G (free_vars e')) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
                                                                   >>~- ([‘Exn exn’], disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> drule bop_sn_lemma >> strip_tac >> rpt (first_x_assum $ drule_all_then $ strip_assume_tac)
      >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[]) >~
  [‘uoptype uop argt ty’]
  >- (rw[eval_exp_def] >> drule uop_sn_lemma >> strip_tac >> rpt (first_x_assum $ drule_all_then $ strip_assume_tac)
      >- (disj1_tac >> qexists ‘cl’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘uoptype uop argt ty’, ‘eval_exp cl E e = Exn exn’]
  >- (rw[eval_exp_def] >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Let vn arg body’, ‘vn ∈ free_vars body’, ‘typecheck G arg t1’, ‘typecheck (G|+(vn,t1)) body t2’]
  >- (‘envsn (DRESTRICT G (free_vars arg)) E ∧ envsn (DRESTRICT G (free_vars body DIFF {vn})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      first_x_assum $ drule_all_then $ strip_assume_tac
      >- (‘envsn (DRESTRICT G (free_vars body) |+ (vn,t1)) (E |+ (vn,v))’ by metis_tac[envsn_update, drestrict_diff_update] >> first_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
          >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> rw[eval_exp_def] >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Let vn arg body’, ‘vn ∉ free_vars body’, ‘typecheck G arg t1’, ‘typecheck (G|+(vn,t1)) body t2’]
  >- (‘envsn (DRESTRICT G (free_vars arg)) E ∧ envsn (DRESTRICT G (free_vars body DIFF {vn})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      last_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
      >- (‘envsn (DRESTRICT G (free_vars body)) (E |+ (vn,v))’ by metis_tac[DRESTRICT_DOMSUB, DELETE_DEF, envsn_g_domsub, diff_eq_same, envsn_e_submap2, SUBMAP_FUPDATE_FLOOKUP, DOMSUB_FLOOKUP, FUPDATE_PURGE] >>
          first_x_assum $ drule_all_then $ strip_assume_tac
          >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘typecheck G e1 (fnT argt ty)’, ‘App e1 e2’]
  >- (‘envsn (DRESTRICT G (free_vars e1)) E ∧ envsn (DRESTRICT G (free_vars e2)) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
      >- (drule sn_v_fnT >> strip_tac >> first_x_assum $ drule_all_then $ strip_assume_tac
          >- (disj1_tac >> qexists ‘cl+cl'+cl''+1’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'+cl''+1’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl+cl'+1’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Case e s1 e1 s2 e2’, ‘s1 ∈ free_vars e1’, ‘s2 ∈ free_vars e2’]
  >- (‘envsn (DRESTRICT G (free_vars e)) E ∧ envsn (DRESTRICT G (free_vars e1 DIFF {s1})) E ∧ envsn (DRESTRICT G (free_vars e2 DIFF {s2})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      last_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
      >- (drule sn_v_sumT >> strip_tac
          >- (‘envsn (DRESTRICT G (free_vars e1) |+ (s1,t1)) (E |+ (s1,v0))’ by metis_tac[envsn_update, drestrict_diff_update] >>
              rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
              >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
              >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
          >> ‘envsn (DRESTRICT G (free_vars e2) |+ (s2,t2)) (E |+ (s2,v0))’ by metis_tac[envsn_update, drestrict_diff_update] >>
          rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
          >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Case e s1 e1 s2 e2’, ‘s1 ∈ free_vars e1’, ‘s2 ∉ free_vars e2’]
  >- (‘envsn (DRESTRICT G (free_vars e)) E ∧ envsn (DRESTRICT G (free_vars e1 DIFF {s1})) E ∧ envsn (DRESTRICT G (free_vars e2 DIFF {s2})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      last_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
      >- (drule sn_v_sumT >> strip_tac
          >- (‘envsn (DRESTRICT G (free_vars e1) |+ (s1,t1)) (E |+ (s1,v0))’ by metis_tac[envsn_update, drestrict_diff_update] >>
              rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
              >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
              >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
          >> ‘envsn (DRESTRICT G (free_vars e2)) (E |+ (s2,v0))’ by metis_tac[DRESTRICT_DOMSUB, DELETE_DEF, envsn_g_domsub, diff_eq_same, envsn_e_submap2, SUBMAP_FUPDATE_FLOOKUP, DOMSUB_FLOOKUP, FUPDATE_PURGE] >>
          rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
          >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Case e s1 e1 s2 e2’, ‘s1 ∉ free_vars e1’, ‘s2 ∈ free_vars e2’]
  >- (‘envsn (DRESTRICT G (free_vars e)) E ∧ envsn (DRESTRICT G (free_vars e1 DIFF {s1})) E ∧ envsn (DRESTRICT G (free_vars e2 DIFF {s2})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
      last_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
      >- (drule sn_v_sumT >> strip_tac
          >- (‘envsn (DRESTRICT G (free_vars e1)) (E |+ (s1,v0))’ by metis_tac[DRESTRICT_DOMSUB, DELETE_DEF, envsn_g_domsub, diff_eq_same, envsn_e_submap2, SUBMAP_FUPDATE_FLOOKUP, DOMSUB_FLOOKUP, FUPDATE_PURGE] >>
              rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
              >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
              >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
          >> ‘envsn (DRESTRICT G (free_vars e2) |+ (s2,t2)) (E |+ (s2,v0))’ by metis_tac[envsn_update, drestrict_diff_update] >>
              rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
              >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]) >~
  [‘Case e s1 e1 s2 e2’, ‘s1 ∉ free_vars e1’, ‘s2 ∉ free_vars e2’]
  >> ‘envsn (DRESTRICT G (free_vars e)) E ∧ envsn (DRESTRICT G (free_vars e1 DIFF {s1})) E ∧ envsn (DRESTRICT G (free_vars e2 DIFF {s2})) E’ by metis_tac[envsn_g_submap, DRESTRICT_SUBSET_SUBMAP, SUBSET_UNION] >>
  last_x_assum $ drule_all_then $ strip_assume_tac >> rw[eval_exp_def]
  >- (drule sn_v_sumT >> strip_tac
      >- (‘envsn (DRESTRICT G (free_vars e1)) (E |+ (s1,v0))’ by metis_tac[DRESTRICT_DOMSUB, DELETE_DEF, envsn_g_domsub, diff_eq_same, envsn_e_submap2, SUBMAP_FUPDATE_FLOOKUP, DOMSUB_FLOOKUP, FUPDATE_PURGE] >>
          rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
          >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
          >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
      >> ‘envsn (DRESTRICT G (free_vars e2)) (E |+ (s2,v0))’ by metis_tac[DRESTRICT_DOMSUB, DELETE_DEF, envsn_g_domsub, diff_eq_same, envsn_e_submap2, SUBMAP_FUPDATE_FLOOKUP, DOMSUB_FLOOKUP, FUPDATE_PURGE] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> rw[eval_exp_def]
      >- (disj1_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt strip_tac >> gvs[])
      >> disj2_tac >> qexists ‘cl+cl'’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[])
  >> disj2_tac >> qexists ‘cl’ >> rpt (dxrule clock_exn_increment) >> rpt strip_tac >> gvs[]
QED

Theorem richerLang_sn:
  ∀ G e t. typecheck FEMPTY e t ⇒ (∃ cl v E. eval_exp cl E e = Value v ∧ sn_v t v) ∨
                             ∃ cl exn E. eval_exp cl E e = Exn exn
Proof
  rw[] >>
  drule sn_lemma >> strip_tac >>
  fs[sn_v_def, sn_e_def, sn_exec_def, envsn_def] >>
  metis_tac[]
QED

        
val _ = export_theory();


open HolKernel boolLib Parse bossLib;
open relationTheory
     bisimulationTheory;

val _ = new_theory "bisimulation_ext";

(* This file is in an odd format because it should be
   PRd into HOL *)

(* Bisimulation Relation is equivalence relation *)
val BISIM_REL_IS_EQUIV_REL = store_thm(
  "BISIM_REL_IS_EQUIV_REL",
  ``!ts. equivalence (BISIM_REL ts)``,
  SRW_TAC[][equivalence_def]
  >- (SRW_TAC[][reflexive_def, BISIM_REL_def] >>
      Q.EXISTS_TAC ‘$=’ >>
      SRW_TAC[][BISIM_def])
  >- (SRW_TAC[][symmetric_def, BISIM_REL_def] >>
      SRW_TAC[][EQ_IMP_THM] >>
      Q.EXISTS_TAC ‘SC R’ >>
      FULL_SIMP_TAC (srw_ss ()) [BISIM_def,SC_DEF] >>
      METIS_TAC[])
  >- (SRW_TAC[][transitive_def,BISIM_REL_def] >>
      Q.EXISTS_TAC ‘\a c. ?b. R a b /\ R' b c’ >>
      FULL_SIMP_TAC (srw_ss ()) [BISIM_def] >>
      METIS_TAC[]));

(* BISIMULATION RELATION IS COINDUCTION *)
(* Define equivalent coinduction bi *)
val (bi_rules,bi_coind,bi_cases) =
Hol_coreln
‘
  !x y. (!x' l. ts x l x' ==> ?y'. ts y l y' /\ bi ts x' y') /\
        (!y' l. ts y l y' ==> ?x'. ts x l x' /\ bi ts x' y') ==>
        bi ts x y
’;
(* Prove equivalence both ways *)
(* -- BISIM_REL gives bi *)
val BISIM_REL_bi = store_thm(
  "BISIM_REL_bi",
  ``!x y. BISIM_REL ts x y ==> bi ts x y``,
  ho_match_mp_tac bi_coind >>
  SRW_TAC [][] >>
  RULE_ASSUM_TAC (REWRITE_RULE [BISIM_REL_def]) >>
  FULL_SIMP_TAC (srw_ss()) []
  >- (`?y'. ts y l y' /\ R x' y'`
        by (FULL_SIMP_TAC (srw_ss ())[BISIM_def] >>
            METIS_TAC[]) >>
      Q.EXISTS_TAC `y'` >>
      FULL_SIMP_TAC (srw_ss()) [BISIM_REL_def] >>
      Q.EXISTS_TAC `R` >>
      FULL_SIMP_TAC (srw_ss ()) [])
  >- (‘?x'. ts x l x' /\ R x' y'’
        by (FULL_SIMP_TAC (srw_ss ()) [BISIM_def] >>
            METIS_TAC[]) >>
      Q.EXISTS_TAC `x'` >>
      FULL_SIMP_TAC (srw_ss ()) [BISIM_REL_def] >>
      Q.EXISTS_TAC `R` >> fs[]));
(* -- bi gives BISIM_REL *)
Theorem bi_BISIM_REL:
  !x y. bi ts x y ==> BISIM_REL ts x y
Proof
  SRW_TAC [] [BISIM_REL_def] >>
  Q.EXISTS_TAC `bi ts` >>
  simp[BISIM_def] >>
  first_x_assum (K ALL_TAC) >>
  METIS_TAC[bi_cases]
QED
(* -- bi and BISIM_REL are equal by extensionality *)
Theorem bi_is_BISIM_REL:
  BISIM_REL = bi
Proof
  simp[FUN_EQ_THM] >>
  METIS_TAC[BISIM_REL_bi,bi_BISIM_REL]
QED


val _ = export_theory ();

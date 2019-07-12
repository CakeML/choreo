open  HolKernel
      boolLib
      bossLib
      relationTheory;

val _ = new_theory "bisimulation";

val BISIM_def = new_definition(
  "BISIM_def",
  ``BISIM ts R = !p q l.
                    R p q ==>
                    (!p'. ts p l p' ==> (?q'. ts q l q' /\ R p' q')) /\
                    (!q'. ts q l q' ==> (?p'. ts p l p' /\ R p' q'))``)

val BISIM_REL_def = new_definition(
  "BISIM_REL_def",
  ``BISIM_REL ts p q = ?R. BISIM ts R /\ R p q``)

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

val _ = export_theory ();

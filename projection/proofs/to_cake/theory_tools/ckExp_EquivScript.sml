open HolKernel boolLib Parse bossLib;
open semanticPrimitivesTheory
     evaluateTheory
     terminationTheory
     evaluatePropsTheory
     ml_translatorTheory;
open evaluate_toolsTheory
     evaluate_rwLib;

val _ = new_theory "ckExp_Equiv";

val WORD8 = “WORD:word8 -> v -> bool”;

(* UNIQUE CORRECT TRANSLATION FRAMEWORK *)
(* Basic Injective HOL, CakeML mapping constraint
   (Unique Correct Translation *)
Definition UNCT_def:
  UNCT (tf:α -> v -> bool) = ∀(a:α) (v1 v2:v). tf a v1 ∧ tf a v2 ⇒ v1 = v2
End

(* Preexistent UNCT maps *)
Theorem INT_UNCT:
  UNCT INT
Proof
  rw[UNCT_def,INT_def] 
QED

Theorem NUM_UNCT:
  UNCT NUM
Proof
  rw[UNCT_def,NUM_def,INT_def] 
QED

Theorem BOOL_UNCT:
  UNCT BOOL
Proof
  rw[UNCT_def,BOOL_def]
QED

Theorem WORD_UNCT:
  UNCT WORD
Proof
  rw[UNCT_def,WORD_def]
QED

Theorem CHAR_UNCT:
  UNCT CHAR
Proof
  rw[UNCT_def,CHAR_def]
QED

Theorem STRING_TYPE_UNCT:
  UNCT STRING_TYPE
Proof
  rw[UNCT_def] >>
  Cases_on ‘a’ >>
  fs[STRING_TYPE_def]
QED

(* -- List version of UNCT type is UNCT *)
Theorem LIST_TYPE_UNCT:
  ∀tf.
    UNCT tf ⇒ UNCT (LIST_TYPE tf)
Proof
  simp[UNCT_def] >>
  strip_tac >>
  strip_tac >>
  Induct_on ‘a’
  >- rw[LIST_TYPE_def]
  >- (rpt strip_tac >>
      fs[LIST_TYPE_def] >>
      metis_tac[])
QED


(* BASIC CAKEML EXP TO HOL EQUIVALENCE FRAMEWORK *)
(* Basic Definition of CakeML Expression/HOL Term equivalence *)
Definition ck_equiv_hol_def:
  ck_equiv_hol cEnv hT cExp hVal =
    ∀arefs.
      ∃bc1 bc2 drefs cVal.
        hT hVal cVal ∧
        evaluate (empty_state with <|clock := bc1; refs := arefs|>) cEnv [cExp] = 
          (empty_state with <|clock := bc2; refs := arefs ++ drefs|>,
          Rval [cVal])
End

(* Methods of applying equivalence *)
(* -- Application of equivalence to produce
      equivalent result in arbtirary state *)
Theorem ck_equiv_hol_apply:
  ∀ cEnv hT cExp hV.
    ck_equiv_hol cEnv hT cExp hV ⇒
      ∀cSt.
        ∃bc1 bc2 drefs cV.
          hT hV cV ∧
          ∀dc.
            evaluate (cSt with clock := bc1 + dc) cEnv [cExp]
            = (cSt with <|clock := dc + bc2;
                          refs := cSt.refs ++ drefs|>,
                      Rval [cV])
Proof
  rpt strip_tac >>
  fs[ck_equiv_hol_def] >>
  first_x_assum (qspec_then ‘cSt.refs’ strip_assume_tac) >>
  MAP_EVERY qexists_tac [‘bc1’,‘bc2’,‘drefs’,‘cVal’] >>
  simp[evaluate_generalise]
QED

(* -- Identical to original but quantifiers moved.
      This is useful because if polymorphic theorems
      (cSt can have any FFI model type) are introduced
      in a HOL proof without being fully intialised they
      are given arbitrary fixed types. So state is at
      top to be specialised at the beginning. *)
Theorem ck_equiv_hol_apply_alt:
  ∀ cEnv hT cExp hV cSt.
    ck_equiv_hol cEnv hT cExp hV ⇒
      ∃bc1 bc2 drefs cV.
        hT hV cV ∧
        ∀dc.
          evaluate (cSt with clock := bc1 + dc) cEnv [cExp]
          = (cSt with <|clock := dc + bc2;
                        refs := cSt.refs ++ drefs|>,
                    Rval [cV])
Proof
  rw[] >>
  drule_then (qspec_then ‘cSt’ strip_assume_tac) ck_equiv_hol_apply >>
  MAP_EVERY qexists_tac [‘bc1’,‘bc2’,‘drefs’,‘cV’] >>
  simp[]
QED

(* -- Swap Expression in Function argument with equivalent literal *)
Theorem ck_equiv_hol_apply_lit_App:
  ∀fexp aexp hT hA cEnv cL.
    UNCT hT                      ∧
    hT hA (Litv cL)              ∧
    ck_equiv_hol cEnv hT aexp hA
     ⇒
    ∀cSt.
        ∃mc1 mc2 drefs.
          ∀dc.
            evaluate (cSt with clock := mc1 + dc) cEnv [App Opapp [fexp;aexp]]
            = evaluate (cSt with <|clock := mc2 + dc; refs := cSt.refs ++ drefs|>) cEnv
              [App Opapp [fexp; Lit cL]]
Proof
  rpt strip_tac >>
  rw[evaluate_def] >>
  qpat_x_assum ‘ck_equiv_hol cEnv hT aexp hA’ assume_tac >>
  drule_then (qspec_then ‘cSt’ strip_assume_tac) ck_equiv_hol_apply >>
  rename1 ‘∀dc.
            evaluate (cSt with clock := bc1_a + dc) cEnv [aexp] =
            (cSt with <|clock := dc + bc2_a; refs := cSt.refs ++ drefs_a|>,
             Rval [cV])’ >>
  Q.REFINE_EXISTS_TAC ‘bc1_a + mc1’ >>
  simp[] >>
  MAP_EVERY qexists_tac [‘0’,‘bc2_a’,‘drefs_a’] >>
  ‘Litv cL = cV’
    suffices_by simp[] >>
  metis_tac[UNCT_def]
QED

(* Methods of constructing equivalence *)
(* -- Literals *)
Theorem ck_equiv_hol_Lit:
  ∀hT cL cEnv hL.
    hT hL (Litv cL) ⇒
    ck_equiv_hol cEnv hT (Lit cL) hL
Proof
  rpt strip_tac >>
  rw[ck_equiv_hol_def,evaluate_def] >>
  MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
  rw[]
QED

(* -- Variables *)
Theorem ck_equiv_hol_Var:
  ∀cEnv vid hT hV.
    (∃cV. nsLookup cEnv.v vid = SOME cV ∧
          hT hV cV) ⇒
    ck_equiv_hol cEnv hT (Var vid) hV
Proof
  rpt strip_tac >>
  rw[ck_equiv_hol_def,evaluate_def] >>
  MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
  rw[]
QED

(* -- Function Application *)
Theorem ck_equiv_hol_App:
  ∀fexp hf aexp ha tA tB cEnv.
    ck_equiv_hol cEnv tA aexp ha          ∧
    ck_equiv_hol cEnv (tA --> tB) fexp hf ⇒
    ck_equiv_hol cEnv tB (App Opapp [fexp;aexp]) (hf ha)
Proof
  rpt strip_tac >>
  rw[ck_equiv_hol_def] >>
  fs[ck_equiv_hol_def] >>
  rw [evaluate_def] >>
  last_x_assum (qspec_then ‘arefs’ strip_assume_tac) >>
  rename1 ‘evaluate (empty_state with <|clock := bc1_a; refs := arefs|>) cEnv
                   [aexp] = (empty_state with <|clock := bc2_a;
                                                refs := arefs ++ drefs_a|>,
                             Rval [cVal_a])’ >>
  Q.REFINE_EXISTS_TAC ‘bc1_a + bc1’ >>
  ‘∀bc1. evaluate (empty_state with <|clock := bc1_a + bc1; refs := arefs|>) cEnv
                   [aexp] = (empty_state with <|clock := bc2_a + bc1;
                                                refs := arefs ++ drefs_a|>,
                             Rval [cVal_a])’
    by (rpt strip_tac >>
        qspecl_then [‘empty_state with <|clock := bc1_a;
                                         refs := arefs|>’,
                     ‘cEnv’, ‘[aexp]’,
                     ‘empty_state with <|clock := bc2_a;
                                         refs := arefs ++ drefs_a|>’,
                     ‘Rval [cVal_a]’, ‘bc1’]
                assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  rfs[] >>
  ntac 2 (first_x_assum (K ALL_TAC)) >>
  last_x_assum (qspec_then ‘arefs ++ drefs_a’ strip_assume_tac) >>
  rename1 ‘evaluate (empty_state with <|clock := bc1_f;
                                        refs := arefs ++ drefs_a|>)
                    cEnv [fexp] = (empty_state with <|clock := bc2_f;
                                                      refs  := arefs
                                                               ++ drefs_a
                                                               ++ drefs_f|>,
                                   Rval [cVal_f])’ >>
  Q.REFINE_EXISTS_TAC ‘bc1_f + bc1’ >>
  ‘∀bc1. evaluate (empty_state with <|clock := bc1_f + bc1 + bc2_a;
                                refs := arefs ++ drefs_a|>)
            cEnv
            [fexp] = (empty_state with <|clock := bc2_f + bc1 + bc2_a;
                                         refs  := arefs ++ drefs_a ++ drefs_f|>,
                      Rval [cVal_f])’
    by (rpt strip_tac >>
        qspecl_then [‘empty_state with <|clock := bc1_f;
                                         refs := arefs ++ drefs_a|>’,
                     ‘cEnv’, ‘[fexp]’,
                     ‘empty_state with <|clock := bc2_f;
                                         refs := arefs ++ drefs_a ++ drefs_f|>’,
                     ‘Rval [cVal_f]’, ‘bc1 + bc2_a’]
                assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  rfs[] >>
  ntac 2 (first_x_assum (K ALL_TAC)) >>
  qspecl_then [‘cVal_f’,‘hf’,‘ha’,‘cVal_a’,‘tA’,‘tB’,
               ‘empty_state with <|refs := arefs ++ drefs_a ++ drefs_f|>’]
  strip_assume_tac do_opapp_translate >>
  rfs[] >>
  rename1 ‘∀dc.
            evaluate
              (empty_state with
               <|clock := bc1 + dc; refs := arefs ++ drefs_a ++ drefs_f|>)
              cfa_env [cfa_exp] =
            (empty_state with
             <|clock := bc2 + dc;
               refs := arefs ++ drefs_a ++ drefs_f ++ drefs|>,Rval [crv])’ >>
  MAP_EVERY qexists_tac [‘SUC bc1’,‘bc2+(bc2_a+bc2_f)’,‘drefs_a ++ drefs_f ++ drefs’,‘crv’] >>
  rw[arithmeticTheory.ADD1,dec_clock_def]
QED

(* -- Equality of byte arrays/lists *)
Theorem ck_equiv_hol_apply_list_word8_equality:
  ∀cEnv aexp hA bexp hB.
    ck_equiv_hol cEnv (LIST_TYPE ^WORD8) aexp hA ∧
    ck_equiv_hol cEnv (LIST_TYPE ^WORD8) bexp hB   ⇒
    ck_equiv_hol cEnv BOOL (App Equality [aexp;bexp]) (hA = hB)
Proof
  rpt strip_tac >>
  rw [ck_equiv_hol_def] >>
  CONV_TAC (RESORT_EXISTS_CONV rev) >>
  MAP_EVERY qexists_tac [‘Boolv (hA = hB)’] >>
  simp trans_sl >>
  CONV_TAC (RESORT_EXISTS_CONV rev) >>
  qmatch_goalsub_abbrev_tac ‘evaluate (cSt with clock := _) _ _’ >>
  qspecl_then [‘cEnv’,‘LIST_TYPE ^WORD8’,‘bexp’,‘hB’,‘cSt’]
              strip_assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + r1’ >>
  rw eval_sl >>
  qpat_x_assum ‘∀dc. P dc’ (K ALL_TAC) >>
  qunabbrev_tac ‘cSt’ >>
  simp [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (cSt with clock := _) _ _’ >>
  qspecl_then [‘cEnv’,‘LIST_TYPE ^WORD8’,‘aexp’,‘hA’,‘cSt’]
              strip_assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + r1’ >>
  simp[] >>
  qpat_x_assum ‘∀dc. P dc’ (K ALL_TAC)
  >- (‘cV' = cV’
        by metis_tac[UNCT_def,LIST_TYPE_UNCT,WORD_UNCT] >>
      fs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘∀hL cL. LIST_TYPE ^WORD8 hL cL ⇒ (do_eq cL cL = Eq_val T)’
        suffices_by (qunabbrev_tac ‘cSt’ >> rw[] >> ‘do_eq cV cV = Eq_val T’ by metis_tac[] >>
                     simp[] >> MAP_EVERY qexists_tac [‘0’,‘bc2 + bc2'’,‘drefs ++ drefs'’] >>
                     simp[state_component_equality]) >>
      Induct_on ‘hL’
      >- (rw trans_sl >> EVAL_TAC)
      >- (Cases_on ‘cL’ >> rw [do_eq_def,LIST_TYPE_def] >>
          rw [do_eq_def] >> Cases_on ‘v2_1’ >> fs[do_eq_def,WORD_def]))
  >- (‘∀hAt cAt hBt cBt.
        LIST_TYPE ^WORD8 hAt cAt ∧
        LIST_TYPE ^WORD8 hBt cBt ∧
        hAt ≠ hBt ⇒
        (do_eq cAt cBt = Eq_val F)’
        suffices_by (qunabbrev_tac ‘cSt’ >> rw[] >> ‘do_eq cV' cV = Eq_val F’ by metis_tac[] >>
                     simp[] >> MAP_EVERY qexists_tac [‘0’,‘bc2 + bc2'’,‘drefs ++ drefs'’] >>
                     simp[state_component_equality]) >>
      Induct_on ‘hAt’
      >- (rw[LIST_TYPE_def] >> Cases_on ‘hBt’ >> fs [] >>
          fs[LIST_TYPE_def] >> rw[do_eq_def] >>
          fs[ctor_same_type_def,same_type_def])
      >- (rw[LIST_TYPE_def] >> Cases_on ‘hBt’ >> fs[LIST_TYPE_def] >>
          rw[do_eq_def] >> fs[ctor_same_type_def,same_type_def] >>
          Cases_on ‘v2_1’ >> Cases_on ‘v2_1'’ >> fs trans_sl >>
          rw[do_eq_def] >> fs[lit_same_type_def,same_type_def] >>
          ‘do_eq v2_2 v2_2' = Eq_val F’
            by metis_tac[] >>
          Cases_on ‘h = h'’ >> simp[]))
QED

val _ = export_theory()
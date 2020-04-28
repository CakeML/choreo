open preamble;
open optionTheory
     rich_listTheory;
open endpoint_to_payloadTheory;
open payloadLangTheory
     payloadSemTheory
     payloadPropsTheory
     payload_to_cakemlTheory
     payloadCongTheory;
open comms_ffi_modelTheory
     comms_ffi_propsTheory
     comms_ffi_eqTheory
     comms_ffi_rec_characTheory
     comms_ffi_consTheory;
open evaluate_toolsTheory
     ckExp_EquivTheory;
open evaluate_rwLib
     state_tacticLib;
open evaluateTheory terminationTheory ml_translatorTheory
     ml_progTheory evaluatePropsTheory namespaceTheory
     semanticPrimitivesTheory ffiTheory;

val _ = new_theory "payload_to_cakemlProof";

val _ = set_grammar_ancestry
  ["option","rich_list","endpoint_to_payload",
   "payloadCong","payloadLang","payloadSem","payloadProps",
   "payload_to_cakeml","comms_ffi_model","comms_ffi_props",
   "comms_ffi_eq","comms_ffi_rec_charac","comms_ffi_cons",
   "evaluate_tools", "ckExp_Equiv","evaluate", "termination",
   "ml_translator", "ml_prog", "evaluateProps", "namespace",
   "semanticPrimitives","ffi"];

val WORD8 = “WORD:word8 -> v -> bool”;
val DATUM = “LIST_TYPE ^WORD8”;

(* ENVIRONMENT CHECK
    General check environment has something defined with property *)
Definition has_v_def:
  has_v env n cfty f =
   (∃v. nsLookup env n = SOME v
        ∧ cfty f v)
End

(* name is defined such that it cannot be easily overwritten *)
Definition in_module_def:
  in_module name =
  ∀x y (env:(modN,varN,v) namespace). nsLookup (nsBind x y env) name = nsLookup env name
End

(* All constructors in conf are defined correctly and cannot be
   overwritten easily *)
Definition env_asm_def:
  env_asm env conf = (
    has_v env.c conf.nil  $= (0,TypeStamp "[]" list_type_num) ∧
    has_v env.c conf.cons $= (2,TypeStamp "::" list_type_num) ∧
    has_v env.v conf.append (^DATUM --> ^DATUM --> ^DATUM) $++ ∧
    has_v env.v conf.append (LIST_TYPE (^DATUM) --> LIST_TYPE (^DATUM) --> LIST_TYPE (^DATUM)) $++ ∧
    has_v env.v conf.concat (LIST_TYPE (^DATUM) --> ^DATUM) FLAT ∧
    has_v env.v conf.length (^DATUM --> NUM) LENGTH ∧
    has_v env.v conf.null (^DATUM --> BOOL) NULL ∧
    has_v env.v conf.take (^DATUM --> NUM --> ^DATUM) (combin$C TAKE) ∧
    has_v env.v conf.drop (^DATUM --> NUM --> ^DATUM) (combin$C DROP) ∧
    (∃v. nsLookup env.v conf.toList = SOME v ∧
         (∀s1:unit semanticPrimitives$state l ll.
           store_lookup ll s1.refs = SOME (W8array l)
            ⇒ ∃env' exp ck1 ck2 lv.
              do_opapp [v; Loc ll] = SOME(env',exp)           ∧
              evaluate (s1 with clock := ck1) env' [exp] =
                (s1 with <|clock := ck2|>,Rval [lv])      ∧
              ^DATUM l lv)) ∧
    (∃v. nsLookup env.v conf.fromList = SOME v ∧
         (∀l lv.
           ^DATUM l lv
           ⇒ ∀s1: unit semanticPrimitives$state. ∃env' exp ck1 ck2. do_opapp [v; lv] = SOME(env',exp)
               ∧ evaluate (s1 with clock := ck1) env' [exp] =
                  (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)]))) ∧
    in_module conf.append ∧
    in_module conf.concat ∧
    in_module conf.length ∧
    in_module conf.null ∧
    in_module conf.take ∧
    in_module conf.drop ∧
    in_module conf.fromList ∧
    in_module conf.toList)
End

(* LUPDATE (List Update) HELPER THEOREMS *)
Theorem LUPDATE_REPLICATE:
  ∀n m x y. n < m ⇒
   LUPDATE x n (REPLICATE m y) = REPLICATE n y ++ [x] ++ REPLICATE (m - (n + 1)) y
Proof
  Induct >> Cases >>
  rw[LUPDATE_def] >> simp[ADD1]
QED

Theorem LUPDATE_LUPDATE_c:
  ∀a b i lst rst.
    LUPDATE a i (LUPDATE b i lst) = LUPDATE a i lst
Proof
  Induct_on ‘lst’ >> Cases_on ‘i’ >>
  rw[LUPDATE_def]
QED

Theorem LUPDATE_LUPDATE:
  ∀a b i lst rst.
    LUPDATE a i (LUPDATE b i lst ++ rst) = LUPDATE a i (lst ++ rst)
Proof
  Induct_on ‘lst’ >> Cases_on ‘i’ >>
  rw[LUPDATE_def]
QED

Theorem LUPDATE_SAME':
  n < LENGTH ls ∧ EL n ls = a
  ⇒ LUPDATE a n ls = ls
Proof
  metis_tac[LUPDATE_SAME]
QED

(* FFI MANIPULATION HELPERS *)

(* Produce list of FFI events to send data *)
Definition send_events_def:
  send_events conf dest d =
  MAP (λm. IO_event "send" dest (ZIP (m,m)))(compile_message conf d)
End
(* Update FFI state based on list of FFI events *)
Definition update_state_def:
  (update_state st oracle [] = st) ∧
  (update_state st oracle (IO_event s c b::es) =
   update_state (@st'. oracle s st c (MAP FST b) = Oracle_return st' (MAP SND b))
                oracle es)
End

(* SIMPLICATIONS
   -- Written by me *)
(* -- Unnecessary FFI update *)
Theorem remove_ffi[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with ffi := cSt.ffi) = cSt
Proof
  simp[state_component_equality]
QED
(* -- Unnecessary memory update *)
Theorem remove_refs[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with refs := cSt.refs) = cSt
Proof
  simp[state_component_equality]
QED
(* -- Unnecessary conversion to string then back *)
Theorem undo_encode_decode[simp]:
  ∀MEP:word8 list.
    MAP (λc. n2w (ORD c)) (EXPLODE (MAP (CHR ∘ w2n) MEP)) = MEP
Proof
  rw[] >> Induct_on ‘MEP’ >> rw[MAP,EXPLODE_def] >>
  ‘n2w o ORD o CHR o w2n = I’
    suffices_by metis_tac[o_DEF,I_THM] >>
  simp[n2w_ORD_CHR_w2n]
QED

(* SENDLOOP CORRECTNESS *)
Theorem padv_correct:
 ∀env conf l lv le s1 s2 refs.
  env_asm env conf ∧
  ^DATUM l lv ∧
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [lv])
  ⇒
  ∃ck1 ck2 refs' num.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [padv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [Loc num]) ∧
  store_lookup num (APPEND s1.refs refs') = SOME(W8array(pad conf l))
Proof
  rpt strip_tac >>
  drule_then assume_tac evaluate_add_to_clock >>
  rw eval_sl >>
  Q.REFINE_EXISTS_TAC ‘ck1 + s1.clock’ >>
  simp[padv_def,do_opapp_def,buffer_size_def,payload_size_def] >>
  qabbrev_tac ‘LA1 = App Opapp [Var conf.length; Var (Short "x")]’ >>
  qabbrev_tac ‘LA2 = App Opapp [App Opapp [Var conf.take;
                                           Var (Short "x")];
                                Lit (IntLit (&conf.payload_size))]’ >>
  qabbrev_tac ‘LA3 = App Opapp [Var conf.fromList; LA2]’ >>
  qabbrev_tac ‘LA4 = App Opapp [Var conf.fromList; Var (Short "x")]’ >>
  rw eval_sl >>
  Q.REFINE_EXISTS_TAC ‘ck1 + 1’ >>
  rw (dec_clock_def::eval_sl) >>
  Q.REFINE_EXISTS_TAC ‘ck1 + 1’ >>
  rw (dec_clock_def::eval_sl) >>
  qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
  qmatch_goalsub_abbrev_tac ‘evaluate (stLA1 with clock := _) envLA1 [LA1]’ >>
  ‘ck_equiv_hol envLA1 NUM LA1 (LENGTH l)’
    by (qunabbrev_tac ‘LA1’ >>
        irule ck_equiv_hol_App >>
        qexists_tac ‘^DATUM’ >>
        rw[] >> irule ck_equiv_hol_Var
        >- simp (Abbr ‘envLA1’::eval_sl) >>
        fs[in_module_def,env_asm_def,
           has_v_def] >>
        qunabbrev_tac ‘envLA1’ >>
        rw[]) >>
  qspecl_then [‘envLA1’,‘NUM’,‘LA1’,‘LENGTH l’,‘stLA1’]
              assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  rename1 ‘∀dc. evaluate (stLA1 with clock := bc1_1 + dc) _ _ =
                (stLA1 with <|clock := bc2_1 + dc; refs := stLA1.refs ++ drefs1|>,
                 Rval [cV1])’ >>
  Q.REFINE_EXISTS_TAC ‘ck1 + bc1_1’ >>
  simp[] >>
  qpat_x_assum ‘∀dc. _’ (K ALL_TAC) >>
  Cases_on ‘cV1’ >> fs[NUM_def,INT_def] >>
  rw[] >>
  Cases_on ‘LENGTH l = conf.payload_size’ >>
  fs eval_sl
  >- (qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC) >>
      qunabbrev_tac ‘envLA1’ >>
      reverse (rw eval_sl) >>
      qunabbrev_tac ‘stLA1’ >>
      fs[] >>
      qmatch_goalsub_abbrev_tac ‘EL IE LE’ >>
      ‘EL IE LE = W8array (REPLICATE (conf.payload_size + 1) 0w)’
        by (‘EL IE LE = HD ([W8array (REPLICATE (conf.payload_size + 1) 0w)] ++ drefs1)’
              suffices_by rw[HD] >>
            MAP_EVERY qunabbrev_tac [‘IE’,‘LE’] >>
            qabbrev_tac ‘cl = s1.refs ++ refs’ >>
            ‘LENGTH refs + LENGTH s1.refs = LENGTH cl’
              by (qunabbrev_tac ‘cl’ >> rw[LENGTH_APPEND]) >>
            pop_assum SUBST1_TAC >>
            qmatch_goalsub_abbrev_tac ‘cl ++ rl0 ++ rl1’ >>
            ‘cl ++ rl0 ++ rl1 = cl ++ (rl0 ++ rl1)’
              by rw[APPEND_ASSOC] >>
            pop_assum SUBST1_TAC >>
            qabbrev_tac ‘rN = rl0 ++ rl1’ >>
            ‘¬NULL rN’
              by (MAP_EVERY qunabbrev_tac [‘rl0’,‘rl1’,‘rN’] >>
                  rw[NULL_DEF]) >>
            metis_tac[EL_LENGTH_APPEND]) >>
      rw[] >>
      MAP_EVERY qunabbrev_tac [‘IE’, ‘LE’] >>
      qunabbrev_tac ‘LA3’ >>
      rw [evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stLA2 with clock := _) envLA2 [LA2]’ >>
      ‘ck_equiv_hol envLA2 (^DATUM) LA2 ((combin$C TAKE) l conf.payload_size)’
        by (qunabbrev_tac ‘LA2’ >>
            irule ck_equiv_hol_App >>
            qexists_tac ‘NUM’ >> rw[]
            >- (irule ck_equiv_hol_Lit >> rw trans_sl) >>
            irule ck_equiv_hol_App >>
            qexists_tac ‘^DATUM’ >> rw[] >>
            irule ck_equiv_hol_Var
            >- simp (Abbr ‘envLA2’::eval_sl) >>
            fs[in_module_def,env_asm_def,
               has_v_def] >>
            qunabbrev_tac ‘envLA2’ >>
            rw[]) >>
      qspecl_then [‘envLA2’,‘^DATUM’,‘LA2’,
                   ‘combin$C TAKE l conf.payload_size’,‘stLA2’]
                  assume_tac ck_equiv_hol_apply_alt >>
      rfs[] >>
      rename1 ‘∀dc. evaluate (stLA2 with clock := bc1_2 + dc) _ _ =
                (stLA2 with <|clock := bc2_2 + dc; refs := stLA2.refs ++ drefs2|>,
                 Rval [cV2])’ >>
      Q.REFINE_EXISTS_TAC ‘ck1 + bc1_2’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. _’ (K ALL_TAC) >>
      qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC) >>
      MAP_EVERY qunabbrev_tac [‘stLA2’,‘envLA2’,‘LA2’] >>
      qmatch_goalsub_abbrev_tac ‘nsLookup LENV conf.fromList’ >>
      ‘(∃v. nsLookup LENV conf.fromList = SOME v ∧
         (∀l lv.
           ^DATUM l lv
           ⇒ ∀s1: α semanticPrimitives$state.
              ∃env' exp ck1 ck2.
               do_opapp [v; lv] = SOME(env',exp)
               ∧
                ∀mc.
                  evaluate (s1 with clock := ck1 + mc) env' [exp] =
                  (s1 with <|clock := ck2 + mc; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)])))’
        by (qunabbrev_tac ‘LENV’ >> fs[env_asm_def,in_module_def,evaluate_generalise] >>
            rw[] >> rename1 ‘LIST_TYPE WORD l1 l2’ >>
            qpat_x_assum ‘∀a b. _’ (qspecl_then [‘l1’,‘l2’] assume_tac) >>
            qmatch_goalsub_rename_tac ‘evaluate (sg with clock := _) _ _ = _’ >>
            rfs[] >> pop_assum (qspec_then ‘empty_state with refs := sg.refs’ strip_assume_tac) >>
            fs[] >>
            rename1 ‘evaluate (empty_state with <|clock:= ck1; refs := _ |>) envE [expE]
                     = (empty_state with <|clock := ck2; refs := _|>,_)’ >>
            MAP_EVERY qexists_tac [‘ck1’,‘ck2’] >>
            metis_tac[evaluate_generalise]) >>
      fs[] >>
      rw[dec_clock_def,ADD1] >>
      pop_assum (qspecl_then [‘TAKE conf.payload_size l’,‘cV2’] assume_tac) >>
      rfs[] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stLA3 with clock := _) _ _’ >>
      first_x_assum (qspec_then ‘stLA3’ strip_assume_tac) >>
      fs[] >>
      rename1 ‘∀mc. evaluate (stLA3 with clock := bc1_3 + mc) _ _ =
                    (stLA3 with <|clock := bc2_3 + mc; refs := _|>,
                     _)’ >>
      Q.REFINE_EXISTS_TAC ‘ck1 + bc1_3’ >>
      simp[] >>
      qunabbrev_tac ‘stLA3’ >>
      rw[EL_LENGTH_APPEND,NULL_DEF,HD] >>
      fs[] >>
      qmatch_goalsub_abbrev_tac
        ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB ++ oldLstC)’ >>
      ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB ++ oldLstC)
        = newVal’
        by (‘EL indVal (LUPDATE newVal indVal oldLstA) = newVal’
              suffices_by (rw[] >>
                           qspecl_then [‘indVal’,‘LUPDATE newVal indVal oldLstA’,
                                        ‘oldLstB ++ oldLstC’]
                                       assume_tac EL_APPEND1 >>
                           ‘indVal < LENGTH (LUPDATE newVal indVal oldLstA)’
                            suffices_by (rw[] >> fs[]) >>
                           rw[LENGTH_LUPDATE] >>
                           MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
                           rw[LENGTH_APPEND]) >>
            rw[EL_LUPDATE] >>
            MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
            fs[LENGTH_APPEND]) >>
      rw[] >> qunabbrev_tac ‘newVal’ >> rw[]
      >- intLib.COOPER_TAC >>
      MAP_EVERY qexists_tac [‘0’,‘bc2_1 + bc2_2 + bc2_3 + s2.clock’] >>
      rw[state_component_equality] >>
      MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’,‘oldLstB’,‘oldLstC’] >>
      rw[LUPDATE_APPEND] >>
      qmatch_goalsub_abbrev_tac ‘EL i (a ++ b ++ c ++ rstA ++ rstB ++ rstC)’ >>
      ‘EL i (a ++ b ++ c ++ rstA ++ rstB ++ rstC)
        = HD (c ++ rstA ++ rstB ++ rstC)’
        by (qmatch_goalsub_abbrev_tac ‘HD rL’ >>
            ‘a ++ b ++ c ++ rstA ++ rstB ++ rstC
             = a ++ b ++ rL’
             by (qunabbrev_tac ‘rL’ >>
                 metis_tac[APPEND_ASSOC]) >>
            pop_assum SUBST1_TAC >>
            qabbrev_tac ‘ab = a ++ b’ >>
            ‘i = LENGTH ab’
              suffices_by (rw[] >> irule EL_LENGTH_APPEND >>
                           MAP_EVERY qunabbrev_tac
                                     [‘ab’,‘a’,‘b’,‘rL’,‘c’,‘rstA’,
                                      ‘rstB’,‘rstC’] >>
                           metis_tac[NULL_DEF,NULL_APPEND]) >>
            MAP_EVERY qunabbrev_tac [‘i’,‘ab’] >>
            rw[LENGTH_APPEND]) >>
      rw[Abbr ‘c’,HD,LUPDATE_def,pad_def] >>
      rw[LUPDATE_REPLICATE,TAKE,TAKE_TAKE] >>
      rw[TAKE_LENGTH_TOO_LONG] >>
      irule DROP_LENGTH_TOO_LONG >>
      rw[LENGTH_REPLICATE,LENGTH] >>
      intLib.COOPER_TAC)
  >- (qunabbrev_tac ‘stLA1’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stLA1 with clock := _) envLA1 [LA1]’ >>
      qspecl_then [‘envLA1’,‘NUM’,‘LA1’,‘LENGTH l’,‘stLA1’]
              assume_tac ck_equiv_hol_apply_alt >>
      rfs[] >>
      rename1 ‘∀dc. evaluate (stLA1 with clock := bc1_1a + dc) _ _ =
                    (stLA1 with <|clock := bc2_1a + dc; refs := stLA1.refs ++ drefs1a|>,
                     Rval [cV1a])’ >>
      Q.REFINE_EXISTS_TAC ‘ck1 + bc1_1a’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. _’ (K ALL_TAC) >>
      Cases_on ‘cV1a’ >> fs[NUM_def,INT_def] >>
      rw[] >>
      Cases_on ‘LENGTH l < conf.payload_size’ >>
      fs[] >> rw[] >>
      MAP_EVERY qunabbrev_tac [‘envLA1’,‘stLA1’]
      >- (rw (LUPDATE_def::LUPDATE_REPLICATE::LUPDATE_LUPDATE::eval_sl) >>
          qmatch_goalsub_abbrev_tac ‘EL IE LE’ >>
          ‘EL IE LE = W8array (REPLICATE (conf.payload_size + 1) 0w)’
            by (‘EL IE LE = HD ([W8array (REPLICATE (conf.payload_size + 1) 0w)] ++ drefs1 ++ drefs1a)’
                  suffices_by rw[HD] >>
                MAP_EVERY qunabbrev_tac [‘IE’,‘LE’] >>
                qabbrev_tac ‘cl = s1.refs ++ refs’ >>
                ‘LENGTH refs + LENGTH s1.refs = LENGTH cl’
                  by (qunabbrev_tac ‘cl’ >> rw[LENGTH_APPEND]) >>
                pop_assum SUBST1_TAC >>
                qmatch_goalsub_abbrev_tac ‘cl ++ rl0 ++ rl1 ++ rl2’ >>
                ‘cl ++ rl0 ++ rl1 ++ rl2 = cl ++ (rl0 ++ rl1 ++ rl2)’
                  by rw[APPEND_ASSOC] >>
                pop_assum SUBST1_TAC >>
                qabbrev_tac ‘rN = rl0 ++ rl1 ++ rl2’ >>
                ‘¬NULL rN’
                  by (MAP_EVERY qunabbrev_tac [‘rl0’,‘rl1’,‘rl2’,‘rN’] >>
                      rw[NULL_DEF]) >>
                metis_tac[EL_LENGTH_APPEND]) >>
          rw[] >>
          MAP_EVERY qunabbrev_tac [‘IE’, ‘LE’] >>
          qunabbrev_tac ‘LA4’ >>
          rw [evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘nsLookup LENV conf.fromList’ >>
          ‘(∃v. nsLookup LENV conf.fromList = SOME v ∧
             (∀l lv.
               ^DATUM l lv
               ⇒ ∀s1: α semanticPrimitives$state.
                  ∃env' exp ck1 ck2.
                   do_opapp [v; lv] = SOME(env',exp)
                   ∧
                    ∀mc.
                      evaluate (s1 with clock := ck1 + mc) env' [exp] =
                      (s1 with <|clock := ck2 + mc; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)])))’
            by (qunabbrev_tac ‘LENV’ >> fs[env_asm_def,in_module_def,evaluate_generalise] >>
                rw[] >> rename1 ‘LIST_TYPE WORD l1 l2’ >>
                qpat_x_assum ‘∀a b. _’ (qspecl_then [‘l1’,‘l2’] assume_tac) >>
                qmatch_goalsub_rename_tac ‘evaluate (sg with clock := _) _ _ = _’ >>
                rfs[] >> pop_assum (qspec_then ‘empty_state with refs := sg.refs’ strip_assume_tac) >>
                fs[] >>
                rename1 ‘evaluate (empty_state with <|clock:= ck1; refs := _ |>) envE [expE]
                         = (empty_state with <|clock := ck2; refs := _|>,_)’ >>
                MAP_EVERY qexists_tac [‘ck1’,‘ck2’] >>
                metis_tac[evaluate_generalise]) >>
          fs[] >>
          rw[dec_clock_def,ADD1] >>
          pop_assum (qspecl_then [‘l’,‘lv’] assume_tac) >>
          rfs[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (stLA4 with clock := _) _ _’ >>
          first_x_assum (qspec_then ‘stLA4’ strip_assume_tac) >>
          fs[] >>
          rename1 ‘∀mc. evaluate (stLA4 with clock := bc1_4 + mc) _ _ =
                        (stLA4 with <|clock := bc2_4 + mc; refs := _|>,
                         _)’ >>
          Q.REFINE_EXISTS_TAC ‘ck1 + bc1_4’ >>
          simp[] >>
          qunabbrev_tac ‘stLA4’ >>
          rw[EL_LENGTH_APPEND,NULL_DEF] >>
          rw[LUPDATE_LUPDATE] >>
          qmatch_goalsub_abbrev_tac
            ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB)’ >>
          ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB)
            = newVal’
            by (‘EL indVal (LUPDATE newVal indVal oldLstA) = newVal’
                  suffices_by (rw[] >>
                               qspecl_then [‘indVal’,‘LUPDATE newVal indVal oldLstA’,
                                            ‘oldLstB’]
                                           assume_tac EL_APPEND1 >>
                               ‘indVal < LENGTH (LUPDATE newVal indVal oldLstA)’
                                suffices_by (rw[] >> fs[]) >>
                               rw[LENGTH_LUPDATE] >>
                               MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
                               rw[LENGTH_APPEND]) >>
                rw[EL_LUPDATE] >>
                MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
                fs[LENGTH_APPEND]) >>
          rw[] >> qunabbrev_tac ‘newVal’ >> rw[]
          >- intLib.COOPER_TAC
          >- intLib.COOPER_TAC >>
          MAP_EVERY qunabbrev_tac [‘oldLstA’,‘oldLstB’] >>
          reverse (rw[LENGTH_APPEND])
          >- (qunabbrev_tac ‘indVal’ >>
              intLib.COOPER_TAC) >>
          qunabbrev_tac ‘indVal’ >> rw[EL_LUPDATE] >>
          qmatch_goalsub_abbrev_tac ‘EL a x’ >>
          ‘EL a x = W8array l’
            by (qunabbrev_tac ‘a’ >> qunabbrev_tac ‘x’ >>
                ‘LENGTH drefs1 +
                 (LENGTH drefs1a +
                  (LENGTH refs +
                   (LENGTH s1.refs + 1))) =
                 LENGTH (s1.refs ++ refs ++
                        [W8array (REPLICATE (conf.payload_size + 1) 0w)]
                        ++ drefs1 ++ drefs1a)’
                  suffices_by (disch_then SUBST1_TAC >>
                               metis_tac[APPEND_ASSOC,EL_LENGTH_APPEND,NULL_DEF,HD]) >>
                rw[LENGTH_APPEND]) >>
          reverse (rw[])
          >- (MAP_EVERY qunabbrev_tac [‘a’,‘x’] >>
              fs[LENGTH_APPEND]) >>
          ‘a ≠ LENGTH refs + LENGTH s1.refs’
            by (qunabbrev_tac ‘a’ >> fs[]) >>
          reverse (rw[EL_LUPDATE])
          >- (MAP_EVERY qunabbrev_tac [‘x’,‘a’] >>
              intLib.COOPER_TAC) >>
          qmatch_goalsub_abbrev_tac ‘if (PA ∨ PB) then NONE else _’ >>
          ‘¬(PA ∨ PB)’
            by (rw[] >> MAP_EVERY qunabbrev_tac [‘PA’,‘PB’] >>
                intLib.COOPER_TAC) >>
          rw[] >>
          MAP_EVERY qexists_tac [‘0’,‘bc2_1+bc2_1a+bc2_4+s2.clock’] >>
          rw[Abbr ‘x’,state_component_equality,pad_def] >>
          rw[LUPDATE_LUPDATE_c] >>
          qmatch_goalsub_abbrev_tac ‘LUPDATE uval _ _’ >>
          qexists_tac ‘refs ++ [uval] ++ drefs1 ++ drefs1a ++ [W8array l]’ >>
          rw[LUPDATE_def]
          >- (qunabbrev_tac ‘a’ >>
              rw[LUPDATE_APPEND,LUPDATE_def] >>
              fs[]) >>
          ‘s1.refs ++ refs ++ [uval] ++ drefs1 ++ drefs1a ++ [W8array l]
           = (s1.refs ++ refs) ++ ([uval] ++ drefs1 ++ drefs1a ++ [W8array l])’
            by rw[APPEND_ASSOC] >>
          pop_assum SUBST1_TAC >>
         ‘LENGTH refs + LENGTH s1.refs = LENGTH (s1.refs ++ refs)’
          by rw[LENGTH_APPEND] >>
         pop_assum SUBST1_TAC >>
         qmatch_goalsub_abbrev_tac ‘EL (LENGTH bl) (bl ++ rl) = uvalM’ >>
         ‘¬NULL rl ∧ HD rl = uvalM’
          suffices_by (rw[] >> metis_tac[EL_LENGTH_APPEND]) >>
        qunabbrev_tac ‘rl’ >> rw[NULL_DEF,HD] >>
        MAP_EVERY qunabbrev_tac [‘uval’,‘uvalM’] >>
        rw[LUPDATE_REPLICATE,LUPDATE_def,DROP,TAKE] >>
        rw[integerTheory.INT_ABS_EQ_ID,integerTheory.int_le,
           integerTheory.INT_SUB,integerTheory.INT_ADD] >>
        ‘conf.payload_size - LENGTH l = SUC (conf.payload_size - LENGTH l - 1)’
          by rw[ADD1] >>
        pop_assum SUBST1_TAC >>
        rw[LUPDATE_REPLICATE,LUPDATE_def,DROP,TAKE] >>
        qmatch_goalsub_abbrev_tac ‘DROP dl dt’ >>
        ‘DROP dl dt = []’
          by (irule DROP_LENGTH_TOO_LONG >>
              MAP_EVERY qunabbrev_tac [‘dl’,‘dt’] >>
              rw[LENGTH_REPLICATE,LENGTH_APPEND]) >>
        rw[] >> MAP_EVERY qunabbrev_tac [‘dl’,‘dt’] >>
        rw[TAKE_APPEND,LENGTH_REPLICATE,TAKE_LENGTH_TOO_LONG])
      >- (rw (LUPDATE_def::LUPDATE_REPLICATE::LUPDATE_LUPDATE::eval_sl) >>
          qmatch_goalsub_abbrev_tac ‘EL IE LE’ >>
          ‘EL IE LE = W8array (REPLICATE (conf.payload_size + 1) 0w)’
            by (‘EL IE LE = HD ([W8array (REPLICATE (conf.payload_size + 1) 0w)] ++ drefs1 ++ drefs1a)’
                  suffices_by rw[HD] >>
                MAP_EVERY qunabbrev_tac [‘IE’,‘LE’] >>
                qabbrev_tac ‘cl = s1.refs ++ refs’ >>
                ‘LENGTH refs + LENGTH s1.refs = LENGTH cl’
                  by (qunabbrev_tac ‘cl’ >> rw[LENGTH_APPEND]) >>
                pop_assum SUBST1_TAC >>
                qmatch_goalsub_abbrev_tac ‘cl ++ rl0 ++ rl1 ++ rl2’ >>
                ‘cl ++ rl0 ++ rl1 ++ rl2 = cl ++ (rl0 ++ rl1 ++ rl2)’
                  by rw[APPEND_ASSOC] >>
                pop_assum SUBST1_TAC >>
                qabbrev_tac ‘rN = rl0 ++ rl1 ++ rl2’ >>
                ‘¬NULL rN’
                  by (MAP_EVERY qunabbrev_tac [‘rl0’,‘rl1’,‘rl2’,‘rN’] >>
                      rw[NULL_DEF]) >>
                metis_tac[EL_LENGTH_APPEND]) >>
          rw[] >>
          MAP_EVERY qunabbrev_tac [‘IE’, ‘LE’] >>
          qunabbrev_tac ‘LA3’ >>
          rw [evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (stLA2 with clock := _) envLA2 [LA2]’ >>
          ‘ck_equiv_hol envLA2 (^DATUM) LA2 ((combin$C TAKE) l conf.payload_size)’
            by (qunabbrev_tac ‘LA2’ >>
                irule ck_equiv_hol_App >>
                qexists_tac ‘NUM’ >> rw[]
                >- (irule ck_equiv_hol_Lit >> rw trans_sl) >>
                irule ck_equiv_hol_App >>
                qexists_tac ‘^DATUM’ >> rw[] >>
                irule ck_equiv_hol_Var
                >- simp (Abbr ‘envLA2’::eval_sl) >>
                fs[in_module_def,env_asm_def,
                   has_v_def] >>
                qunabbrev_tac ‘envLA2’ >>
                rw[]) >>
          qspecl_then [‘envLA2’,‘^DATUM’,‘LA2’,
                       ‘combin$C TAKE l conf.payload_size’,‘stLA2’]
                      assume_tac ck_equiv_hol_apply_alt >>
          rfs[] >>
          rename1 ‘∀dc. evaluate (stLA2 with clock := bc1_2 + dc) _ _ =
                    (stLA2 with <|clock := bc2_2 + dc; refs := stLA2.refs ++ drefs2|>,
                     Rval [cV2])’ >>
          Q.REFINE_EXISTS_TAC ‘ck1 + bc1_2’ >>
          simp[] >>
          qpat_x_assum ‘∀dc. _’ (K ALL_TAC) >>
          qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC) >>
          MAP_EVERY qunabbrev_tac [‘stLA2’,‘envLA2’,‘LA2’] >>
          qmatch_goalsub_abbrev_tac ‘nsLookup LENV conf.fromList’ >>
          ‘(∃v. nsLookup LENV conf.fromList = SOME v ∧
             (∀l lv.
               ^DATUM l lv
               ⇒ ∀s1: α semanticPrimitives$state.
                  ∃env' exp ck1 ck2.
                   do_opapp [v; lv] = SOME(env',exp)
                   ∧
                    ∀mc.
                      evaluate (s1 with clock := ck1 + mc) env' [exp] =
                      (s1 with <|clock := ck2 + mc; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)])))’
            by (qunabbrev_tac ‘LENV’ >> fs[env_asm_def,in_module_def,evaluate_generalise] >>
                rw[] >> rename1 ‘LIST_TYPE WORD l1 l2’ >>
                qpat_x_assum ‘∀a b. _’ (qspecl_then [‘l1’,‘l2’] assume_tac) >>
                qmatch_goalsub_rename_tac ‘evaluate (sg with clock := _) _ _ = _’ >>
                rfs[] >> pop_assum (qspec_then ‘empty_state with refs := sg.refs’ strip_assume_tac) >>
                fs[] >>
                rename1 ‘evaluate (empty_state with <|clock:= ck1; refs := _ |>) envE [expE]
                         = (empty_state with <|clock := ck2; refs := _|>,_)’ >>
                MAP_EVERY qexists_tac [‘ck1’,‘ck2’] >>
                metis_tac[evaluate_generalise]) >>
          fs[] >>
          rw[dec_clock_def,ADD1] >>
          pop_assum (qspecl_then [‘TAKE conf.payload_size l’,‘cV2’] assume_tac) >>
          rfs[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (stLA3 with clock := _) _ _’ >>
          first_x_assum (qspec_then ‘stLA3’ strip_assume_tac) >>
          fs[] >>
          rename1 ‘∀mc. evaluate (stLA3 with clock := bc1_3 + mc) _ _ =
                        (stLA3 with <|clock := bc2_3 + mc; refs := _|>,
                         _)’ >>
          Q.REFINE_EXISTS_TAC ‘ck1 + bc1_3’ >>
          simp[] >>
          qunabbrev_tac ‘stLA3’ >>
          rw[EL_LENGTH_APPEND,NULL_DEF,HD] >>
          fs[] >>
          qmatch_goalsub_abbrev_tac
            ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB ++ oldLstC)’ >>
          ‘EL indVal ((LUPDATE newVal indVal oldLstA) ++ oldLstB ++ oldLstC)
            = newVal’
            by (‘EL indVal (LUPDATE newVal indVal oldLstA) = newVal’
                  suffices_by (rw[] >>
                               qspecl_then [‘indVal’,‘LUPDATE newVal indVal oldLstA’,
                                            ‘oldLstB ++ oldLstC’]
                                           assume_tac EL_APPEND1 >>
                               ‘indVal < LENGTH (LUPDATE newVal indVal oldLstA)’
                                suffices_by (rw[] >> fs[]) >>
                               rw[LENGTH_LUPDATE] >>
                               MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
                               rw[LENGTH_APPEND]) >>
                rw[EL_LUPDATE] >>
                MAP_EVERY qunabbrev_tac [‘indVal’,‘oldLstA’] >>
                fs[LENGTH_APPEND]) >>
          rw[] >> qunabbrev_tac ‘newVal’ >> rw[]
          >- intLib.COOPER_TAC >>
          qabbrev_tac ‘oldLstBC = oldLstB ++ oldLstC’ >>
          ‘∀lx. lx ++ oldLstB ++ oldLstC = lx ++ oldLstBC’
            by (qunabbrev_tac ‘oldLstBC’ >> metis_tac[APPEND_ASSOC]) >>
          rw[] >> pop_assum (K ALL_TAC) >>
          rw[LUPDATE_LUPDATE] >>
          MAP_EVERY qexists_tac [‘0’,‘bc2_1 + bc2_1a + bc2_2 + bc2_3 + s2.clock’] >>
          MAP_EVERY qunabbrev_tac [‘oldLstA’,‘oldLstBC’,‘oldLstB’,‘oldLstC’] >>
          rw[state_component_equality] >>
          qmatch_goalsub_abbrev_tac ‘LUPDATE nmbit indVal _’ >>
          qexists_tac ‘refs ++ [nmbit] ++ drefs1 ++ drefs1a ++ drefs2 ++ [W8array (TAKE conf.payload_size l)]’ >>
          MAP_EVERY qunabbrev_tac [‘indVal’,‘nmbit’] >> rw[]
          >- (rw[LUPDATE_APPEND,LUPDATE_def]) >>
          qmatch_goalsub_abbrev_tac ‘s1.refs ++ refs ++ [valI] ++ drefs1 ++ drefs1a ++ drefs2 ++ ojnk’ >>
          ‘s1.refs ++ refs ++ [valI] ++ drefs1 ++ drefs1a ++ drefs2 ++ ojnk
            = s1.refs ++ refs ++ ([valI] ++ drefs1 ++ drefs1a ++ drefs2 ++ ojnk)’
            by rw[APPEND_ASSOC] >>
          pop_assum SUBST1_TAC >>
          ‘LENGTH refs + LENGTH s1.refs = LENGTH (s1.refs ++ refs)’
            by rw[LENGTH_APPEND] >>
          pop_assum SUBST1_TAC >>
          qmatch_goalsub_abbrev_tac ‘EL (LENGTH bl) (bl ++ rl) = uvalM’ >>
          ‘¬NULL rl ∧ HD rl = uvalM’
            suffices_by (rw[] >> metis_tac[EL_LENGTH_APPEND]) >>
          qunabbrev_tac ‘rl’ >> rw[NULL_DEF,HD] >>
          MAP_EVERY qunabbrev_tac [‘valI’,‘uvalM’] >>
          rw[LUPDATE_REPLICATE,LUPDATE_def,DROP,TAKE] >>
          rw[integerTheory.INT_ABS_EQ_ID,integerTheory.int_le,
             integerTheory.INT_SUB,integerTheory.INT_ADD] >>
          rw[TAKE_TAKE,DROP_LENGTH_TOO_LONG,LENGTH_REPLICATE] >>
          rw[pad_def]
        )
      )
QED

Theorem sendloop_correct:
  ∀conf l env env' aexp s stpred dest.
  env_asm env' conf ∧
  conf.payload_size ≠ 0 ∧
  nsLookup env.v (Short "sendloop") = SOME(Recclosure env' (sendloop conf (MAP (CHR o w2n) dest)) "sendloop") ∧
  ck_equiv_hol env (^DATUM) aexp l ∧
  stpred s.ffi.ffi_state ∧
  ffi_accepts_rel stpred (valid_send_call_format conf dest) s.ffi.oracle
  ⇒
  ∃ck1 ck2 refs'.
  evaluate$evaluate (s with clock:= ck1) env [App Opapp [Var (Short "sendloop"); aexp]] =
                    (s with
                       <|clock := ck2; refs := APPEND s.refs refs';
                         ffi:= s.ffi with
                         <|io_events := s.ffi.io_events ++ send_events conf dest l;
                           ffi_state := update_state s.ffi.ffi_state s.ffi.oracle (send_events conf dest l)
                          |>
                        |>, Rval [Conv NONE []])
Proof
  ho_match_mp_tac compile_message_ind>>
  rpt strip_tac >>
  ntac 3 (simp[Once evaluate_def]) >>
  drule_then (qspec_then ‘s’ strip_assume_tac) ck_equiv_hol_apply >>
  Q.REFINE_EXISTS_TAC ‘bc1 + ck1’ >>
  simp[do_opapp_def] >>
  first_x_assum (K ALL_TAC) >>
  ntac 2 (simp[Once sendloop_def]) >>
  simp[find_recfun_def] >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env1’ >>
  ‘env_asm env1 conf’
    by (fs[Abbr ‘env1’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
        rfs[] >> metis_tac [EQ_SYM_EQ]) >>
  drule padv_correct >> disch_then drule >>
  disch_then(qspecl_then [‘Var (Short "x")’,‘s with refs := s.refs ++ drefs’,‘s’,‘[]’] mp_tac) >>
  impl_tac >- simp[evaluate_def,Abbr ‘env1’,semanticPrimitivesTheory.state_component_equality] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack1)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack1’ >>
  dxrule evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  unite_nums "dc" >>
  ntac 4 (simp[Once evaluate_def]) >>
  simp[ml_progTheory.nsLookup_nsBind_compute,namespaceTheory.nsOptBind_def,
       do_app_def,ffiTheory.call_FFI_def] >>
  simp[Once evaluate_def] >>
  qhdtm_assum ‘ffi_accepts_rel’
              (mp_tac o REWRITE_RULE [valid_send_call_format_def,
                                      ffi_accepts_rel_def]) >>
  disch_then drule >> simp[] >>
  disch_then(qspec_then ‘pad conf l’ mp_tac) >>
  impl_keep_tac >- rw[pad_def] >>
  strip_tac >>
  simp[IMPLODE_EXPLODE_I,MAP_MAP_o,o_DEF,
       SIMP_RULE std_ss [o_DEF] n2w_ORD_CHR_w2n] >>
  fs[store_assign_def,store_lookup_def,store_v_same_type_def,
     LUPDATE_SAME'] >>
  simp[payload_size_def] >>
  qabbrev_tac ‘LEN_EXP = App Opapp [Var conf.length; Var (Short "x")]’ >>
  qabbrev_tac ‘DRP_EXP = App Opapp [App Opapp [Var conf.drop; Var (Short "x")]; Lit (IntLit (&conf.payload_size))]’ >>
  rw eval_sl >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env2’ >>
  qmatch_goalsub_abbrev_tac ‘evaluate (s2 with clock := _) _’ >>
  ‘env_asm env2 conf’
    by (fs[Abbr ‘env2’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
        rfs[] >> metis_tac [EQ_SYM_EQ]) >>
  ‘ck_equiv_hol env2 NUM LEN_EXP (LENGTH l)’
    by (qunabbrev_tac ‘LEN_EXP’ >> irule ck_equiv_hol_App >>
        qexists_tac ‘^DATUM’ >> strip_tac
        >- (irule ck_equiv_hol_Var >> qexists_tac ‘cV’ >>
            simp[Abbr ‘env2’,ml_progTheory.nsLookup_nsBind_compute])
        >- (irule ck_equiv_hol_Var >>
           fs[env_asm_def,in_module_def,has_v_def])) >>
  drule_then (qspec_then ‘s2’ strip_assume_tac) ck_equiv_hol_apply >>
  rename [‘∀dc. evaluate (s2 with clock := bc1 + dc) _ _ =
               (s2 with <|clock:= dc + bc2; refs := s2.refs ++ drefsL|>,
                Rval [cVL])’] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
  simp[] >>
  first_x_assum (K ALL_TAC) >>
  fs trans_sl >>
  ntac 2 (first_x_assum (K ALL_TAC)) >>
  qpat_x_assum ‘Abbrev (LEN_EXP = _)’ (K ALL_TAC) >>
  qabbrev_tac ‘SND_EXP = App Opapp [Var (Short "sendloop"); Var (Short "x")]’ >>
  rw eval_sl
  >- (simp[Abbr ‘s2’,state_component_equality] >>
      ‘LENGTH l ≤ conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw[update_state_def,send_events_def] >>
      ‘final (pad conf l)’
        by (rw[final_def,pad_def]) >>
      PURE_ONCE_REWRITE_TAC [compile_message_def] >>
      simp[] >>
      ‘ffi = update_state s.ffi.ffi_state
                          s.ffi.oracle
                          [IO_event "send" dest (ZIP (pad conf l,pad conf l))]’
        suffices_by simp[state_component_equality] >>
      rw[update_state_def,send_events_def])
  >- (first_x_assum (K ALL_TAC) >>
      ‘LENGTH l > conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl) >>
      ‘¬final (pad conf l)’
        by (rw[final_def,pad_def]) >>
      ‘ck_equiv_hol env2 (^DATUM) DRP_EXP (combin$C DROP l conf.payload_size)’
        by (qunabbrev_tac ‘DRP_EXP’ >> irule ck_equiv_hol_App >>
            qexists_tac ‘NUM’ >> strip_tac
            >- (irule ck_equiv_hol_Lit >> rw trans_sl)
            >- (irule ck_equiv_hol_App >> qexists_tac ‘^DATUM’ >> strip_tac
                >- (irule ck_equiv_hol_Var >> qexists_tac ‘cV’ >>
                    simp[Abbr ‘env2’,ml_progTheory.nsLookup_nsBind_compute])
                >- (irule ck_equiv_hol_Var >>
                    fs[env_asm_def,in_module_def,has_v_def]))) >>
      unite_nums "dc" >>
      drule_then (qspec_then
                 ‘s2 with refs := s2.refs ++ drefsL’
              strip_assume_tac) ck_equiv_hol_apply >>
      rpt (qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC)) >>
      fs[] >>
      rename [‘∀dc. evaluate (s2 with <|clock := bc1 + dc; refs := s2.refs ++ drefsL|>) _ _ =
               (s2 with <|clock:= bc2 + dc; refs := s2.refs ++ drefsL ++ drefsD|>,
                Rval [cVD])’] >>
      Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (s3 with clock := _) env3’ >>
      last_x_assum (qspecl_then [‘env3’,‘env'’,‘Var (Short "x")’,‘s3’,‘stpred’,‘dest’] strip_assume_tac) >>
      rfs[] >>
      ‘nsLookup env3.v (Short "sendloop") =
       SOME (Recclosure env' (sendloop conf (MAP (CHR ∘ w2n) dest))
                 "sendloop")’
        by (qunabbrev_tac ‘env3’ >> qunabbrev_tac ‘env2’ >> rw[sendloop_def] >>
            EVAL_TAC >> rw[o_DEF]) >>
      ‘ck_equiv_hol env3 (LIST_TYPE WORD) (Var (Short "x")) (DROP conf.payload_size l)’
        by (irule ck_equiv_hol_Var >> qunabbrev_tac ‘env3’ >> EVAL_TAC >>
            qexists_tac ‘cVD’ >> rw[]) >>
      ‘stpred s3.ffi.ffi_state’
        by (qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> fs[]) >>
      ‘ffi_accepts_rel stpred (valid_send_call_format conf dest) s3.ffi.oracle’
        by (qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> fs[]) >>
      fs[] >>
      ntac 4 (first_x_assum (K ALL_TAC)) >>
      unite_nums "dc" >>
      rename [‘evaluate (s3 with clock := bc1) env3 [SND_EXP] =
                (s3 with <|clock := bc2; refs := s3.refs ++ drefsS; ffi:= _|>,
                 _)’] >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs[] >>
      Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
      simp[state_component_equality,ffi_state_component_equality] >>
      ntac 2 (first_x_assum (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘^DATUM _ _’ (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘env_asm _ _’ (K ALL_TAC)) >>
      qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> rw[]
      >- (rw [Once EQ_SYM_EQ,Once send_events_def,Once compile_message_def] >>
          PURE_ONCE_REWRITE_TAC [update_state_def] >>
          rw[MAP_ZIP] >>
          PURE_ONCE_REWRITE_TAC [send_events_def] >>
          simp[])
      >- (rw [Once EQ_SYM_EQ,Once send_events_def,
              Once compile_message_def,Once send_events_def]))
  >- (‘¬(LENGTH l ≤ conf.payload_size)’
        by (CCONTR_TAC >> fs eval_sl) >>
      ‘LENGTH l ≤ conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl))
QED

(* ---- Past this point this file is entirely my contribution *)

(* RECEIVELOOP CORRECT *)
(* List of IO events to receive a piece of data *)
Definition receive_events_def:
  receive_events conf bufInit src d =
  let
    msgChunks  = compile_message conf d;
    data_pairs = ZIP (bufInit::msgChunks,msgChunks)
  in
    MAP (λ(a,b). IO_event "receive" src (ZIP (a,b))) data_pairs
End

(* HOL Model of CakeML find_one function *)
(* -- Definition of model *)
Definition hfind_one_def:
  hfind_one n l =
    if (LENGTH l ≤ n) then
      LENGTH l
    else
      if (1w = EL n l) then
        n
      else
        hfind_one (SUC n) l
Termination
  WF_REL_TAC ‘measure (λ(n,l). LENGTH l - n)’
End

(* -- Model matches CakeML *)
Theorem find_one_equiv:
  ∀env lnum s1 l n.
    nsLookup     env.v (Short "x") = SOME (Loc lnum) ∧
    store_lookup lnum  s1.refs     = SOME (W8array l) ⇒
    ∃ck1 ck2 drefs_f rv.
      evaluate$evaluate (s1 with clock := ck1) env
                      [Letrec find_one
                        (App Opapp [Var (Short "find_one");
                                    Lit (IntLit &n)])]
      = (s1 with <|clock := ck2; refs := s1.refs ++ drefs_f|>,
         Rval [rv]) ∧
      NUM (hfind_one n l) rv
Proof
  rw[] >>
  completeInduct_on ‘LENGTH l - n’ >>
  rw (find_one_def::(Once find_recfun_def)::eval_sl) >>
  qmatch_goalsub_abbrev_tac ‘App Opapp [Var (Short "find_one"); rec_value]’ >>
  qabbrev_tac ‘rec_call = App Opapp [Var (Short "find_one"); rec_value]’ >>
  qunabbrev_tac ‘rec_value’ >>
  Q.REFINE_EXISTS_TAC ‘SUC ck1’ >> rw (ADD1::dec_clock_def::eval_sl)
  >- (‘LENGTH l ≤ n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::trans_sl) >>
      MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
      rw[])
  >- (‘LENGTH l > n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::(trans_sl@eval_sl)) >> fs[]
      >- (MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >> rw[])
      >- (rpt (qpat_x_assum ‘T’ (K ALL_TAC)) >>
          first_x_assum (qspec_then ‘LENGTH l - (n + 1)’ assume_tac) >>
          rfs[] >>
          first_x_assum (qspecl_then [‘l’,‘n + 1’] assume_tac) >>
          rfs(ADD1::store_lookup_def::trans_sl)  >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2’,‘drefs_f’] >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM _’ >>
          qmatch_asmsub_abbrev_tac ‘evaluate s1m env [irecexp]’ >>
          ‘evaluate s1m envM [rec_call] = evaluate s1m env [irecexp]’
            suffices_by rw[] >>
          qpat_x_assum ‘evaluate s1m env [irecexp] = _’ (K ALL_TAC) >>
          qunabbrev_tac ‘irecexp’ >>
          qunabbrev_tac ‘rec_call’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM IGNORE’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m env [Letrec find_one IGNORE2]’ >>
          rw eval_sl
          >- (EVAL_TAC >>
              qmatch_goalsub_abbrev_tac ‘evaluate s1m envMR [IGNORE2]’ >>
              ‘envM = envMR with v := nsBind "n" (Litv (IntLit (&n))) envMR.v’
                by (qunabbrev_tac ‘envM’ >> qunabbrev_tac ‘envMR’ >> simp[]) >>
              rw[] >>
              qunabbrev_tac ‘IGNORE’ >> qunabbrev_tac ‘IGNORE2’ >>
              PURE_ONCE_REWRITE_TAC [evaluate_def] >>
              simp[] >>
              qabbrev_tac ‘IGNORE = do_opapp’ >>
              rw eval_sl >>
              ‘(((&(n :num)) :int) + 1) = ((&(n + (1 :num))) :int)’
                suffices_by rw[] >>
              intLib.COOPER_TAC)
          >- (‘ALL_DISTINCT (MAP (λ(x,y,z). x) find_one)’
                suffices_by fs[] >>
              EVAL_TAC)))
  >- (Cases_on ‘LENGTH l ≤ n’ >> fs eval_sl)
QED

(* -- Model, and thus CakeML code also, correctly simulates SPLITP  *)
Theorem find_one_correct:
  ∀env lnum s1 h l.
    nsLookup     env.v (Short "x") = SOME (Loc lnum) ∧
    store_lookup lnum  s1.refs     = SOME (W8array (h::l)) ⇒
    ∃ck1 ck2 drefs_f rv.
      evaluate$evaluate (s1 with clock := ck1) env
                      [Letrec find_one
                        (App Opapp [Var (Short "find_one");
                                    Lit (IntLit &1)])]
      = (s1 with <|clock := ck2; refs := s1.refs ++ drefs_f|>,
         Rval [rv]) ∧
      NUM (1 + LENGTH (FST (SPLITP ($=1w) l))) rv
Proof
  rw[] >>
  ‘1 + LENGTH (FST (SPLITP ($=1w) l)) = hfind_one 1 (h::l)’
    suffices_by (rw[] >> metis_tac[find_one_equiv]) >>
  Cases_on ‘LENGTH l = 0’
  >- (Cases_on ‘l’ >> fs[LENGTH_NIL,SPLITP,Once hfind_one_def]) >>
  ‘0 < LENGTH l’
    by simp[] >>
  qpat_x_assum ‘LENGTH l ≠ 0’ (K ALL_TAC) >>
  ‘∀n (l : word8 list). n < LENGTH l ⇒ hfind_one n l = n + LENGTH (FST (SPLITP ($=1w) (DROP n l)))’
    suffices_by (rw[] >> first_x_assum (assume_tac o REWRITE_RULE [Once EQ_SYM_EQ]) >>
                 first_x_assum (qspecl_then [‘1’,‘h::l’] assume_tac)) >>
  rpt (first_x_assum (K ALL_TAC)) >>
  rw[] >>
  Induct_on ‘LENGTH l - n’
  >- rw[Once hfind_one_def,DROP_LENGTH_TOO_LONG,SPLITP,FST]
  >- (rw[Once hfind_one_def] >>
      ‘DROP n l = (EL n l)::(DROP (SUC n) l)’
        by (irule DROP_CONS_EL >> fs[])
      >- rw[Once SPLITP]
      >- (first_x_assum (qspecl_then [‘l’,‘SUC n’] assume_tac) >>
          rfs[] >>
          Cases_on ‘SUC n < LENGTH l’
          >- (fs[] >> rw[Once SPLITP])
          >- (rw[Once SPLITP] >>
              ‘DROP (SUC n) l = []’
                by (irule DROP_LENGTH_TOO_LONG >> fs[]) >>
              fs[SPLITP,FST,LENGTH_NIL] >>
              rw[Once hfind_one_def])))
QED

(* unpadv matches unpad  *)
Theorem unpadv_correct:
 ∀env conf l le lnum s1 s2 refs.
  env_asm env conf ∧
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [Loc lnum]) ∧
  store_lookup lnum (APPEND s1.refs refs) = SOME(W8array l) ∧
  LENGTH l > 0
  ⇒
  ∃ck1 ck2 refs' ulv.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [unpadv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [ulv]) ∧
  ^DATUM (unpad l) ulv
Proof
  rpt strip_tac >>
  rw[unpadv_def,validv_def,finalv_def] >>
  qabbrev_tac ‘FEXP = App Opapp [Var conf.toList; Var (Short "y")]’ >>
  qabbrev_tac ‘BEXP = Letrec find_one (App Opapp [Var (Short "find_one"); Lit (IntLit 1)])’ >>
  ‘∃h t. l = h::t’
    by (Cases_on ‘l’ >> fs[LENGTH]) >>
  rw(unpad_def::eval_sl) >>
  drule_then strip_assume_tac evaluate_add_to_clock >>
  fs[] >> Q.REFINE_EXISTS_TAC ‘ck1 + s1.clock’ >>
  simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
  rw[ADD1,dec_clock_def] >> rw eval_sl >>
  ‘¬((&SUC (LENGTH t) :int) - 1 < 0)’
        by (qmatch_goalsub_abbrev_tac ‘¬(SLT - 1 < 0)’ >>
            ‘1 ≤ SLT’
                suffices_by metis_tac[integerTheory.INT_NOT_LE,
                                      integerTheory.INT_SUB_LE,
                                      integerTheory.INT_LE] >>
            qunabbrev_tac ‘SLT’ >> rw[realTheory.REAL]) >>
  fs (store_lookup_def::terminationTheory.do_eq_def::eval_sl)
  >- (rw eval_sl
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC)
      >- (qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
          ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
            by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
          fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
          ‘Num (ABS (1 + &Num (ABS (&SUC (LENGTH t) − 1)))) = SUC (LENGTH t)’
            by (qmatch_goalsub_abbrev_tac ‘1 + &Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >>
                ‘&Num SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_OF_NUM] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >> rw[]) >>
          rw[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (s2M with clock := _) envM [FEXP]’ >>
          ‘env_asm envM conf’
            by (qunabbrev_tac ‘envM’ >>
                fs[env_asm_def,has_v_def,in_module_def] >>
                rfs[] >>
                metis_tac[EQ_SYM_EQ]) >>
          qunabbrev_tac ‘FEXP’ >>
          rw[evaluate_def] >>
          qunabbrev_tac ‘envM’ >>
          rw[nsLookup_def,nsBind_def,nsLookup_nsBind_compute] >>
          qmatch_asmsub_abbrev_tac ‘env_asm (env with v:= envMv) conf’ >>
          qpat_x_assum ‘env_asm (env with v:= envMv) conf’
                       (assume_tac o REWRITE_RULE [env_asm_def]) >>
          qmatch_asmsub_abbrev_tac ‘_ ∧ has_v _ conf.drop _ _ ∧ toThing ∧ _’ >>
          ‘toThing’
            by (qunabbrev_tac ‘toThing’ >> fs[]) >>
          qunabbrev_tac ‘toThing’ >>
          qpat_x_assum ‘has_v _ _ _ _ ∧ _’
                       (assume_tac o REWRITE_RULE [GSYM env_asm_def]) >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
          rw[ADD1,dec_clock_def] >>
          ‘store_lookup (LENGTH TOG) (empty_state with refs := s2M.refs).refs =
            SOME (W8array t)’
            by (qunabbrev_tac ‘s2M’ >> rw[store_lookup_def] >>
                rw[EL_LENGTH_APPEND] >>
                qmatch_goalsub_abbrev_tac ‘&Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >>
                rw[integerTheory.INT,int_arithTheory.elim_minus_ones] >>
                rw[DROP_REPLICATE]) >>
          first_x_assum (drule_then strip_assume_tac) >>
          rw[] >>
          qunabbrev_tac ‘s2M’ >> qunabbrev_tac ‘TOG’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with <| clock := ck1; refs := _|>)
                                             senv [sexp] =
                                      (empty_state with <| clock := ck2; refs := _ |>,Rval[ulv])’ >>
          fs[] >>
          qmatch_asmsub_abbrev_tac ‘evaluate _ _ _ = (empty_state with <|clock := ck2;
                                                                         refs := s1.refs ++ ex_refs1
                                                                                         ++ ex_refs2
                                                                         |>,
                                                      _)’ >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2 + s2.clock’,‘ex_refs1 ++ ex_refs2’,‘ulv’] >>
          qspecl_then [‘s2 with refs := s1.refs ++ ex_refs1 ++ ex_refs2’,
                       ‘senv’,‘sexp’,‘ck1’,‘ck2’,‘[]’,‘ulv’] strip_assume_tac
                       evaluate_generalise >>
          rfs[])
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC))
  >- (rw eval_sl
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC)
      >- (qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
          ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
            by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
          fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
          ‘Num (ABS (1 + &Num (ABS (&SUC (LENGTH t) − 1)))) = SUC (LENGTH t)’
            by (qmatch_goalsub_abbrev_tac ‘1 + &Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >>
                ‘&Num SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_OF_NUM] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >> rw[]) >>
          rw[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (s2M with clock := _) envM [FEXP]’ >>
          ‘env_asm envM conf’
            by (qunabbrev_tac ‘envM’ >>
                fs[env_asm_def,has_v_def,in_module_def] >>
                rfs[] >>
                metis_tac[EQ_SYM_EQ]) >>
          qunabbrev_tac ‘FEXP’ >>
          rw[evaluate_def] >>
          qunabbrev_tac ‘envM’ >>
          rw[nsLookup_def,nsBind_def,nsLookup_nsBind_compute] >>
          qmatch_asmsub_abbrev_tac ‘env_asm (env with v:= envMv) conf’ >>
          qpat_x_assum ‘env_asm (env with v:= envMv) conf’
                       (assume_tac o REWRITE_RULE [env_asm_def]) >>
          qmatch_asmsub_abbrev_tac ‘_ ∧ has_v _ conf.drop _ _ ∧ toThing ∧ _’ >>
          ‘toThing’
            by (qunabbrev_tac ‘toThing’ >> fs[]) >>
          qunabbrev_tac ‘toThing’ >>
          qpat_x_assum ‘has_v _ _ _ _ ∧ _’
                       (assume_tac o REWRITE_RULE [GSYM env_asm_def]) >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
          rw[ADD1,dec_clock_def] >>
          ‘store_lookup (LENGTH TOG) (empty_state with refs := s2M.refs).refs =
            SOME (W8array t)’
            by (qunabbrev_tac ‘s2M’ >> rw[store_lookup_def] >>
                rw[EL_LENGTH_APPEND] >>
                qmatch_goalsub_abbrev_tac ‘&Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >>
                rw[integerTheory.INT,int_arithTheory.elim_minus_ones] >>
                rw[DROP_REPLICATE]) >>
          first_x_assum (drule_then strip_assume_tac) >>
          rw[] >>
          qunabbrev_tac ‘s2M’ >> qunabbrev_tac ‘TOG’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with <| clock := ck1; refs := _|>)
                                             senv [sexp] =
                                      (empty_state with <| clock := ck2; refs := _ |>,Rval[ulv])’ >>
          fs[] >>
          qmatch_asmsub_abbrev_tac ‘evaluate _ _ _ = (empty_state with <|clock := ck2;
                                                                         refs := s1.refs ++ ex_refs1
                                                                                         ++ ex_refs2
                                                                        |>,
                                                      _)’ >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2 + s2.clock’,‘ex_refs1 ++ ex_refs2’,‘ulv’] >>
          qspecl_then [‘s2 with refs := s1.refs ++ ex_refs1 ++ ex_refs2’,
                       ‘senv’,‘sexp’,‘ck1’,‘ck2’,‘[]’,‘ulv’] strip_assume_tac
                       evaluate_generalise >>
          rfs[])
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC))
  >- (qmatch_goalsub_abbrev_tac ‘evaluate (SE with clock := _) EE’ >>
      qspecl_then [‘EE’,‘lnum’,‘SE’,‘6w’,‘t’] strip_assume_tac find_one_correct >>
      qunabbrev_tac ‘SE’ >> qunabbrev_tac ‘EE’ >> rfs[store_lookup_def] >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs trans_sl >>
      Q.REFINE_EXISTS_TAC ‘ck1 + ck1f’ >>
      simp[] >>
      qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
      ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
        by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
      fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
      rw eval_sl
      >- (fs[env_asm_def,has_v_def] >>
          qunabbrev_tac ‘TOG’ >>
          MAP_EVERY qexists_tac [‘0’,‘ck2+s2.clock’,‘refs ++ drefs_f’] >>
          simp[] >>
          ‘LENGTH (FST (SPLITP ($= 1w) t)) = LENGTH t’
            by (CCONTR_TAC >> fs(ADD1::eval_sl)) >>
          ‘LENGTH (SND (SPLITP ($= 1w) t)) = 0’
            by (‘LENGTH t +
                 LENGTH (SND (SPLITP ($=1w) t)) =
                 LENGTH t’
                  by metis_tac[SPLITP_LENGTH] >>
                fs[]) >>
          Cases_on ‘SPLITP ($= 1w) t’ >> fs (list_type_num_def::trans_sl))
      >- (‘LENGTH (FST (SPLITP ($=1w) t)) + 1 < SUC (LENGTH t)’
            by (‘LENGTH (FST (SPLITP ($=1w) t)) + 1 ≠ SUC (LENGTH t)’
                  by (CCONTR_TAC >> fs eval_sl) >>
                ‘∀ (l:word8 list). LENGTH (FST (SPLITP ($=1w) l)) ≤ LENGTH l’
                  suffices_by (rw[] >> first_x_assum (qspec_then ‘t’ assume_tac) >>
                               fs[ADD1]) >>
                Induct_on ‘l’ >>
                rw[SPLITP]) >>
          rw[EL_LENGTH_APPEND,EL_APPEND_EQN]
          >- (intLib.COOPER_TAC) >>
          simp[integerTheory.INT_OF_NUM,integerTheory.INT_ABS_NUM,
               integerTheory.INT_ADD, integerTheory.INT_SUB,ADD1] >>
          qunabbrev_tac ‘FEXP’ >>
          fs[env_asm_def,in_module_def] >>
          PURE_ONCE_REWRITE_TAC [evaluate_def] >>
          rw eval_sl_nf >>
          qmatch_goalsub_abbrev_tac ‘LUPDATE (W8array l) ll os’ >>
          last_x_assum (qspecl_then [‘empty_state with refs :=
                                        LUPDATE (W8array l) ll os’,
                                     ‘l’,‘ll’] strip_assume_tac) >>
          rpt (qpat_x_assum ‘has_v _ _ _ _’ (K ALL_TAC)) >>
          rpt (qpat_x_assum ‘∀a. _’ (K ALL_TAC)) >>
          rpt (qpat_x_assum ‘nsLookup _ _ = _’ (K ALL_TAC)) >>
          qunabbrev_tac ‘ll’ >> qunabbrev_tac ‘os’ >>
          rfs[store_lookup_def,EL_LENGTH_APPEND,EL_APPEND_EQN,
              EL_LUPDATE] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1f’ >>
          rw[ADD1,dec_clock_def] >>
          qmatch_goalsub_abbrev_tac
            ‘evaluate (s2c with clock := _) envE [expE] = (_,_)’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with
                                                <| clock := Ack1;
                                                   refs := _|>)
                                              _ _ =
                                              (empty_state with
                                                <| clock := Ack2;
                                                   refs := _|>,
                                              Rval[vE])’ >>
          qspecl_then [‘s2c’,‘envE’,‘expE’,‘Ack1’,‘Ack2’,‘[]’,‘vE’]
                      strip_assume_tac evaluate_generalise >>
          qunabbrev_tac ‘s2c’ >> rfs[] >>
          Q.REFINE_EXISTS_TAC ‘Ack1 + ck1f’ >>
          simp[] >>
          qunabbrev_tac ‘TOG’ >>
          MAP_EVERY qexists_tac [‘0’,‘Ack2 + ck2 + s2.clock’,
                                 ‘refs ++ drefs_f ++ [W8array l]’] >>
          qmatch_goalsub_abbrev_tac ‘s2 with <| clock := _; refs := r1 |> =
                                     s2 with <| clock := _; refs := r2 |>’ >>
          rw[state_component_equality]
          >- (qunabbrev_tac ‘r1’ >> qunabbrev_tac ‘r2’ >>
              rpt (first_x_assum (K ALL_TAC)) >>
              qabbrev_tac ‘rj = s1.refs ++ refs ++ drefs_f’ >>
              ‘LENGTH (s1.refs ++ refs) + LENGTH drefs_f = LENGTH rj’
                by (qunabbrev_tac ‘rj’ >> simp[LENGTH_APPEND]) >>
              rw[])
          >- (qmatch_goalsub_abbrev_tac ‘LIST_TYPE WORD ol vE’ >>
              ‘ol = l’
                suffices_by rw[] >>
              qunabbrev_tac ‘ol’ >> qunabbrev_tac ‘l’ >>
              rpt (first_x_assum (K ALL_TAC)) >>
              rw[DROP_LENGTH_TOO_LONG,LENGTH_REPLICATE] >>
              Induct_on ‘t’ >> simp [SPLITP] >>
              rw[] >> Cases_on ‘1w = h’ >> simp[] >> fs[ADD1] >>
              Cases_on ‘SPLITP ($= 1w) t’ >> fs[]))
      >- (Cases_on ‘LENGTH (FST (SPLITP ($= 1w) t)) + 1 = SUC (LENGTH t)’ >>
          fs trans_sl))
  >- (fs[env_asm_def,has_v_def] >>
      MAP_EVERY qexists_tac [‘0’,‘s2.clock’,‘refs’] >>
      rw (list_type_num_def::trans_sl))
QED

(* Main receiveloop characterisation *)

Theorem receiveloop_correct:
  ∀conf l env env' s src bufLoc bufInit.
    (* We have a sensible environment for execution at all *)
    env_asm env' conf ∧
    conf.payload_size ≠ 0 ∧
    (* Receive loop function and storage buffer properly initialised *)
    nsLookup env.v (Short "receiveloop") = SOME(Recclosure env' (receiveloop conf (MAP (CHR o w2n) src)) "receiveloop") ∧
    nsLookup env'.v (Short "buff") = SOME(Loc bufLoc) ∧
    store_lookup bufLoc s.refs = SOME(W8array bufInit) ∧
    LENGTH bufInit = SUC conf.payload_size ∧
    (* Our ffi is in the right state to receive a message *)
    ffi_receives conf s.ffi src l
    ⇒
    ∃ck1 ck2 bufFinl refs' ulv.
    evaluate$evaluate (s with clock:= ck1) env [App Opapp [Var (Short "receiveloop"); Con NONE []]] =
                      (s with
                         <|clock := ck2; refs := APPEND (LUPDATE bufFinl bufLoc s.refs) refs';
                           ffi:= s.ffi with
                           <|io_events := s.ffi.io_events ++ receive_events conf bufInit src l;
                             ffi_state := update_state s.ffi.ffi_state s.ffi.oracle (receive_events conf bufInit src l)
                            |>
                          |>, Rval [ulv]) ∧
    LIST_TYPE (^DATUM) (MAP unpad (compile_message conf l)) ulv
Proof
  ntac 2 gen_tac >>
  completeInduct_on ‘LENGTH l’ >>
  rw [receiveloop_def] >>
  qabbrev_tac ‘NESTREC = App Opapp [Var(Short "receiveloop");Var(Short "u")]’ >>
  qabbrev_tac ‘NOEVAL = App Opapp [unpadv conf; Var (Short "buff")]’ >>
  rw eval_sl_nffi >>
  fs[store_lookup_def] >>
  PURE_ONCE_REWRITE_TAC [find_recfun_def] >>
  rw eval_sl_nffi >>
  Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
  rw[dec_clock_def,ADD1] >>
  simp[IMPLODE_EXPLODE_I,MAP_MAP_o,o_DEF,
     SIMP_RULE std_ss [o_DEF] n2w_ORD_CHR_w2n] >>
  qpat_x_assum ‘ffi_receives _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [ffi_receives_def]) >>
  rfs[] >>
  first_x_assum (qspecl_then [‘"receive"’,‘src’,‘bufInit’] assume_tac) >>
  ‘valid_receive_call_format conf src "receive" src bufInit’
    by rw[valid_receive_call_format_def] >>
  reverse (fs[final_def,intermediate_def]) >>
  rfs[] >>
  rw (finalv_def::eval_sl)
  (* Final Message *)
  >- (rw (EL_LUPDATE::eval_sl) >>
      Cases_on ‘pad conf l’ >> fs[final_def] >>
      rw (EL_LUPDATE::eval_sl) >>
      qpat_assum ‘env_asm _ _’ (assume_tac o (el 1) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
      qpat_assum ‘env_asm _ _’ (assume_tac o (el 2) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
      fs[has_v_def] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (sUn with clock := _) envUn [NOEVAL]’ >>
      qunabbrev_tac ‘NOEVAL’
      (* Message takes whole space *)
      >- (qspecl_then [‘envUn’,‘conf’,‘7w::t’,‘Var (Short "buff")’,‘bufLoc’,
                       ‘sUn’,‘sUn’,‘[]’] assume_tac unpadv_correct >>
          ‘env_asm envUn conf’
            by (fs[Abbr ‘envUn’,env_asm_def,has_v_def,in_module_def] >>
                rfs[] >> metis_tac[EQ_SYM_EQ]) >>
          ‘evaluate sUn envUn [Var (Short "buff")] =
            (sUn with refs := sUn.refs ++ [], Rval[Loc bufLoc])’
            by fs (Abbr ‘envUn’::eval_sl) >>
          ‘store_lookup bufLoc (sUn.refs ++ []) = SOME (W8array (7w::t))’
            by rw (Abbr ‘sUn’::EL_LUPDATE::eval_sl) >>
          ‘LENGTH (7w::t) > 0’
            by rw[] >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘sUn.clock + ck1’ >>
          qpat_x_assum ‘evaluate _ _ [App Opapp _] = _’ assume_tac >>
          dxrule_then assume_tac evaluate_add_to_clock >>
          fs[store_lookup_def] >>
          rw (EL_LUPDATE::eval_sl) >>
          qunabbrev_tac ‘sUn’ >>
          rw (EL_APPEND_EQN::LENGTH_LUPDATE::EL_LUPDATE::eval_sl) >>
          rename1 ‘(s with <| refs := _; ffi := _|>).refs ++ drefs’ >>
          MAP_EVERY qexists_tac [‘ck2 + s.clock’,‘W8array (7w::t)’,‘drefs’] >>
          rw[state_component_equality] >>
          fs[call_FFI_def,receive_events_def,update_state_def,
                 unpad_def] >>
          Cases_on ‘s.ffi.oracle "receive" s.ffi.ffi_state src bufInit’ >>
          fs[] >>
          rename1 ‘LENGTH rl = LENGTH bufInit’ >>
          Cases_on ‘LENGTH rl = LENGTH bufInit’ >>
          fs[] >>
          rfs[LENGTH] >>
          ‘compile_message conf l = [pad conf t]’
                by (rw[Once compile_message_def] >>
                    rfs[final_def,pad_def])
          >- (qpat_x_assum ‘_ = nst’ (SUBST1_TAC o GSYM) >>
              rw[ffi_state_component_equality] >>
              EVAL_TAC >> rw[Once ZIP_def] >>
              rw[Once update_state_def] >>
              ‘MAP FST (ZIP (bufInit,7w::t)) = bufInit’
                by metis_tac[MAP_ZIP,LENGTH] >>
              rw[] >> SELECT_ELIM_TAC >> rw[] >>
              metis_tac[MAP_ZIP,LENGTH])
          >- (rw[unpad_def] >>
              Cases_on ‘t’ >> rw[pad_def,unpad_def]
              >- fs[LENGTH] >>
              rw[Once LIST_TYPE_def,list_type_num_def] >>
              rw[Once LIST_TYPE_def]))
      (* Message takes some of the space *)
      >- (qspecl_then [‘envUn’,‘conf’,‘6w::t’,‘Var (Short "buff")’,‘bufLoc’,
                       ‘sUn’,‘sUn’,‘[]’] assume_tac unpadv_correct >>
          ‘env_asm envUn conf’
            by (fs[Abbr ‘envUn’,env_asm_def,has_v_def,in_module_def] >>
                rfs [] >> metis_tac[EQ_SYM_EQ]) >>
          ‘evaluate sUn envUn [Var (Short "buff")] =
            (sUn with refs := sUn.refs ++ [], Rval[Loc bufLoc])’
            by fs (Abbr ‘envUn’::eval_sl) >>
          ‘store_lookup bufLoc (sUn.refs ++ []) = SOME (W8array (6w::t))’
            by rw (Abbr ‘sUn’::EL_LUPDATE::eval_sl) >>
          ‘LENGTH (6w::t) > 0’
            by rw[] >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘sUn.clock + ck1’ >>
          qpat_x_assum ‘evaluate _ _ [App Opapp _] = _’ assume_tac >>
          dxrule_then assume_tac evaluate_add_to_clock >>
          fs[store_lookup_def] >>
          rw (EL_LUPDATE::eval_sl) >>
          qunabbrev_tac ‘sUn’ >>
          rw (EL_APPEND_EQN::LENGTH_LUPDATE::EL_LUPDATE::eval_sl) >>
          rename1 ‘(s with <| refs := _; ffi := _|>).refs ++ drefs’ >>
          MAP_EVERY qexists_tac [‘ck2 + s.clock’,‘W8array (6w::t)’,‘drefs’] >>
          rw[state_component_equality] >>
          fs[call_FFI_def,receive_events_def,update_state_def] >>
          Cases_on ‘s.ffi.oracle "receive" s.ffi.ffi_state src bufInit’ >>
          fs[] >>
          rename1 ‘LENGTH rl = LENGTH bufInit’ >>
          Cases_on ‘LENGTH rl = LENGTH bufInit’ >>
          fs[] >>
          rfs[LENGTH] >>
          ‘compile_message conf l = [pad conf l]’
                by (rw[Once compile_message_def] >>
                    rfs[final_def,pad_def]) >>
          rw[ZIP_def,ffi_state_component_equality]
          >- (rw[update_state_def] >>
              ‘(MAP FST (ZIP (bufInit,6w::t)) = bufInit) ∧
               (MAP SND (ZIP (bufInit,6w::t)) = 6w::t)’
                by (‘∀x. LENGTH (pad conf x) = SUC conf.payload_size’
                      suffices_by (rw[] >> metis_tac[MAP_ZIP,LENGTH]) >>
                    rw[pad_def]) >>
              rw[] >> SELECT_ELIM_TAC >> rw[])
          >- (rw[Once LIST_TYPE_def,list_type_num_def] >>
              rw[Once LIST_TYPE_def])))
  (* Intermediate Message *)
  >- (rw (EL_LUPDATE::eval_sl) >>
      Cases_on ‘pad conf l’ >> fs[intermediate_def] >>
      rw (EL_LUPDATE::eval_sl) >>
      qpat_assum ‘env_asm _ _’ (assume_tac o (el 1) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
      qpat_assum ‘env_asm _ _’ (assume_tac o (el 2) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
      fs[has_v_def] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (sUn with clock := _) envUn [NOEVAL]’ >>
      qunabbrev_tac ‘NOEVAL’ >>
      qspecl_then [‘envUn’,‘conf’,‘2w::t’,‘Var (Short "buff")’,‘bufLoc’,
                       ‘sUn’,‘sUn’,‘[]’] assume_tac unpadv_correct >>
      ‘env_asm envUn conf’
        by (fs[Abbr ‘envUn’,env_asm_def,has_v_def,in_module_def] >>
            rfs[] >> metis_tac[EQ_SYM_EQ]) >>
      ‘evaluate sUn envUn [Var (Short "buff")] =
        (sUn with refs := sUn.refs ++ [], Rval[Loc bufLoc])’
        by fs (Abbr ‘envUn’::eval_sl) >>
      ‘store_lookup bufLoc (sUn.refs ++ []) = SOME (W8array (2w::t))’
        by rw (Abbr ‘sUn’::EL_LUPDATE::eval_sl) >>
      ‘LENGTH (2w::t) > 0’
        by rw[] >>
      fs[] >>
      qpat_x_assum ‘evaluate _ _ [App Opapp _] = _’ assume_tac >>
      dxrule_then assume_tac evaluate_add_to_clock >>
      Q.REFINE_EXISTS_TAC ‘ck1 + ck1e’ >>
      fs[store_lookup_def] >>
      rw (EL_LUPDATE::eval_sl) >>
      qunabbrev_tac ‘sUn’ >>
      rw (EL_APPEND_EQN::LENGTH_LUPDATE::EL_LUPDATE::eval_sl) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (sRn with clock := _) envRn [NESTREC]’ >>
      qunabbrev_tac ‘NESTREC’ >>
      last_x_assum (qspec_then ‘LENGTH (DROP conf.payload_size l)’ assume_tac) >>
      fs[LENGTH_DROP] >> rfs[] >>
      first_x_assum (qspec_then ‘DROP conf.payload_size l’ assume_tac) >>
      fs[LENGTH_DROP] >> rfs[] >>
      first_x_assum (qspecl_then [‘envRn’,‘env'’,‘sRn’,‘src’,
                                  ‘bufLoc’,‘2w::t’]
                                 assume_tac) >>
      rfs[] >>
      ‘nsLookup envRn.v (Short "receiveloop") =
       SOME
         (Recclosure env' (receiveloop conf (MAP (CHR ∘ w2n) src))
            "receiveloop") ∧
       (bufLoc < LENGTH sRn.refs ∧ EL bufLoc sRn.refs = W8array (2w::t)) ∧
       LENGTH t = conf.payload_size ∧
       ffi_receives conf sRn.ffi src (DROP conf.payload_size l)’
        by (MAP_EVERY qunabbrev_tac [‘sRn’, ‘envRn’] >>
            fs[EL_LUPDATE,receiveloop_def,o_DEF,finalv_def] >>
            rw[EL_APPEND_EQN,LENGTH_LUPDATE,EL_LUPDATE] >>
            ‘∀x. LENGTH (pad conf x) = SUC conf.payload_size’
              suffices_by (disch_then (qspec_then ‘l’ mp_tac) >>
                           fs[]) >>
            rw[pad_def]) >>
      fs[] >> ntac 5 (pop_assum (K ALL_TAC)) >>
      dxrule_then assume_tac evaluate_add_to_clock >>
      fs[] >> pop_assum (assume_tac o REWRITE_RULE eval_sl) >>
      fs[] >> pop_assum (assume_tac o REWRITE_RULE eval_sl) >>
      fs[] >> rw eval_sl >>
      ‘nsLookup envRn.v (Short "u") = SOME (Conv NONE [])’
        by (qunabbrev_tac ‘envRn’ >> rw eval_sl) >>
      rw eval_sl >>
      qmatch_asmsub_rename_tac ‘sRn with clock := ack1 + _’ >>
      qmatch_asmsub_rename_tac ‘Rval [aulv]’ >>
      Q.REFINE_EXISTS_TAC ‘ack1 + ck1e’ >>
      simp[] >>
      ntac 2 (pop_assum (K ALL_TAC)) >>
      MAP_EVERY qunabbrev_tac [‘sRn’,‘envRn’] >>
      qmatch_goalsub_rename_tac ‘s with <| clock := _ + (FC1 + FC2);
                                           refs := LUPDATE _ _ _ ++ drefs2; ffi := _;
                                           refs := LUPDATE _ _ _ ++ drefs ; ffi := _|>’ >>
      MAP_EVERY qexists_tac [‘0’,‘FC1 + FC2’,‘bufFinl’,‘drefs ++ drefs2’] >>
      fs[call_FFI_def,receive_events_def,update_state_def] >>
      Cases_on ‘s.ffi.oracle "receive" s.ffi.ffi_state src bufInit’ >>
      fs[] >>
      rename1 ‘LENGTH rl = LENGTH bufInit’ >>
      Cases_on ‘LENGTH rl = LENGTH bufInit’ >>
      fs[] >>
      rfs[LENGTH] >>
      rw[state_component_equality] >>
      ‘compile_message conf l = (2w::t)::compile_message conf (DROP conf.payload_size l)’
        by (rw[Once compile_message_def] >>
            fs[final_def])
      >- (rw[LUPDATE_LUPDATE,LUPDATE_APPEND,LENGTH_LUPDATE,
             LENGTH_APPEND])
      >- (rw[ffi_state_component_equality,update_state_def] >>
          qmatch_goalsub_abbrev_tac ‘update_state lSt _ _ = update_state rSt _ _’ >>
          ‘lSt = rSt’ suffices_by rw[] >>
          MAP_EVERY qunabbrev_tac [‘lSt’,‘rSt’] >>
          ‘(MAP FST (ZIP (bufInit,2w::t)) = bufInit) ∧
           (MAP SND (ZIP (bufInit,2w::t)) = 2w::t)’
            by (‘∀x. LENGTH (pad conf x) = SUC conf.payload_size’
                  suffices_by (rw[] >> metis_tac[MAP_ZIP,LENGTH]) >>
                rw[pad_def]) >>
          rw[] >> SELECT_ELIM_TAC >> rw[])
      >- rw[LIST_TYPE_def,list_type_num_def])
QED

Theorem receiveloop_pres_ffi_eq:
  ∀conf env env' s1 s2 src bufLoc bufInit.
    (* We have a sensible environment for execution at all *)
    env_asm env' conf ∧
    conf.payload_size ≠ 0 ∧
    (* Receive loop function and storage buffer properly initialised *)
    nsLookup env.v (Short "receiveloop") = SOME(Recclosure env' (receiveloop conf (MAP (CHR o w2n) src)) "receiveloop") ∧
    nsLookup env'.v (Short "buff") = SOME(Loc bufLoc) ∧
    store_lookup bufLoc s1.refs = SOME(W8array bufInit) ∧
    store_lookup bufLoc s2.refs = SOME(W8array bufInit) ∧
    LENGTH bufInit = SUC conf.payload_size ∧
    (* Our ffi is in the right state to receive the same message *)
    ffi_eq conf s1.ffi.ffi_state s2.ffi.ffi_state
    ⇒
    ∃ckA1 ckB1 ckA2 ckB2 refsB1 refsB2 ffiB1 ffiB2 r1 r2.
    evaluate$evaluate (s1 with clock:= ckA1) env [App Opapp [Var (Short "receiveloop"); Con NONE []]] =
                      (s1 with <|clock := ckB1; refs := refsB1; ffi:= ffiB1|>,
                      r1) ∧
    evaluate$evaluate (s2 with clock:= ckA2) env [App Opapp [Var (Short "receiveloop"); Con NONE []]] =
                      (s2 with <|clock := ckB2; refs := refsB2; ffi:= ffiB2|>,
                      r2) ∧
    ffi_eq conf ffiB1.ffi_state ffiB2.ffi_state ∧
    (r1 = r2)
Proof
  cheat
QED

(* HOL HELPERS CORRECT *)
Theorem w1ckV_is_1w:
  ∀env conf.
    env_asm env conf ⇒
    ck_equiv_hol env (^DATUM) (w1ckV conf) [1w]
Proof
  rw[ck_equiv_hol_def,w1ckV_def] >>
  rw eval_sl >>
  fs[env_asm_def,has_v_def] >>
  rw trans_sl >>
  simp[list_type_num_def] >>
  MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
  simp[state_component_equality]
QED

Theorem convList_corr:
  ∀env conf cvs hvs.
    env_asm env conf  ∧
    (LENGTH cvs = LENGTH hvs) ∧
    EVERY (λ(c,h). ck_equiv_hol env (^DATUM) c h) (ZIP (cvs,hvs))
    ⇒
    ck_equiv_hol env (LIST_TYPE ^DATUM) (convList conf cvs) hvs
Proof
  Induct_on ‘cvs’
  >- (rw (convList_def::ck_equiv_hol_def::eval_sl) >>
      fs[env_asm_def,has_v_def] >> rw (list_type_num_def::trans_sl) >>
      MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >> simp[])
  >- (rpt strip_tac >> rw (convList_def::ck_equiv_hol_def::eval_sl) >>
      Cases_on ‘hvs’ >> fs[] >>
      rename1 ‘LENGTH cvs = LENGTH hvs’ >>
      qmatch_goalsub_rename_tac ‘LIST_TYPE _ (hv::hvs) _’ >>
      first_x_assum (qspecl_then [‘env’,‘conf’,‘hvs’] strip_assume_tac) >>
      rfs[] >> qmatch_goalsub_abbrev_tac ‘evaluate (cls with clock := _) _ _’ >>
      drule_then (qspec_then ‘cls’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1
      ‘∀dc.
        evaluate (cls with clock := bc1_l + dc) env [convList conf cvs] =
        (cls with <|clock := dc + bc2_l; refs := cls.refs ++ drefs_l|>,
         Rval [cV])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_l + bc1’ >>
      simp[] >> fs[env_asm_def,has_v_def] >>
      first_x_assum (K ALL_TAC) >> qunabbrev_tac ‘cls’ >> simp[] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cls with clock := _) _ _’ >>
      qpat_x_assum ‘ck_equiv_hol _ _ (convList _ _) _’ (K ALL_TAC) >>
      drule_then (qspec_then ‘cls’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1
      ‘∀dc.
        evaluate (cls with clock := abc1_h + dc) env [h] =
        (cls with <|clock := dc + abc2_h; refs := cls.refs ++ drefs_h|>,
         Rval [cV_h])’ >>
      Q.REFINE_EXISTS_TAC ‘abc1_h + bc1’ >>
      simp[] >> rw (list_type_num_def::trans_sl) >>
      qunabbrev_tac ‘cls’ >> simp[] >>
      MAP_EVERY qexists_tac [‘0’,‘abc2_h+bc2_l’,‘drefs_l ++ drefs_h’] >> simp[])
QED

Theorem convDatum_corr:
  ∀env conf hv.
    env_asm env conf ⇒
    ck_equiv_hol env ^DATUM (convDatum conf hv) hv
Proof
  Induct_on ‘hv’ >>
  rw (convDatum_def::ck_equiv_hol_def::eval_sl) >>
  qpat_assum ‘env_asm _ _’ (assume_tac o (el 1) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
  qpat_assum ‘env_asm _ _’ (assume_tac o (el 2) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
  fs[has_v_def] >>
  rw (list_type_num_def::trans_sl)
  >- (MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >> rw[]) >>
  last_x_assum (drule_all_then assume_tac) >>
  qspecl_then [‘env’,‘^DATUM’,‘convDatum conf hv’,‘hv’,‘empty_state with refs := arefs’]
              assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  first_x_assum (qspec_then ‘0’ assume_tac) >>
  qexists_tac ‘bc1’ >>
  fs[] >>
  MAP_EVERY qexists_tac [‘bc2’,‘drefs’] >>
  rw[]
QED

Theorem convDatumList_corr:
  ∀env conf hvs.
    env_asm env conf ⇒
    ck_equiv_hol env (LIST_TYPE ^DATUM) (convDatumList conf hvs) hvs
Proof
  Induct_on ‘hvs’ >> rw[] >>
  qpat_assum ‘env_asm _ _’ (assume_tac o (el 1) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
  qpat_assum ‘env_asm _ _’ (assume_tac o (el 2) o (CONJUNCTS o REWRITE_RULE [env_asm_def])) >>
  rw (convDatumList_def::ck_equiv_hol_def::eval_sl) >>
  fs (has_v_def::list_type_num_def::trans_sl)
  >- metis_tac[APPEND_NIL] >>
  last_x_assum (drule_all_then assume_tac) >>
  qspecl_then [‘env’,‘LIST_TYPE ^DATUM’,‘convDatumList conf hvs’,‘hvs’,‘empty_state with refs := arefs’]
              assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + bc1e’ >>
  simp[] >>
  drule_all_then assume_tac convDatum_corr >>
  pop_assum (qspec_then ‘h’ assume_tac) >>
  qspecl_then [‘env’,‘^DATUM’,‘convDatum conf h’,‘h’,‘empty_state with refs := arefs ++ drefs’]
              assume_tac ck_equiv_hol_apply_alt >>
  rfs[] >>
  qmatch_asmsub_rename_tac
    ‘∀dc.
       evaluate
       (empty_state with <|clock := abc1 + dc; refs := arefs ++ drefs|>) env
       [convDatum conf h] =
       (empty_state with <|clock := abc2 + dc; refs := arefs ++ drefs ++ drefs2 |>,
        Rval [cV2])’ >>
  Q.REFINE_EXISTS_TAC ‘abc1 + bc1e’ >>
  simp[] >>
  MAP_EVERY qexists_tac [‘0’,‘abc2 + bc2’,‘drefs ++ drefs2’] >>
  rw[]
QED

(* CORRESPONDENCE RESTRICTIONS *)
(* Payload State and Code Coherence *)
(* -- Check the payload code and state make sense wrt. free variables *)
Definition pFv_def[simp]:
  pFv Nil = {} ∧
  pFv (Send _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (Receive _ fv _ npCd) =  pFv npCd DELETE fv ∧
  pFv (IfThen fv npCd1 npCd2) = fv INSERT pFv npCd1 ∪ pFv npCd2 ∧
  pFv (Let bv _ fvs npCd) = (pFv npCd DELETE bv) ∪ set fvs
End

Definition pSt_pCd_corr_def:
  pSt_pCd_corr (pSt :payloadLang$state) pCd ⇔ ∀vn. vn ∈ pFv pCd
                              ⇒ ∃vv. FLOOKUP pSt.bindings vn = SOME vv
End

Theorem trans_pSt_pCd_corr_pres:
  ∀conf p s c L s' c'.
   trans conf (NEndpoint p s c) L (NEndpoint p s' c') ∧
   pSt_pCd_corr s c
   ⇒ pSt_pCd_corr s' c'
Proof
  rw []
  \\ last_assum (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw [] \\ fs [pSt_pCd_corr_def,pFv_def] \\ rw []
  \\ TRY (fs [FLOOKUP_UPDATE] \\ EVERY_CASE_TAC \\ fs [] \\ NO_TAC)
  \\ metis_tac []
QED

(* Payload State and Semantic Environment *)
(* -- Check the semantic environment contains all the variable bindings in
      the payload state and also matches all the config assumptions        *)
Definition sem_env_cor_def:
    sem_env_cor conf (pSt :payloadLang$state) cEnv ⇔
        env_asm cEnv conf ∧
        ∀ n v.  FLOOKUP pSt.bindings n = SOME v
                ⇒ ∃v'.  nsLookup (cEnv.v) (Short (ps2cs n)) = SOME v' ∧
                        ^(DATUM) v v'
End

(* -- Check the semantic environment has all the Let functions
      defined as specified in given list *)
Definition enc_ok_def:
    (enc_ok _ _ [] [] = T) ∧
    (enc_ok conf cEnv (f::fs) (n::ns) =
       ((∃cl.
            (SOME cl = nsLookup (cEnv.v) (getLetID conf n)) ∧
            (LIST_TYPE ^(DATUM) --> ^DATUM) f cl
         ) ∧
        enc_ok conf cEnv fs ns
        )
    ) ∧
    (enc_ok _ _ _ _ = F)
End

(* -- Helper Theorems about enc_ok *)
Theorem enc_ok_take:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv x (TAKE (LENGTH x) vs)
Proof
  Induct_on ‘x’ >> fs[enc_ok_def,LENGTH,TAKE] >>
  rw[] >> PURE_ONCE_REWRITE_TAC [enc_ok_def] >>
  ‘SUC (LENGTH x) ≤ LENGTH vs’
    by (‘∀a b. enc_ok conf cEnv a b ⇒ (LENGTH a = LENGTH b)’
          by (Induct_on ‘a’ >> Cases_on ‘b’ >>
              fs[enc_ok_def]) >>
        ‘LENGTH (h :: (x ++ y)) = LENGTH vs’
          by rw[] >>
        ‘SUC (LENGTH (x ++ y)) = LENGTH vs’
          by metis_tac[LENGTH] >>
        ‘LENGTH x ≤ LENGTH (x ++ y)’
          suffices_by (rw[] >>
                      ‘SUC (LENGTH x) ≤ SUC (LENGTH (x ++ y))’
                        by rw[] >>
                      simp[]) >>
        rw[]) >>
  Cases_on ‘vs’ >> fs[enc_ok_def] >>
  metis_tac[]
QED

Theorem enc_ok_drop:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv y (DROP (LENGTH x) vs)
Proof
  Induct_on ‘x’ >> fs[enc_ok_def,LENGTH,TAKE] >>
  rw[] >> PURE_ONCE_REWRITE_TAC [enc_ok_def] >>
  ‘SUC (LENGTH x) ≤ LENGTH vs’
    by (‘∀a b. enc_ok conf cEnv a b ⇒ (LENGTH a = LENGTH b)’
          by (Induct_on ‘a’ >> Cases_on ‘b’ >>
              fs[enc_ok_def]) >>
        ‘LENGTH (h :: (x ++ y)) = LENGTH vs’
          by rw[] >>
        ‘SUC (LENGTH (x ++ y)) = LENGTH vs’
          by metis_tac[LENGTH] >>
        ‘LENGTH x ≤ LENGTH (x ++ y)’
          suffices_by (rw[] >>
                      ‘SUC (LENGTH x) ≤ SUC (LENGTH (x ++ y))’
                        by rw[] >>
                      simp[]) >>
        rw[]) >>
  Cases_on ‘vs’ >> fs[enc_ok_def]
QED

Theorem enc_ok_bind:
  ∀conf cEnv hs vs.
    enc_ok conf cEnv hs vs ⇒
    ∀name val.
      enc_ok conf (cEnv with v:= nsBind (ps2cs name) val cEnv.v) hs vs
Proof
  Induct_on ‘hs’ >>
  rw[] >> Cases_on ‘vs’ >> fs[enc_ok_def] >>
  qexists_tac ‘cl’ >> rw[] >>
  fs[nsLookup_def,getLetID_def]
QED


(* FFI and Payload State *)
(* -- Check identifier and FFI model contains
      correct messages *)
Definition ffi_state_cor_def:
  ffi_state_cor conf cpNum pSt (fNum,fQueue,fNet) ⇔
    cpNum = fNum ∧
    ∃fQueue1 fNet1.
      ffi_wf (fNum,fQueue1,fNet1) ∧
      ffi_eq conf (fNum,fQueue,fNet) (fNum,fQueue1,fNet1) ∧
      ∀sp.
        isPREFIX (qlk pSt.queues sp) (qlk fQueue1 sp)
End

(* Combined *)
Definition cpEval_valid_def:
  cpEval_valid conf cpNum cEnv pSt pCd vs cSt ⇔
    conf.payload_size ≠ 0 ∧
    env_asm cEnv conf ∧
    enc_ok conf cEnv (letfuns pCd) vs ∧
    pSt_pCd_corr pSt pCd ∧
    sem_env_cor conf pSt cEnv ∧
    ffi_state_cor conf cpNum pSt cSt.ffi.ffi_state ∧
    ffi_wf cSt.ffi.ffi_state ∧
    cSt.ffi.oracle = comms_ffi_oracle conf
End

(* VALIDITY *)
(* Check that Payload States with label transition and
   two corresponding FFI states are all valid to produce
   coherent corresponding transitions *)
Definition cpFFI_valid_def:
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 (LSend _ d rp)
    ⇔ strans conf ffi1 (ASend rp d) ffi2) ∧
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 (LReceive _ _ _)
    ⇔ ffi_eq conf ffi1 ffi2) ∧
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 LTau
    ⇔ case (some (sp,d).
              pSt1.queues = normalise_queues (pSt2.queues |+ (sp,d::qlk pSt2.queues sp))) of
        SOME (sp,d) => strans conf ffi1 (ARecv sp d) ffi2
      | NONE        => ffi_eq conf ffi1 ffi2)
End

Theorem normalise_queues_dequeue_eq:
  ∀s s' q r.
    normalised s'.queues ∧
    s.queues = normalise_queues (s'.queues |+ (q,r::qlk s'.queues q))
    ⇒ s'.queues = normalise_queues (s.queues |+ (q,qlk s'.queues q))
Proof
  rw [] \\ fs [normalised_def]
  \\ Cases_on ‘qlk s'.queues q’
  >- (fs [qlk_def,fget_def]
      \\ EVERY_CASE_TAC
      >- (fs [normalise_queues_FUPDATE_NONEMPTY,FLOOKUP_DEF]
          \\ drule NOT_FDOM_DRESTRICT \\ rw [])
      \\ fs [] \\ rveq
      \\ pop_assum (fn t1 => last_assum (fn t2 => assume_tac (ONCE_REWRITE_RULE [GSYM t2] t1)))
      \\ fs [normalise_queues_def,FLOOKUP_DRESTRICT] \\ fs [])
  \\ qmatch_goalsub_abbrev_tac ‘_ = ss’
  \\ qpat_assum ‘normalise_queues _ = _’  (ONCE_REWRITE_TAC o single o GSYM)
  \\ UNABBREV_ALL_TAC
  \\ AP_TERM_TAC
  \\ ONCE_REWRITE_TAC [GSYM fmap_EQ_THM]
  \\ fs [qlk_def,fget_def]
  \\ EVERY_CASE_TAC
  \\ fs [] \\ rveq \\ rw []
  >- fs [FLOOKUP_DEF,ABSORPTION_RWT]
  \\ rw [FAPPLY_FUPDATE_THM]
  \\ fs [FLOOKUP_DEF]
QED

(* CAKEML EQUIVALENCE *)
(* Basic Definition *)
Definition cEval_equiv_def:
  cEval_equiv conf (csA,crA) (csB,crB) ⇔
    ffi_eq conf csA.ffi.ffi_state csB.ffi.ffi_state ∧
    crA = crB ∧
    crA ≠ Rerr (Rabort Rtimeout_error)
End
(* Transitive *)
Theorem cEval_equiv_trans:
  ∀conf p1 p2 p3.
   cEval_equiv conf p1 p2 ∧
   cEval_equiv conf p2 p3
   ⇒ cEval_equiv conf p1 p3
Proof
  rw [] \\ Cases_on ‘p1’ \\ Cases_on ‘p2’ \\ Cases_on ‘p3’
  \\ fs [cEval_equiv_def] \\ qspec_then ‘conf’ assume_tac ffi_eq_equivRel
  \\ fs [equivalence_def,transitive_def]
  \\ metis_tac []
QED
(* Irrelevance of extra time/fuel to equivalence *)
Theorem clock_irrel:
  ∀ conf cSt1 cSt2 cEnv1 cExps1 cEnv2 cExps2.
    ∀mc eck1 eck2.
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) cEnv1 cExps1)
        (evaluate (cSt2 with clock := mc) cEnv2 cExps2)
    ⇒ cEval_equiv conf
        (evaluate (cSt1 with clock := eck1 + mc) cEnv1 cExps1)
        (evaluate (cSt2 with clock := eck2 + mc) cEnv2 cExps2)
Proof
  rpt strip_tac >>
  Cases_on ‘evaluate (cSt1 with clock := mc) cEnv1 cExps1’ >>
  Cases_on ‘evaluate (cSt2 with clock := mc) cEnv2 cExps2’ >>
  fs[cEval_equiv_def] >>
  ‘evaluate (cSt1 with clock := eck1 + mc) cEnv1 cExps1
    = (q with clock := eck1 + q.clock,r)’
    by (Q.ISPECL_THEN [‘(cSt1 with clock := mc)’,‘cEnv1’, ‘cExps1’,‘q’,‘r’,‘eck1’]
                      assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  ‘evaluate (cSt2 with clock := eck2 + mc) cEnv2 cExps2
    = (q' with clock := eck2 + q'.clock,r')’
    by (Q.ISPECL_THEN [‘(cSt2 with clock := mc)’,‘cEnv2’, ‘cExps2’,‘q'’,‘r'’,‘eck2’]
                      assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  rw[cEval_equiv_def]
QED

(* SEND EVENTS FFI INTERACTION
    Used with sendloop_correct in proofs to model
    changes to FFI *)
(* send_events produces valid send events *)
Theorem send_events_is_stream:
  ∀conf l d.
    EVERY (valid_send_event_format conf l) (send_events conf l d)
Proof
  rw[] >> Cases_on ‘conf.payload_size = 0’
  >- rw[send_events_def,Once compile_message_def] >>
  completeInduct_on ‘LENGTH d’ >>
  rw[send_events_def,Once compile_message_def] >>
  rw[valid_send_event_format_def,valid_send_call_format_def,pad_def] >>
  ‘0 < LENGTH d’
    by (‘0 ≠ LENGTH d’
          suffices_by metis_tac[DECIDE “0 ≠ (n:num) ⇒ 0 < n”] >>
        CCONTR_TAC >> fs[] >>
        ‘final (pad conf d)’
          suffices_by fs[] >>
        simp[pad_def,final_def]) >>
  qmatch_goalsub_abbrev_tac ‘EVERY (valid_send_event_format conf l) func’ >>
  ‘func = send_events conf l (DROP conf.payload_size d)’
    suffices_by rw[] >>
  rw[Abbr ‘func’,send_events_def]
QED
(* A stream of valid send events cannot break wellformedness *)
Theorem ffi_wf_send_stream_irrel:
  ∀conf ckFSt l send_stream P.
    ffi_wf ckFSt ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_wf (update_state ckFSt (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_wf (update_state ckFSt1 _ send_stream)’ >>
  rename1 ‘valid_send_event_format conf l (IO_event s l' d)’ >>
  ‘l' = l’
    by fs[valid_send_event_format_def,valid_send_call_format_def] >>
  fs[] >>
  first_x_assum (K ALL_TAC) >>
  last_x_assum irule >>
  qpat_assum ‘ffi_accepts_rel _ _ _’ (assume_tac o (REWRITE_RULE [ffi_accepts_rel_def])) >>
  first_x_assum (qspecl_then [‘<|oracle := comms_ffi_oracle conf;
                               ffi_state := ckFSt;
                               io_events := ARB|>’,
                               ‘s’,‘l’,‘MAP FST d’]
                           strip_assume_tac) >>
  rfs[valid_send_event_format_def] >>
  fs[] >> qunabbrev_tac ‘ckFSt1’ >>
  qmatch_goalsub_rename_tac ‘ffi_wf ckFSt1’ >>
  rw[]
  >- (fs[valid_send_event_format_def,
         valid_send_call_format_def,
         comms_ffi_oracle_def] >>
      rfs[ffi_send_def] >>
      fs[some_def] >>
      Cases_on ‘∃ns. strans conf ckFSt (ASend l (MAP SND d)) ns’ >>
      fs[] >> qpat_x_assum ‘(@ns. _) = _’ mp_tac >>
      SELECT_ELIM_TAC >> metis_tac[strans_pres_wf])
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> fs[])
QED
(* send_events cannot break wellformedness *)
Theorem ffi_wf_send_events_irrel:
  ∀conf ckFSt l d P.
    ffi_wf ckFSt ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_wf (update_state ckFSt (comms_ffi_oracle conf)
                         (send_events conf l d))
Proof
  rpt strip_tac >>
  ‘EVERY (valid_send_event_format conf l) (send_events conf l d)’
    suffices_by  (rw[] >> irule ffi_wf_send_stream_irrel >> rw[] >>
                  MAP_EVERY qexists_tac [‘P’,‘l’] >> rw[]) >>
  metis_tac[send_events_is_stream]
QED

(* A stream of valid send events cannot break FFI correspondence*)
Theorem ffi_state_cor_send_stream_irrel:
  ∀conf cpNum pSt ckFSt l send_stream P.
    ffi_wf ckFSt ∧
    ffi_state_cor conf cpNum pSt ckFSt ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor conf cpNum pSt (update_state ckFSt (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_state_cor conf cpNum pSt (update_state ckFSt1 _ send_stream)’ >>
  rename1 ‘valid_send_event_format conf l (IO_event s l' d)’ >>
  ‘l' = l’
    by fs[valid_send_event_format_def,valid_send_call_format_def] >>
  pop_assum SUBST_ALL_TAC >>
  last_x_assum irule >>
  qpat_assum ‘ffi_accepts_rel _ _ _’
             (assume_tac o (REWRITE_RULE [ffi_accepts_rel_def])) >>
  first_x_assum (qspecl_then [‘<|oracle := comms_ffi_oracle conf;
                                 ffi_state := ckFSt;
                                 io_events := ARB|>’,
                              ‘s’,‘l’,‘MAP FST d’]
                           strip_assume_tac) >>
  rfs[valid_send_event_format_def] >>
  fs[] >> qunabbrev_tac ‘ckFSt1’ >>
  qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ _ ckFSt1’ >>
  rw[]
  >- (fs[comms_ffi_oracle_def,valid_send_call_format_def] >>
      rw[] >> fs[ffi_send_def,AllCaseEqs()] >> first_x_assum mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >> metis_tac[strans_pres_wf])
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> fs[]) >>
  fs[ffi_accepts_rel_def,valid_send_event_format_def] >>
  rfs[] >>
  qpat_x_assum ‘∀a b c d. e’ (K ALL_TAC) >>
  fs[comms_ffi_oracle_def] >>
  ‘s = "send"’
    by fs[valid_send_call_format_def] >> pop_assum SUBST_ALL_TAC >>
  fs[ffi_send_def, some_def, AllCaseEqs()] >> rw[] >>
  irule SELECT_ELIM_THM >>
  rw[]
  >- (qpat_x_assum ‘strans _ _ _ ns’ (K ALL_TAC) >>
      qmatch_goalsub_rename_tac ‘ffi_state_cor _ _  _ ns’ >>
      MAP_EVERY PairCases_on [‘ns’,‘ckFSt’] >>
      fs[ffi_state_cor_def] >>
      ‘ns0 = ckFSt0’
        by metis_tac[strans_pres_pnum,pairTheory.FST] >>
      rw[] >>
      ‘∃s2.
        strans conf (ckFSt0,fQueue1,fNet1)
                    (ASend l (MAP SND d))
                    s2’
        by metis_tac[ffi_eq_def,bisimulationTheory.BISIM_REL_def,
                     bisimulationTheory.BISIM_def,pairTheory.FORALL_PROD] >>
      PairCases_on ‘s2’ >>
      ‘s20 = ckFSt0’
        by metis_tac[strans_pres_pnum,pairTheory.FST] >>
      rw[] >>
      MAP_EVERY qexists_tac [‘s21’,‘s22’] >>
      rw[]
      >- metis_tac[strans_pres_wf]
      >- metis_tac[ffi_eq_pres,pairTheory.FORALL_PROD] >>
      ‘∀sp.
        isPREFIX (qlk fQueue1 sp) (qlk s21 sp)’
        suffices_by metis_tac[IS_PREFIX_TRANS] >>
      metis_tac[strans_queue_pres])
  >- (qexists_tac ‘ns’ >> simp[])
QED

(* send_events cannot break FFI correspondence*)
Theorem ffi_state_cor_send_events_irrel:
  ∀conf cpNum pSt ckFSt l d P.
    ffi_wf ckFSt ∧
    ffi_state_cor conf cpNum pSt ckFSt ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor conf cpNum pSt (update_state ckFSt (comms_ffi_oracle conf)
                                          (send_events conf l d))
Proof
  rpt strip_tac >>
  ‘EVERY (valid_send_event_format conf l) (send_events conf l d)’
    suffices_by  (rw[] >> irule ffi_state_cor_send_stream_irrel >> rw[] >>
                  MAP_EVERY qexists_tac [‘P’,‘l’] >> rw[]) >>
  metis_tac[send_events_is_stream]
QED
(* A stream of valid send events applied to two FFI states does not
   break equivalence *)
Theorem ffi_eq_send_stream_irrel:
  ∀conf fs1 fs2 l send_stream P.
    ffi_wf fs1 ∧
    ffi_wf fs2 ∧
    ffi_eq conf fs1 fs2 ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P fs1 ∧
    P fs2
    ⇒
    ffi_eq conf (update_state fs1 (comms_ffi_oracle conf) send_stream)
                (update_state fs2 (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_eq conf (update_state fs1A _ _) (update_state fs2A _ _)’ >>
  last_x_assum irule >>
  ‘l' = l’
    by fs[valid_send_event_format_def,valid_send_call_format_def] >>
  fs[] >> first_x_assum (K ALL_TAC) >>
  qmatch_asmsub_rename_tac ‘IO_event s l data’ >> rw[] >>
  ‘∃L. strans conf fs1 L fs1A ∧ strans conf fs2 L fs2A’
    by (qexists_tac ‘ASend l (MAP FST data)’ >>
        qunabbrev_tac ‘fs1A’ >> qunabbrev_tac ‘fs2A’ >>
        ‘s = "send"’
          by fs[valid_send_event_format_def,valid_send_call_format_def] >>
        fs[] >> first_x_assum (K ALL_TAC) >>
        ‘LENGTH data = SUC conf.payload_size’
          by fs[valid_send_event_format_def,valid_send_call_format_def] >>
        rw[] >> qmatch_goalsub_rename_tac ‘strans conf si _ _’ >>
        SELECT_ELIM_TAC >> rw[] >>
        fs[ffi_accepts_rel_def,comms_ffi_oracle_def,ffi_send_def,some_def] >>
        first_x_assum (qspecl_then [‘<|oracle := comms_ffi_oracle conf;
                                       ffi_state := si;
                                       io_events := ARB|>’,
                                       ‘"send"’,‘l’,‘MAP FST data’]
                         strip_assume_tac) >>
        fs[valid_send_event_format_def,valid_send_call_format_def,comms_ffi_oracle_def,ffi_send_def,
          some_def] >>
        rfs[] >>
        Cases_on ‘∃ns. strans conf si (ASend l (MAP SND data)) ns’ >> fs[] >>
        metis_tac[])
  >- (metis_tac[strans_pres_wf])
  >- (metis_tac[strans_pres_wf])
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> qunabbrev_tac ‘fs1A’ >>
      qunabbrev_tac ‘fs2A’ >> simp[] >>
      ‘∀si. P si ⇒ P (@st. comms_ffi_oracle conf s si l (MAP FST data) =
                            Oracle_return st (MAP SND data))’
        suffices_by rw[] >>
      rw[] >> SELECT_ELIM_TAC >> rw[] >>
      fs[ffi_accepts_rel_def] >>
      first_x_assum (qspecl_then [‘<|oracle := comms_ffi_oracle conf;
                                     ffi_state := si;
                                     io_events := ARB|>’,
                                     ‘s’,‘l’,‘MAP FST data’]
                       strip_assume_tac) >>
      fs[valid_send_event_format_def] >>
      rfs[])
  >- (metis_tac[ffi_eq_pres])
QED
(* send_events applied to two FFI states does not
   break equivalence *)
Theorem ffi_eq_send_events_irrel:
  ∀conf fs1 fs2 l send_stream P d.
    ffi_wf fs1 ∧
    ffi_wf fs2 ∧
    ffi_eq conf fs1 fs2 ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P fs1 ∧
    P fs2 ⇒
    ffi_eq conf (update_state fs1 (comms_ffi_oracle conf) (send_events conf l d))
                (update_state fs2 (comms_ffi_oracle conf) (send_events conf l d))
Proof
  rpt strip_tac >>
  ‘EVERY (valid_send_event_format conf l) (send_events conf l d)’
    suffices_by  (rw[] >> irule ffi_eq_send_stream_irrel >> rw[] >>
                  MAP_EVERY qexists_tac [‘P’,‘l’] >> rw[]) >>
  metis_tac[send_events_is_stream]
QED

(* FFI IRRELEVANCE TO EVALUATION THEOREM
    Primary theorem we hope will help prove forward
    correctness *)
Theorem ffi_irrel:
  ∀conf cpNum cEnv pSt pCd vs cSt1 cSt2.
    cpEval_valid conf cpNum cEnv pSt pCd vs cSt1 ∧
    cpEval_valid conf cpNum cEnv pSt pCd vs cSt2 ∧
    ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state
    ⇒ ∃mc. cEval_equiv conf
            (evaluate (cSt1  with clock := mc) cEnv
                      [compile_endpoint conf vs  pCd])
            (evaluate (cSt2  with clock := mc) cEnv
                      [compile_endpoint conf vs  pCd])
Proof
  Induct_on ‘pCd’ >> rw[compile_endpoint_def]
  >- ((* Nil Case *)
      rw (cEval_equiv_def::eval_sl_nf))
  >- ((* Send Case *)
      rw eval_sl_nf >>
      ‘∃ha_s. FLOOKUP pSt.bindings s = SOME ha_s’
        by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
      fs[] >>
      ‘ALL_DISTINCT (MAP (λ(x,y,z). x) (sendloop conf (MAP (CHR ∘ w2n) l))) = T’
        by EVAL_TAC >>
      first_x_assum SUBST1_TAC >>
      rw eval_sl_nf >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ cEnvBR _’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ _ [App Opapp [_;Drop_Exp]]’ >>
      ‘ck_equiv_hol cEnvBR (^DATUM) Drop_Exp (combin$C DROP ha_s n)’
        by (qunabbrev_tac ‘Drop_Exp’ >>
            irule ck_equiv_hol_App >>
            qexists_tac ‘NUM’ >>
            rw[]
            >- (irule ck_equiv_hol_Lit >>
                rw trans_sl)
            >- (irule ck_equiv_hol_App >>
                qexists_tac ‘^DATUM’ >>
                rw[]
                >- (irule ck_equiv_hol_Var >>
                    ‘nsLookup cEnvBR.v (Short (ps2cs s)) = nsLookup cEnv.v (Short (ps2cs s))’
                      by (qunabbrev_tac ‘cEnvBR’ >> rw[sendloop_def] >> EVAL_TAC) >>
                    first_x_assum SUBST1_TAC >>
                    fs[cpEval_valid_def,sem_env_cor_def])
                >- (irule ck_equiv_hol_Var >>
                    ‘nsLookup cEnvBR.v conf.drop = nsLookup cEnv.v conf.drop’
                      by (qunabbrev_tac ‘cEnvBR’ >>
                          rw[sendloop_def] >> fs[cpEval_valid_def,env_asm_def,in_module_def]) >>
                    first_x_assum SUBST1_TAC >>
                    fs[cpEval_valid_def,env_asm_def,has_v_def]))) >>
      qspecl_then [‘conf’,‘combin$C DROP ha_s n’,‘cEnvBR’,‘cEnv’,‘Drop_Exp’,‘cSt1’,
                   ‘valid_send_dest l’,‘l’] strip_assume_tac sendloop_correct >>
      ‘env_asm cEnv conf’
        by fs[cpEval_valid_def] >>
      ‘conf.payload_size ≠ 0’
        by fs[cpEval_valid_def] >>
      ‘nsLookup cEnvBR.v (Short "sendloop")
       = SOME (Recclosure cEnv (sendloop conf (MAP (CHR o w2n) l)) "sendloop")’
        by rw[Abbr ‘cEnvBR’,sendloop_def,nsLookup_def,nsBind_def] >>
      qpat_x_assum ‘ck_equiv_hol _ _ Drop_Exp _’ assume_tac >>
      ‘ffi_accepts_rel (valid_send_dest l) (valid_send_call_format conf l) (cSt1.ffi.oracle)’
        by (‘cSt1.ffi.oracle = comms_ffi_oracle conf’
             by fs[cpEval_valid_def] >>
            rw [send_invariant]) >>
      fs[] >>
      Cases_on ‘valid_send_dest l cSt1.ffi.ffi_state’
      >- (fs[] >> rename [‘evaluate (cSt1 with clock := bc1_1) cEnvBR _ =
                               (cSt1 with <|clock := bc2_1; refs := cSt1.refs ++ drefsS1;
                                ffi := _|>,_)’] >>
          Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
          drule_then strip_assume_tac evaluate_add_to_clock >>
          fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
          qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
          ‘cSt1.ffi.oracle = cSt2.ffi.oracle’
            by fs[cpEval_valid_def] >>
          fs[] >> first_x_assum (K ALL_TAC) >>
          qspecl_then [‘conf’,‘combin$C DROP ha_s n’,‘cEnvBR’,‘cEnv’,‘Drop_Exp’,‘cSt2’,
                       ‘valid_send_dest l’,‘l’] strip_assume_tac sendloop_correct >>
          rfs[] >>
          ‘valid_send_dest l cSt2.ffi.ffi_state’
            by metis_tac[ffi_eq_sendval] >>
          fs[] >> rename [‘evaluate (cSt2 with clock := bc1_2) cEnvBR _ =
                           (cSt2 with <|clock := bc2_2; refs := cSt2.refs ++ drefsS2;
                                          ffi := _|>,_)’] >>
          Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
          drule_then strip_assume_tac evaluate_add_to_clock >>
          fs[] >>
          ‘∀a. bc1_1 + (bc1_2 + a) = bc1_2 + (bc1_1 + a)’ by rw [] >>
          pop_assum (fn thm => ONCE_REWRITE_TAC [thm]) >>
          fs [] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
          qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
          simp[nsOptBind_def] >>
          qmatch_goalsub_abbrev_tac ‘∃mc. cEval_equiv conf
                                    (evaluate (cSt1M with clock := bc1_2 + (bc2_1 + mc)) cEnv _)
                                    (evaluate (cSt2M with clock := bc1_1 + (bc2_2 + mc)) cEnv _)’ >>
          last_x_assum (qspecl_then [‘conf’,‘cpNum’,‘cEnv’,‘pSt’,‘vs’,
                                     ‘cSt1M’,‘cSt2M’] strip_assume_tac) >>
          ‘cpEval_valid conf cpNum cEnv pSt pCd vs cSt1M’
            by (qunabbrev_tac ‘cSt1M’ >> rw[cpEval_valid_def] >>
                fs[cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def]
                >- (irule ffi_state_cor_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[])
                >- (irule ffi_wf_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[])) >>
          ‘cpEval_valid conf cpNum cEnv pSt pCd vs cSt2M’
            by (qunabbrev_tac ‘cSt2M’ >> rw[cpEval_valid_def] >>
                fs[cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def]
                >- (irule ffi_state_cor_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[])
                >- (irule ffi_wf_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[])) >>
          ‘ffi_eq conf cSt1M.ffi.ffi_state cSt2M.ffi.ffi_state’
          suffices_by (ONCE_REWRITE_TAC [ADD_ASSOC] >>
                       qabbrev_tac ‘dc1 = bc1_2 + bc2_1’ >>
                       qabbrev_tac ‘dc2 = bc1_1 + bc2_2’ >>
                       rw[] >> fs[] >> metis_tac[clock_irrel]) >>
          qunabbrev_tac ‘cSt1M’ >> qunabbrev_tac ‘cSt2M’ >> simp[] >>
          qpat_x_assum ‘ffi_accepts_rel _ _ _’ assume_tac >>
          qpat_x_assum ‘ffi_eq conf _ _’ assume_tac >>
          ‘cSt2.ffi.oracle = comms_ffi_oracle conf’
            by fs[cpEval_valid_def] >>
          fs[] >>
          first_x_assum (K ALL_TAC) >>
          ‘ffi_wf cSt1.ffi.ffi_state’
            by fs[cpEval_valid_def] >>
          ‘ffi_wf cSt2.ffi.ffi_state’
            by fs[cpEval_valid_def] >>
          irule ffi_eq_send_events_irrel >> rw[] >>
          qexists_tac ‘valid_send_dest l’ >> simp[]) >>
      qpat_x_assum ‘valid_send_dest _ _ ⇒ _’ (K ALL_TAC) >>
      rw eval_sl >>
      drule_then (qspec_then ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      rename [‘∀dc. evaluate (cSt1 with clock := bc1_1 + dc) cEnvBR _ =
               (cSt1 with <|clock := dc + bc2_1; refs := cSt1.refs ++ drefsD1|>,
                Rval [cVD1])’] >>
      Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      Q.REFINE_EXISTS_TAC ‘SUC mc’ >>
      reverse (rw[ADD1,dec_clock_def]) >>
      drule_then (qspec_then ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      rename [‘∀dc. evaluate (cSt2 with clock := bc1_2 + dc) cEnvBR _ =
               (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefsD2|>,
                Rval [cVD2])’] >>
      Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
      ‘∀mc. bc1_1 + (bc1_2 + mc + 1) = bc1_2 + (bc1_1 + mc + 1)’ by rw [] >>
      pop_assum (fn thm => ONCE_REWRITE_TAC [thm]) >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      rw (sendloop_def::do_opapp_def::eval_sl) >>
      PURE_ONCE_REWRITE_TAC [find_recfun_def] >>
      rw [GSYM sendloop_def] >>
      PURE_ONCE_REWRITE_TAC eval_sl_nf >>
      (* BEGIN: DISPOSE REFS CHANGE *)
      qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefsD1’ >>
      qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefsD2’ >>
      ‘¬valid_send_dest l cSt1I.ffi.ffi_state’
        by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
      qpat_x_assum ‘¬valid_send_dest l cSt1.ffi.ffi_state’ (K ALL_TAC) >>
      ‘cSt1.ffi.oracle = cSt1I.ffi.oracle’
        by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
      fs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
        by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
        by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
      ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
        by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
      qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt1A = cSt1 with refs := (cSt1).refs ++ drefsD1)’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt2A = cSt2 with refs := (cSt2).refs ++ drefsD2)’ (K ALL_TAC) >>
      rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’
      (* END: DISPOSE REFS CHANGE *)
      (* Handle type error case *)
      >- (qexists_tac ‘0’ >> rw[cEval_equiv_def]) >>
      (* Continue with non-errant case *)
      (* Evaluate padv *)
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) cEnvAT1 _’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt2 with clock := _) cEnvAT2 _’ >>
      qspecl_then [‘cEnvAT1’, ‘conf’, ‘DROP n ha_s’, ‘cVD1’,‘Var (Short "x")’,
                   ‘cSt1’,‘cSt1’,‘[]’] strip_assume_tac padv_correct >>
      ‘env_asm cEnvAT1 conf’
        by (fs[Abbr ‘cEnvAT1’,env_asm_def,in_module_def,has_v_def] >>
            rfs[] >> metis_tac[EQ_SYM_EQ]) >>
      fs[] >> first_x_assum (K ALL_TAC) >> rfs[] >>
      ‘evaluate cSt1 cEnvAT1 [Var (Short "x")] = (cSt1 with refs := cSt1.refs, Rval [cVD1])’
        by (qunabbrev_tac ‘cEnvAT1’ >> rw ([nsLookup_def,nsBind_def,nsOptBind_def]@eval_sl) >>
            simp[state_component_equality]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ONCE_REWRITE_TAC [ADD_ASSOC] >>
      qabbrev_tac ‘dc1 = bc1_2 + bc2_1’ >> pop_assum (K ALL_TAC) >>
      qabbrev_tac ‘dc2 = bc1_1 + bc2_2’ >> pop_assum (K ALL_TAC) >>
      rename1 ‘evaluate (cSt1 with clock := bc1_1) _ [_] =
               (cSt1 with <|clock:=bc2_1;refs:=cSt1.refs++drefs_1|>,Rval[Loc num1])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
      qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
      unite_nums "dc1" >>
      unite_nums "dc2" >>
      qspecl_then [‘cEnvAT2’, ‘conf’, ‘DROP n ha_s’, ‘cVD2’,‘Var (Short "x")’,
                   ‘cSt2’,‘cSt2’,‘[]’] strip_assume_tac padv_correct >>
      ‘env_asm cEnvAT2 conf’
        by (fs[Abbr ‘cEnvAT2’,env_asm_def,in_module_def,has_v_def] >>
            rfs[] >> metis_tac[EQ_SYM_EQ]) >>
      fs[] >> first_x_assum (K ALL_TAC) >> rfs[] >>
      ‘evaluate cSt2 cEnvAT2 [Var (Short "x")] = (cSt2 with refs := cSt2.refs, Rval [cVD2])’
        by (qunabbrev_tac ‘cEnvAT2’ >> rw ([nsLookup_def,nsBind_def,nsOptBind_def]@eval_sl) >>
            simp[state_component_equality]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename1 ‘evaluate (cSt2 with clock := bc1_2) _ [_] =
               (cSt2 with <|clock:=bc2_2;refs:=cSt2.refs++drefs_2|>,Rval[Loc num2])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
      qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
      unite_nums "dc1" >>
      unite_nums "dc2" >>
      (* Done padv *)
      (* BEGIN: DISPOSE REFS CHANGE *)
      qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefs_1’ >>
      qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefs_2’ >>
      ‘¬valid_send_dest l cSt1I.ffi.ffi_state’
        by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
      qpat_x_assum ‘¬valid_send_dest l cSt1.ffi.ffi_state’ (K ALL_TAC) >>
      ‘cSt1.ffi.oracle = cSt1I.ffi.oracle’
        by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘cSt1.refs ++ drefs_1  = cSt1I.refs’
        by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘cSt2.refs ++ drefs_2  = cSt2I.refs’
        by (qunabbrev_tac ‘cSt2I’ >> simp[]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
        by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
        by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
      ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
        by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
      qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt1I = cSt1 with refs := cSt1I.refs)’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt2I = cSt2 with refs := cSt2I.refs)’ (K ALL_TAC) >>
      rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’ >>
      (* END: DISPOSE REFS CHANGE *)
      PURE_ONCE_REWRITE_TAC eval_sl_nf >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) cEnvFF1 [App (FFI "send")[d1;v1]]’ >>
      ‘∀mc. evaluate (cSt1 with clock := mc) cEnvFF1 [App (FFI "send") [d1;v1]] =
       (cSt1 with clock := mc,
        Rerr (Rabort (Rffi_error (Final_event "send" l (pad conf (DROP n ha_s)) FFI_diverged))))’
        by (rw([Abbr ‘cEnvFF1’,Abbr ‘v1’,Abbr ‘d1’,nsLookup_def,nsBind_def,
                nsOptBind_def]@eval_sl)
            >- (fs[store_lookup_def] >> rw[] >>
                ‘cSt1.ffi.oracle = comms_ffi_oracle conf’
                  by fs[cpEval_valid_def] >> rw[comms_ffi_oracle_def,ffi_send_def,some_def]
                >- (‘LENGTH (pad conf (DROP n ha_s)) = SUC conf.payload_size’
                    suffices_by fs[] >>
                    first_x_assum (K ALL_TAC) >> rw[pad_def])
                >- (‘valid_send_dest l cSt1.ffi.ffi_state’
                    suffices_by fs[] >>
                    metis_tac[strans_dest_check]))
            >- (qmatch_asmsub_abbrev_tac ‘store_lookup N cSt1.refs = SOME SV’ >>
                ‘store_lookup N cSt1.refs = NONE’
                suffices_by fs[] >>
                rpt (qpat_x_assum ‘store_lookup _ _ = _’ (K ALL_TAC)) >>
                rw[store_lookup_def])) >>
      simp[] >> first_x_assum (K ALL_TAC) >>
      ‘¬valid_send_dest l cSt2.ffi.ffi_state’
        by metis_tac[ffi_eq_sendval] >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt2 with clock := _) cEnvFF2 [App (FFI "send")[d1;v1]]’ >>
      ‘∀mc. evaluate (cSt2 with clock := mc) cEnvFF2 [App (FFI "send") [d1;v1]] =
       (cSt2 with clock := mc,
        Rerr (Rabort (Rffi_error (Final_event "send" l (pad conf (DROP n ha_s)) FFI_diverged))))’
        by (rw([Abbr ‘cEnvFF2’,Abbr ‘v1’,Abbr ‘d1’,nsLookup_def,nsBind_def,
                nsOptBind_def]@eval_sl)
            >- (fs[store_lookup_def] >> rw[] >>
                ‘cSt2.ffi.oracle = comms_ffi_oracle conf’
                  by fs[cpEval_valid_def] >> rw[comms_ffi_oracle_def,ffi_send_def,some_def]
                >- (‘LENGTH (pad conf (DROP n ha_s)) = SUC conf.payload_size’
                    suffices_by fs[] >>
                    first_x_assum (K ALL_TAC) >> rw[pad_def])
                >- (‘valid_send_dest l cSt2.ffi.ffi_state’
                    suffices_by fs[] >>
                    metis_tac[strans_dest_check]))
            >- (qmatch_asmsub_abbrev_tac ‘store_lookup N cSt2.refs = SOME SV’ >>
                ‘store_lookup N cSt2.refs = NONE’
                suffices_by fs[] >>
                rpt (qpat_x_assum ‘store_lookup _ _ = _’ (K ALL_TAC)) >>
                rw[store_lookup_def])) >>
      simp[] >> first_x_assum (K ALL_TAC) >>
      rw[cEval_equiv_def])
  >- ((* Receive Case *)
      qabbrev_tac ‘rec = App Opapp [Var (Short "receiveloop"); Con NONE []]’ >>
      qabbrev_tac ‘lsa = App Opapp [App Opapp [Var conf.append; rec]; convDatumList conf l]’ >>
      qabbrev_tac ‘lsc = App Opapp [Var conf.concat; lsa]’ >>
      rw (buffer_size_def::eval_sl) >>
      rename1 ‘ALL_DISTINCT
                   (MAP (λ(x,y,z). x) (receiveloop conf (MAP (CHR ∘ w2n) l0)))’ >>
      ‘ALL_DISTINCT
                   (MAP (λ(x,y,z). x) (receiveloop conf (MAP (CHR ∘ w2n) l0)))’
        by rw[receiveloop_def,ALL_DISTINCT] >>
      rw[] >> pop_assum (K ALL_TAC) >>
      MAP_EVERY qunabbrev_tac [‘lsa’,‘lsc’] >>
      (* Evaluate Left Hand Side *)
      ntac 4 (rw[Once evaluate_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1M with clock := _) cEnvM’ >>
      cheat
      )
  >- ((* IfThen case *)
      ‘∃ha_s. FLOOKUP pSt.bindings s = SOME ha_s’
        by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
      ‘ck_equiv_hol cEnv (^DATUM) (Var (Short (ps2cs s))) ha_s’
        by (irule ck_equiv_hol_Var >> fs[cpEval_valid_def,sem_env_cor_def]) >>
      ‘ck_equiv_hol cEnv (^DATUM) (w1ckV conf) [1w]’
        by (irule w1ckV_is_1w >> fs[cpEval_valid_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) _ [If Eexp _ _]’ >>
      ‘ck_equiv_hol cEnv BOOL Eexp (ha_s = [1w])’
        by (qunabbrev_tac ‘Eexp’ >> irule ck_equiv_hol_apply_list_word8_equality >>
            fs[]) >>
      rw eval_sl >>
      drule_then (qspec_then ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. evaluate _ _ _ = _’ (K ALL_TAC) >>
      qmatch_goalsub_rename_tac ‘evaluate (cSt2 with clock := dcA + _) _ [_]’ >>
      drule_then (qspec_then ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. evaluate _ _ _ = _’ (K ALL_TAC) >>
      unite_nums "dc1" >> unite_nums "dc2" >>
      Cases_on ‘ha_s = [1w]’ >>
      fs [BOOL_def] >> rw eval_sl >>
      qmatch_goalsub_abbrev_tac
      ‘∃mc.
        cEval_equiv conf
          (evaluate
            (cSt1A with clock := dc1 + mc) cEnv
            [compile_endpoint conf nvs pCdG])
          (evaluate
            (cSt2A with clock := dc2 + mc) cEnv
            [compile_endpoint conf nvs pCdG])’ >>
      qpat_x_assum ‘∀conf cpNum cEnv pSt vs cSt1 cSt1.
                      cpEval_valid _ _ _ _ pCdG _ _ ∧ _ ⇒
                      ∃mc. _’
                  (qspecl_then [‘conf’,‘cpNum’,‘cEnv’,‘pSt’,
                                ‘nvs’,‘cSt1A’,‘cSt2A’]
                                strip_assume_tac) >>
      ‘ffi_eq conf cSt1A.ffi.ffi_state cSt2A.ffi.ffi_state’
        by simp[Abbr ‘cSt1A’,Abbr ‘cSt2A’] >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt pCdG nvs cSt1A’
        by (fs[Abbr ‘cSt1A’,cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
            qunabbrev_tac ‘nvs’ >>
            qpat_x_assum ‘enc_ok conf cEnv _ _’ assume_tac >>
            ntac 18 (last_x_assum (K ALL_TAC)) >>
            metis_tac[enc_ok_drop,enc_ok_take]) >>
      ‘cpEval_valid conf cpNum cEnv pSt pCdG nvs cSt2A’
        by fs[Abbr ‘cSt2A’,cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
      fs[] >> ntac 2 (first_x_assum (K ALL_TAC)) >>
      qexists_tac ‘mc’ >> irule clock_irrel >> fs[])
  >- ((* Let case *)
      ‘∃hd tl. vs = hd::tl’
        by (‘vs ≠ []’
              suffices_by (Cases_on ‘vs’ >> fs[]) >>
            CCONTR_TAC >>
            fs[cpEval_valid_def,enc_ok_def,letfuns_def]) >>
      rw (compile_endpoint_def::eval_sl_nf) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) cEnv [App Opapp [fexp;aexp]]’ >>
      ‘ck_equiv_hol cEnv (LIST_TYPE ^DATUM --> ^DATUM) fexp f’
        by (qunabbrev_tac ‘fexp’ >> irule ck_equiv_hol_Var >>
            fs[cpEval_valid_def,enc_ok_def,letfuns_def] >>
            metis_tac[]) >>
      ‘ck_equiv_hol cEnv (LIST_TYPE ^DATUM) aexp (MAP (THE o FLOOKUP pSt.bindings) l)’
        by (qunabbrev_tac ‘aexp’ >> irule convList_corr >> reverse (rw[LENGTH_MAP])
            >- fs[cpEval_valid_def]
            >- (Induct_on ‘l’ >> rw[EVERY_DEF]
                >- (‘∃h_h. FLOOKUP pSt.bindings h = SOME h_h’
                      by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
                    simp[] >> irule ck_equiv_hol_Var >>
                    fs[cpEval_valid_def,sem_env_cor_def])
                >- (first_x_assum irule >>
                    fs[cpEval_valid_def,enc_ok_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
                    metis_tac[])
                )
            ) >>
      qspecl_then [‘fexp’,‘f’,‘aexp’,‘MAP (THE o FLOOKUP pSt.bindings) l’,‘LIST_TYPE ^DATUM’,
                   ‘^DATUM’,‘cEnv’] strip_assume_tac ck_equiv_hol_App >>
      rfs[] >>
      drule_then (qspec_then ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt2 with clock := bc1_2 + dc) cEnv
                  [App Opapp [fexp; aexp]] =
                (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefs_2|>,
                 Rval [cV_2])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >> simp[] >>
      first_x_assum (K ALL_TAC) >>
      drule_then (qspec_then ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt1 with clock := bc1_1 + dc) cEnv
                  [App Opapp [fexp; aexp]] =
                (cSt1 with <|clock := dc + bc2_1; refs := cSt1.refs ++ drefs_1|>,
                 Rval [cV_1])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >> simp[] >>
      first_x_assum (K ALL_TAC) >>
      unite_nums "dc1" >> unite_nums "dc2" >>
      ‘cV_2 = cV_1’
        by (‘UNCT ^DATUM’
              suffices_by metis_tac[UNCT_def] >>
            metis_tac[LIST_TYPE_UNCT,WORD_UNCT]) >>
      rw[] >> first_x_assum (K ALL_TAC) >>
      rename1 ‘LIST_TYPE WORD _ cV’ >>
      rpt (qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC)) >>
      qunabbrev_tac ‘aexp’ >> qunabbrev_tac ‘fexp’ >>
      qmatch_goalsub_abbrev_tac ‘cEnvM:v sem_env’ >>
      qmatch_asmsub_abbrev_tac ‘^DATUM haf cV’ >>
      first_x_assum (qspecl_then [‘conf’,‘cpNum’,‘cEnvM’,
                                  ‘pSt with bindings := pSt.bindings |+ (s,haf)’,
                                  ‘tl’,‘cSt1 with refs := cSt1.refs ++ drefs_1’,
                                  ‘cSt2 with refs := cSt2.refs ++ drefs_2’]
                                 strip_assume_tac) >>
      rfs[] >>
      qmatch_asmsub_abbrev_tac ‘cpEval_valid conf cpNum cEnvM pStM pCd tl cSt1M ∧
                                cpEval_valid conf cpNum cEnvM pStM pCd tl cSt2M ⇒
                                _’ >>
      ‘conf.payload_size ≠ 0’
        by fs[cpEval_valid_def] >>
      ‘env_asm cEnvM conf’
        by (‘env_asm cEnv conf’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘cEnvM’ >>
            fs[env_asm_def,has_v_def,in_module_def,nsOptBind_def] >>
            qmatch_asmsub_rename_tac ‘(^DATUM --> ^DATUM --> ^DATUM) $++ kv’ >>
            qmatch_goalsub_rename_tac ‘_ $++ uv’ >>
            ‘SOME uv = SOME kv’ suffices_by rw[] >>
            metis_tac[]) >>
      ‘enc_ok conf cEnvM (letfuns pCd) tl’
        by (‘enc_ok conf cEnv (letfuns (Let s f l pCd)) (hd::tl)’
              by fs[cpEval_valid_def] >>
            qpat_x_assum ‘Abbrev (cEnvM = _)’ assume_tac >>
            ntac 11 (last_x_assum (K ALL_TAC)) >>
            fs[letfuns_def,enc_ok_def] >>
            ntac 2 (last_x_assum (K ALL_TAC)) >>
            ‘∀hl cl. enc_ok conf cEnv hl cl ⇒ enc_ok conf cEnvM hl cl’
              suffices_by metis_tac[] >>
            Induct_on ‘hl’ >> Induct_on ‘cl’ >> simp[enc_ok_def] >>
            rw[] >> rename1 ‘SOME c = nsLookup cEnv.v (getLetID conf h)’ >>
            qexists_tac ‘c’ >> simp[getLetID_def] >> qunabbrev_tac ‘cEnvM’ >>
            rw[nsOptBind_def]) >>
      ‘pSt_pCd_corr pStM pCd’
        by (‘pSt_pCd_corr pSt (Let s f l pCd)’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >>
            ntac 10 (last_x_assum (K ALL_TAC)) >>
            fs[pSt_pCd_corr_def] >> rw[] >>
            Cases_on ‘vn = s’ >> rw[FLOOKUP_UPDATE]) >>
      ‘sem_env_cor conf pStM cEnvM’
        by (‘sem_env_cor conf pSt cEnv’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >>
            qunabbrev_tac ‘cEnvM’ >>
            fs[sem_env_cor_def] >>
            qpat_x_assum ‘LIST_TYPE WORD haf cV’ assume_tac >>
            ntac 12 (last_x_assum (K ALL_TAC)) >>
            rw[] >> rename1 ‘FLOOKUP _ n = SOME hn’ >> Cases_on ‘n = s’
            >- (rw[FLOOKUP_UPDATE,nsLookup_def,nsOptBind_def] >>
                qmatch_goalsub_rename_tac ‘LIST_TYPE WORD gH cV’ >>
                ‘gH = haf’
                  by fs[FLOOKUP_UPDATE] >>
                rw[])
            >- (‘ps2cs n ≠ ps2cs s’
                  by rw[ps2cs_def] >>
                fs[FLOOKUP_UPDATE,nsOptBind_def,nsLookup_nsBind_compute])) >>
      ‘ffi_state_cor conf cpNum pStM cSt1M.ffi.ffi_state’
        by (‘ffi_state_cor conf cpNum pSt cSt1.ffi.ffi_state’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >> qunabbrev_tac ‘cSt1M’ >>
            simp[] >> Cases_on ‘cSt1.ffi.ffi_state’ >>
            qmatch_goalsub_rename_tac ‘ffi_state_cor  _ _ _ (P,R)’ >>
            Cases_on ‘R’ >> fs[ffi_state_cor_def] >>
            metis_tac[]) >>
      ‘ffi_state_cor conf cpNum pStM cSt2M.ffi.ffi_state’
        by (‘ffi_state_cor conf cpNum pSt cSt2.ffi.ffi_state’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >> qunabbrev_tac ‘cSt2M’ >>
            simp[] >> Cases_on ‘cSt2.ffi.ffi_state’ >>
            qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ _ (P,R)’ >>
            Cases_on ‘R’ >> fs[ffi_state_cor_def] >>
            metis_tac[]) >>
      ‘ffi_wf cSt1M.ffi.ffi_state’
        by (qunabbrev_tac ‘cSt1M’ >> fs[cpEval_valid_def]) >>
      ‘ffi_wf cSt2M.ffi.ffi_state’
        by (qunabbrev_tac ‘cSt2M’ >> fs[cpEval_valid_def]) >>
      ‘cSt1M.ffi.oracle = comms_ffi_oracle conf’
        by (qunabbrev_tac ‘cSt1M’ >> fs[cpEval_valid_def]) >>
      ‘cSt2M.ffi.oracle = comms_ffi_oracle conf’
        by (qunabbrev_tac ‘cSt2M’ >> fs[cpEval_valid_def]) >>
      fs[cpEval_valid_def] >>
      qexists_tac ‘mc’ >>
      irule clock_irrel >>
      simp[])
QED

Theorem nsOptBind_NONE[simp]:
  nsOptBind NONE x env = env
Proof
  simp[nsOptBind_def]
QED

Theorem ALL_DISTINCT_sendloop_names[simp]:
  ALL_DISTINCT (MAP (λ(x,y,z). x) (sendloop conf data))
Proof
  simp[sendloop_def]
QED

Theorem nsLookup_sendloop[simp]:
  nsLookup (build_rec_env (sendloop conf data) env envv) (Short (ps2cs v)) =
  nsLookup envv (Short (ps2cs v))
Proof
  simp[build_rec_env_def, ps2cs_def, nsLookup_def, sendloop_def]
QED

Theorem nsLookup_cpEval_valid:
  cpEval_valid conf p cE pSt pCd vs cSt ∧ FLOOKUP pSt.bindings v = SOME d ⇒
  ∃cv. nsLookup cE.v (Short (ps2cs v)) = SOME cv ∧ LIST_TYPE WORD d cv
Proof
  csimp[cpEval_valid_def, sem_env_cor_def] >>  metis_tac[]
QED

Theorem nsLookup_build_rec_env_drop:
  cpEval_valid conf p env pSt pCd vs cSt ⇒
  ∃dv. nsLookup (build_rec_env (sendloop conf data) env env.v) conf.drop =
       SOME dv ∧
       (LIST_TYPE (WORD : word8 -> v -> bool) --> NUM --> LIST_TYPE WORD)
       (combin$C DROP) dv
Proof
  simp[build_rec_env_def, sendloop_def, nsLookup_def, nsBind_def,
       cpEval_valid_def, env_asm_def, has_v_def, in_module_def, PULL_EXISTS] >>
  rw[]
QED

Theorem dec_clock_with_clock:
  dec_clock (s with clock := c) = s with clock := c - 1
Proof
  simp[dec_clock_def]
QED

Definition result_bind_def[simp]:
  result_bind (x, Rval v) f = f (x,v) ∧
  result_bind (x, Rerr e) f = (x, Rerr e)
End

Definition result_return_def:
  result_return (x,v) = (x, Rval v)
End

val _ = declare_monad("result", {bind = “result_bind”, ignorebind = NONE,
                                 unit = “result_return”, fail = NONE,
                                 choice = NONE, guard = NONE})

val _ = enable_monad "result"

Theorem evaluate_letNONE:
  evaluate st env [Let NONE e1 e2] =
     do
        (st,v) <- evaluate st env [e1] ;
        evaluate st env [e2]
     od
Proof
  simp[evaluate_def] >> Cases_on‘evaluate st env [e1]’ >>
  rename [‘evaluate _ _ _ = (v, res)’] >> Cases_on ‘res’ >> simp[]
QED

Theorem evaluate_opapp:
  evaluate st env [App Opapp [e1; e2]] =
   do
     (st1,vs2) <- evaluate st env [e2];
     (st2,vs1) <- evaluate st1 env [e1];
     case do_opapp (REVERSE (HD vs2::vs1)) of
       NONE => (st2, Rerr (Rabort Rtype_error))
     | SOME (env, e) => if st2.clock = 0 then (st2,Rerr (Rabort Rtimeout_error))
                        else evaluate (dec_clock st2) env [e]
   od
Proof
  simp[evaluate_def] >>
  Cases_on ‘evaluate st env [e2]’ >>
  rename [‘evaluate st env [e2] = (st1, res2)’] >>
  Cases_on ‘res2’ >> simp[] >>
  ‘(∃st2 vs1. evaluate st1 env [e1] = (st2, Rval vs1)) ∨
   ∃st2 e. evaluate st1 env [e1] = (st2, Rerr e)’
     by metis_tac[pair_CASES, TypeBase.nchotomy_of “:(α,β) result”] >>
  simp[]
QED

val evalths = evaluate_def |> CONJUNCTS
fun find_evalform q =
  let
    val e = Parse.typed_parse_in_context “:ast$exp” [] q
    val l = listSyntax.mk_list([e], type_of e)
    fun test th =
      let val (_, eqn) = strip_forall (concl th)
      in
          can (match_term l) (rand (lhs eqn))
      end

  in
    valOf (List.find test evalths) handle Option => failwith "no match"
  end

Theorem bind_assoc:
  result_bind (result_bind m f) g =
  result_bind m (combin$C (result_bind o f) g)
Proof
  Cases_on ‘m’ >> Cases_on ‘r’ >> simp[]
QED

Theorem nsLookup_sendloop_exists:
  ∃slv. nsLookup (build_rec_env(sendloop conf data) cE cEv) (Short "sendloop") =
        SOME slv
Proof
  simp[build_rec_env_def, sendloop_def]
QED

val cp_type =
  strip_fun (type_of “cpEval_valid”) |> #1 |> last |> dest_type |> #2 |> hd

Theorem pSt_pCd_corr_Send:
  pSt_pCd_corr ps (Send p v n cd) ⇔
    pSt_pCd_corr ps cd ∧
    ∃vv. FLOOKUP ps.bindings v = SOME vv
Proof
  simp[pSt_pCd_corr_def, DISJ_IMP_THM, FORALL_AND_THM, CONJ_COMM]
QED

Theorem ffi_eq_REFL[simp]:
  ffi_eq c s s
Proof
  ‘equivalence (ffi_eq c)’ by simp[ffi_eq_equivRel] >>
  fs[equivalence_def, reflexive_def]
QED

Theorem ffi_eq_TRANS:
  ffi_eq c s1 s2 ∧ ffi_eq c s2 s3 ⇒ ffi_eq c s1 s3
Proof
  ‘equivalence (ffi_eq c)’ by simp[ffi_eq_equivRel] >>
  fs[equivalence_def, transitive_def] >> metis_tac[]
QED

Theorem ffi_eq_bisimulation_L:
  ffi_eq conf s1 s2 ∧ strans conf s1 L s1' ⇒
  ∃s2'. ffi_eq conf s1' s2' ∧ strans conf s2 L s2'
Proof
  simp[ffi_eq_def] >>
  simp[SimpL “$==>”, Once bisimulationTheory.BISIM_REL_cases] >>
  metis_tac[]
QED

Theorem active_trans_pres_nodes:
  (active_trans c p)^* (q0,n0) (q,n) ⇒
  ∀nd. net_has_node n nd ⇔ net_has_node n0 nd
Proof
  ‘∀a b. (active_trans c p)^* a b ⇒
         ∀q0 n0 q n. a = (q0,n0) ∧ b = (q,n) ⇒
                     ∀nd. net_has_node n nd ⇔ net_has_node n0 nd’
  suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  simp[active_trans_def, FORALL_PROD, internal_trans_def, emit_trans_def] >>
  metis_tac[trans_pres_nodes]
QED

Theorem strans_send_queues_unchanged:
  ffi_wf (p,q0,n0) ∧ strans c (p,q0,n0) (ASend d m) (p,q,n) ⇒
  ∃n'. strans c (p,q0,n0) (ASend d m) (p,q0,n') ∧
       ffi_eq c (p,q,n) (p,q0,n')
Proof
  rw[] >>
  ‘∃n'. strans c (p,q0,n0) (ASend d m) (p,q0,n')’
    suffices_by metis_tac[ffi_eq_pres, ffi_eq_REFL] >>
  ‘∃n'. trans c n0 (LReceive p m d) n'’ suffices_by metis_tac[strans_rules] >>
  ‘p ≠ d ∧ net_has_node n0 d’
    by metis_tac[strans_dest_check, valid_send_dest_def, FST,
                 ffi_has_node_def] >>
  metis_tac[trans_receive_cond]
QED

Theorem strans_ASend_pres_ffi_state_cor:
  strans conf s0 (ASend d m) s1 ∧ ffi_state_cor conf p ps s0 ⇒
  ffi_state_cor conf p ps s1
Proof
  map_every PairCases_on [‘s0’, ‘s1’] >> rw[] >>
  drule_then assume_tac strans_pres_pnum >> fs[] >> rw[] >>
  fs[ffi_state_cor_def] >>
  rename [‘strans _ (p,q1,n1) (ASend d m) (p,qA,nA)’,
          ‘ffi_eq _ (p,q1,n1) (p,q2,n2)’] >>
  ‘∃S3. strans conf (p,q2,n2) (ASend d m) S3 ∧ ffi_eq conf (p,qA,nA) S3’
    by metis_tac[ffi_eq_bisimulation_L] >>
  pop_assum mp_tac >> PairCases_on ‘S3’ >>
  rename [‘ffi_eq _ _ (pnum, qB,nB) ⇒ _’] >> drule strans_pres_pnum >>
  rw[] >> qexists_tac ‘q2’ >> simp[] >>
  metis_tac[strans_pres_wf, strans_send_queues_unchanged, ffi_eq_TRANS]
QED

Theorem cpEval_valid_Send_strans_E:
  cpEval_valid conf p1 cEnv pSt pCd vs cSt1 ∧
  cSt2.ffi.oracle = comms_ffi_oracle conf ∧
  strans conf cSt1.ffi.ffi_state (ASend d m) cSt2.ffi.ffi_state
    ⇒
  cpEval_valid conf p1 cEnv pSt pCd vs cSt2
Proof
  simp[cpEval_valid_def, letfuns_def, pSt_pCd_corr_Send] >>
  metis_tac[strans_pres_wf, strans_ASend_pres_ffi_state_cor]
QED

Theorem cpEval_valid_Send_E[simp]:
  cpEval_valid conf p1 cEnv pSt (Send p2 v n pCd) vs cSt
    ⇔
  cpEval_valid conf p1 cEnv pSt pCd vs cSt ∧
  ∃vv. FLOOKUP pSt.bindings v = SOME vv
Proof
  simp[cpEval_valid_def, letfuns_def, pSt_pCd_corr_Send] >> metis_tac[]
QED

Theorem cEval_equiv_bump_clocks:
  cEval_equiv conf (evaluate st1 e1 l1) (evaluate st2 e2 l2) ∧
  st1.clock ≤ clk1 ∧ st2.clock ≤ clk2 ⇒
  cEval_equiv conf (evaluate (st1 with clock := clk1) e1 l1)
                   (evaluate (st2 with clock := clk2) e2 l2)
Proof
  map_every Cases_on [‘evaluate st1 e1 l1’, ‘evaluate st2 e2 l2’] >>
  simp[cEval_equiv_def] >> rw[] >>
  dxrule_then (qspec_then ‘clk2 - st2.clock’ mp_tac) evaluate_add_to_clock >>
  dxrule_then (qspec_then ‘clk1 - st1.clock’ mp_tac) evaluate_add_to_clock >>
  simp[cEval_equiv_def]
QED

Theorem strans_dest_check':
  strans conf S1 (ASend dest bytes) S2 ⇒
  valid_send_dest dest S1 ∧ valid_send_dest dest S2
Proof
  strip_tac >>
  drule_then assume_tac
             (SIMP_RULE (srw_ss()) [PULL_EXISTS] strans_dest_check) >>
  drule_then assume_tac strans_pres_nodes >>
  drule_then assume_tac strans_pres_pnum >> simp[] >>
  fs[valid_send_dest_def]
QED

Theorem pSt_pCd_corr_ignores_queues[simp]:
  pSt_pCd_corr (ps with queues := x) pcd ⇔ pSt_pCd_corr ps pcd
Proof
  simp[pSt_pCd_corr_def]
QED

Theorem sem_env_cor_ignores_queues[simp]:
  sem_env_cor c (ps with queues := x) pcd ⇔ sem_env_cor c ps pcd
Proof
  simp[sem_env_cor_def]
QED

(* FORWARD CORRECTNESS
    Just the spec :) *)
Theorem endpoint_forward_correctness:
  ∀conf p pSt1 pCd1 L pSt2 pCd2 vs1 cEnv1 cSt1 cSt2.
    trans conf (NEndpoint p pSt1 pCd1) L (NEndpoint p pSt2 pCd2) ∧
    cpEval_valid conf p cEnv1 pSt1 pCd1 vs1 cSt1 ∧
    normalised pSt1.queues ∧
    cSt2.ffi.oracle = comms_ffi_oracle conf ∧
    ffi_wf cSt2.ffi.ffi_state ∧
    FST cSt2.ffi.ffi_state = FST cSt1.ffi.ffi_state ∧
    cpFFI_valid conf pSt1 pSt2 cSt1.ffi.ffi_state cSt2.ffi.ffi_state L ⇒
    ∃mc vs2 cEnv2.
         cpEval_valid conf p cEnv2 pSt2 pCd2 vs2 cSt2 ∧
         cEval_equiv conf
          (evaluate (cSt1 with clock := mc) cEnv1
                    [compile_endpoint conf vs1 pCd1])
          (evaluate (cSt2 with clock := mc) cEnv2
                    [compile_endpoint conf vs2 pCd2])
Proof
  simp[Once trans_cases] >> rw[] >> simp[compile_endpoint_def]
  >- ((* sendloop; d ≤ n + payload_size *)
      fs[cpFFI_valid_def] >>
      simp[evaluate_letNONE, find_evalform ‘Letrec _ _’,
           (* Once evaluate_opapp, *)
           bind_assoc, o_UNCURRY_R, C_UNCURRY_L, o_ABS_R, C_ABS_L] >>
      qmatch_goalsub_abbrev_tac ‘sendloop conf data’ >>
      qabbrev_tac ‘
        Env1 = build_rec_env (sendloop conf data) cEnv1 cEnv1.v
      ’ >>
      qmatch_goalsub_abbrev_tac ‘App Opapp [Var (Short "sendloop"); aexp]’ >>
      ‘ck_equiv_hol (cEnv1 with v := Env1) (LIST_TYPE WORD) aexp (DROP n d)’
        by (simp[Abbr‘aexp’, ck_equiv_hol_def, evaluate_opapp, bind_assoc,
                 o_UNCURRY_R, C_UNCURRY_L, o_ABS_R, C_ABS_L,
                 find_evalform ‘Lit _’, find_evalform ‘Var _’] >>
            qx_gen_tac ‘refs0’ >>
            ‘∀v. nsLookup Env1 (Short (ps2cs v)) =
                 nsLookup cEnv1.v (Short (ps2cs v))’
              by simp[Abbr‘Env1’] >> simp[] >>
            drule_all_then (qx_choose_then ‘cv’ strip_assume_tac)
                           nsLookup_cpEval_valid >> simp[] >>
            drule_then (qspec_then ‘data’ $ qx_choose_then ‘dv’ $
                        strip_assume_tac)
                       nsLookup_build_rec_env_drop >> rfs[] >>
            drule_all_then
             (qspec_then ‘empty_state with refs := refs0’ $
              qx_choosel_then [‘dcs_env’, ‘dcs_e’, ‘dcs_cl1’, ‘dcs_cl2’,
                               ‘dcs_refs’, ‘dcs_v’] strip_assume_tac)
             (SIMP_RULE (srw_ss()) [PULL_EXISTS] do_opapp_translate
              |> INST_TYPE [“:'ffi” |-> “:unit”]) >>
            Q.REFINE_EXISTS_TAC ‘dcs_cl1 + (mc + 1)’ >>
            simp[dec_clock_with_clock] >>
            pop_assum kall_tac >>
            ‘NUM n (Litv (IntLit (&n)))’ by simp[NUM_def, INT_def] >>
            drule_all_then
             (qspec_then ‘empty_state with refs := refs0 ++ dcs_refs’ $
              qx_choosel_then [‘alld_env’, ‘alld_e’, ‘alld_cl1’, ‘alld_cl2’,
                               ‘alld_refs’, ‘alld_v’] strip_assume_tac)
             (SIMP_RULE (srw_ss()) [PULL_EXISTS] do_opapp_translate
              |> INST_TYPE [“:'ffi” |-> “:unit”]) >> simp[] >>
            Q.REFINE_EXISTS_TAC ‘alld_cl1 + (mc + 1)’ >> simp[] >> fs[] >>
            simp[state_component_equality]) >>
      first_assum (mp_then (Pos (el 4)) mp_tac
                   (sendloop_correct
                    |> INST_TYPE [alpha |-> cp_type])) >>
      simp[] >>
      ‘nsLookup Env1 (Short "sendloop") =
       SOME (Recclosure cEnv1 (sendloop conf data) "sendloop")’
        by simp[Abbr‘Env1’, build_rec_env_def, sendloop_def] >> simp[] >>
      disch_then (qspecl_then [‘conf’, ‘cSt1’] mp_tac) >>
      ‘cSt1.ffi.oracle = comms_ffi_oracle conf’
        by fs[cpEval_valid_def] >>
      simp[Abbr‘data’] >>
      disch_then (qspecl_then [‘valid_send_dest p2’, ‘p2’] mp_tac) >>
      simp[send_invariant] >> impl_tac
      >- (drule (SIMP_RULE (srw_ss()) [PULL_EXISTS] strans_dest_check) >>
          fs[cpEval_valid_def]) >>
      disch_then (qx_choosel_then [‘ck1’, ‘ck2’, ‘refs’] strip_assume_tac) >>
      Q.REFINE_EXISTS_TAC ‘ck1 + mc’ >>
      dxrule evaluate_add_to_clock >> simp[] >> disch_then kall_tac >>
      drule_all_then assume_tac cpEval_valid_Send_strans_E >>
      goal_assum drule >>
      MAP_EVERY RM_ABBREV_TAC ["aexp", "Env1"] >>
      qpat_x_assum ‘nsLookup _ _ = _’ kall_tac >>
      qpat_abbrev_tac ‘FFI1 = _.ffi with <| ffi_state := _; io_events := _|>’ >>
      ‘cpEval_valid conf p cEnv1 pSt1 pCd2 vs1
        (cSt1 with <| ffi := FFI1 ; refs := cSt1.refs ++ refs|>)’
        by (fs[cpEval_valid_def] >> simp[Abbr‘FFI1’] >>
            conj_tac
            >- (irule ffi_state_cor_send_events_irrel >> simp[] >>
                qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
                irule strans_dest_check >> metis_tac[]) >>
            irule ffi_wf_send_events_irrel >> simp[] >>
            qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
            irule strans_dest_check >> metis_tac[]) >>
      pop_assum (mp_then (Pos hd) drule ffi_irrel) >> simp[] >>
      impl_tac
      >- (‘conf.payload_size > 0’ by fs[cpEval_valid_def] >>
          irule ffi_eq_pres >>
          goal_assum (first_assum o mp_then (Pos last) mp_tac) >>
          qexists_tac ‘cSt1.ffi.ffi_state’ >> csimp[] >> conj_tac
          >- fs[cpEval_valid_def] >>
          simp[Abbr‘FFI1’, send_events_def, Once compile_message_def] >>
          Cases_on ‘LENGTH d = n + conf.payload_size’ >>
          fs[pad_def, final_def, DROP_LENGTH_NIL, update_state_def,
             comms_ffi_oracle_def, ffi_send_def] >>
          simp[AllCaseEqs()] >>
          DEEP_INTRO_TAC optionTheory.some_intro >>
          qpat_x_assum ‘strans _ _ _ _’ mp_tac >>
          simp[] >> metis_tac[]) >>
      disch_then (qx_choose_then ‘mc’ assume_tac) >> qexists_tac ‘mc’ >>
      dxrule cEval_equiv_bump_clocks >> simp[])
  >- ((* Send with LENGTH d > n + conf.payload_size, and evaluations on both
         sides: one of drop v n, other of drop v (n + conf.payload_size) *)
      fs[cpFFI_valid_def, GREATER_DEF] >>
      CONV_TAC SWAP_VARS_CONV >> qexists_tac ‘vs1’ >>
      CONV_TAC SWAP_VARS_CONV >> qexists_tac ‘cEnv1’ >>
      simp[evaluate_letNONE, find_evalform ‘Letrec _ _’,
           (* Once evaluate_opapp, *)
           bind_assoc, o_UNCURRY_R, C_UNCURRY_L, o_ABS_R, C_ABS_L] >>
      qmatch_goalsub_abbrev_tac ‘sendloop conf data’ >>
      qabbrev_tac ‘
        Env1 = build_rec_env (sendloop conf data) cEnv1 cEnv1.v
      ’ >>
      qmatch_goalsub_abbrev_tac ‘App Opapp [dropv; Lit _]’ >>
      qabbrev_tac ‘aexpf = λm. App Opapp [dropv; Lit (IntLit (&m))]’ >>
      simp[] >>
      ‘∀m. ck_equiv_hol (cEnv1 with v := Env1) (LIST_TYPE WORD)
                        (aexpf m)
                        (DROP m d)’
        by (simp[Abbr‘aexpf’, ck_equiv_hol_def, evaluate_opapp, bind_assoc,
                 o_UNCURRY_R, C_UNCURRY_L, o_ABS_R, C_ABS_L, Abbr‘dropv’,
                 find_evalform ‘Lit _’, find_evalform ‘Var _’] >>
            qx_genl_tac [‘m’, ‘refs0’] >>
            ‘∀v. nsLookup Env1 (Short (ps2cs v)) =
                 nsLookup cEnv1.v (Short (ps2cs v))’
              by simp[Abbr‘Env1’] >> simp[] >>
            drule_all_then (qx_choose_then ‘cv’ strip_assume_tac)
                           nsLookup_cpEval_valid >> simp[] >>
            drule_then (qspec_then ‘data’ $ qx_choose_then ‘dv’ $
                        strip_assume_tac)
                       nsLookup_build_rec_env_drop >> rfs[] >>
            drule_all_then
             (qspec_then ‘empty_state with refs := refs0’ $
              qx_choosel_then [‘dcs_env’, ‘dcs_e’, ‘dcs_cl1’, ‘dcs_cl2’,
                               ‘dcs_refs’, ‘dcs_v’] strip_assume_tac)
             (SIMP_RULE (srw_ss()) [PULL_EXISTS] do_opapp_translate
              |> INST_TYPE [“:'ffi” |-> “:unit”]) >>
            Q.REFINE_EXISTS_TAC ‘dcs_cl1 + (mc + 1)’ >>
            simp[dec_clock_with_clock] >>
            pop_assum kall_tac >>
            ‘NUM m (Litv (IntLit (&m)))’ by simp[NUM_def, INT_def] >>
            drule_all_then
             (qspec_then ‘empty_state with refs := refs0 ++ dcs_refs’ $
              qx_choosel_then [‘alld_env’, ‘alld_e’, ‘alld_cl1’, ‘alld_cl2’,
                               ‘alld_refs’, ‘alld_v’] strip_assume_tac)
             (SIMP_RULE (srw_ss()) [PULL_EXISTS] do_opapp_translate
              |> INST_TYPE [“:'ffi” |-> “:unit”]) >> simp[] >>
            Q.REFINE_EXISTS_TAC ‘alld_cl1 + (mc + 1)’ >> simp[] >> fs[] >>
            simp[state_component_equality]) >>
      ‘nsLookup Env1 (Short "sendloop") =
       SOME (Recclosure cEnv1 (sendloop conf data) "sendloop")’
        by simp[Abbr‘Env1’, build_rec_env_def, sendloop_def] >>
      first_assum (qspec_then ‘n’ assume_tac) >>
      first_x_assum (mp_then (Pos (el 4)) mp_tac
                     (sendloop_correct
                      |> INST_TYPE [alpha |-> cp_type])) >>
      simp[] >>
      disch_then (qspecl_then [‘conf’, ‘cSt1’] mp_tac) >>
      ‘cSt1.ffi.oracle = comms_ffi_oracle conf’
        by fs[cpEval_valid_def] >>
      simp[Abbr‘data’] >>
      disch_then (qspecl_then [‘valid_send_dest p2’, ‘p2’] mp_tac) >>
      simp[send_invariant] >> impl_tac
      >- (drule strans_dest_check' >> fs[cpEval_valid_def]) >>
      disch_then (qx_choosel_then [‘ck1’, ‘ck2’, ‘refs’] strip_assume_tac) >>
      Q.REFINE_EXISTS_TAC ‘ck1 + mc’ >>
      dxrule evaluate_add_to_clock >> simp[] >> disch_then kall_tac >>

      first_assum (qspec_then ‘n + conf.payload_size’ assume_tac) >>
      first_x_assum (mp_then (Pos (el 4)) mp_tac
                     (sendloop_correct
                      |> INST_TYPE [alpha |-> cp_type])) >>
      simp[] >>
      disch_then (qspecl_then [‘conf’, ‘cSt2’] mp_tac) >>
      ‘cSt2.ffi.oracle = comms_ffi_oracle conf’
        by fs[cpEval_valid_def] >>
      disch_then (qspecl_then [‘valid_send_dest p2’, ‘p2’] mp_tac) >>
      simp[send_invariant] >> impl_tac
      >- (drule strans_dest_check' >> fs[cpEval_valid_def]) >>
      disch_then (qx_choosel_then [‘ck0’, ‘ck3’, ‘refs2’] strip_assume_tac) >>
      Q.REFINE_EXISTS_TAC ‘ck0 + mc’ >>
      dxrule evaluate_add_to_clock >> simp[] >> disch_then kall_tac >>
      drule_all_then assume_tac cpEval_valid_Send_strans_E >>
      goal_assum drule >>
      MAP_EVERY RM_ABBREV_TAC ["aexpf", "Env1"] >>
      qpat_x_assum ‘nsLookup _ _ = _’ kall_tac >>
      qpat_abbrev_tac ‘FFI1 = _.ffi with <| ffi_state := _; io_events := _|>’ >>
      qmatch_goalsub_abbrev_tac
        ‘cSt2 with <| clock := _ ; refs := _ ; ffi := FFI2 |>’ >>
      ‘cpEval_valid conf p cEnv1 pSt1 e vs1
        (cSt2 with <| ffi := FFI2; refs := cSt2.refs ++ refs2|>)’
        by (fs[cpEval_valid_def] >> simp[Abbr‘FFI2’] >> conj_tac
            >- (irule ffi_state_cor_send_events_irrel >> simp[] >>
                qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
                metis_tac[strans_dest_check']) >>
            irule ffi_wf_send_events_irrel >> simp[] >>
            qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
            metis_tac[strans_dest_check']) >>
      ‘cpEval_valid conf p cEnv1 pSt1 e vs1
        (cSt1 with <| ffi := FFI1 ; refs := cSt1.refs ++ refs|>)’
        by (fs[cpEval_valid_def] >> simp[Abbr‘FFI1’] >>
            conj_tac
            >- (irule ffi_state_cor_send_events_irrel >> simp[] >>
                qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
                irule strans_dest_check >> metis_tac[]) >>
            irule ffi_wf_send_events_irrel >> simp[] >>
            qexists_tac ‘valid_send_dest p2’ >> simp[send_invariant] >>
            irule strans_dest_check >> metis_tac[]) >>
      pop_assum (mp_then (Pos hd) drule ffi_irrel) >>
      ‘0 < conf.payload_size’ by fs[cpEval_valid_def] >> impl_tac
      >- (simp[Abbr‘FFI1’, Abbr‘FFI2’] >>
          simp[send_events_def] >>
          simp[SimpL “ffi_eq conf”, Once compile_message_def] >>
          simp[DROP_DROP_T] >>
          ‘¬final (pad conf (DROP n d))’ by simp[final_def, pad_def] >>
          simp[update_state_def] >> SELECT_ELIM_TAC >> conj_tac
          >- (simp[comms_ffi_oracle_def, ffi_send_def] >>
              simp[pad_def] >> DEEP_INTRO_TAC some_intro >> simp[] >>
              qpat_x_assum ‘strans _ _ _ _’ mp_tac >>
              simp[pad_def] >> metis_tac[]) >>
          qx_gen_tac ‘cSt’ >> simp[comms_ffi_oracle_def, ffi_send_def] >>
          simp[AllCaseEqs()] >> DEEP_INTRO_TAC some_intro >> simp[] >>
          rpt strip_tac >>
          irule ffi_eq_send_stream_irrel >> rw[]
          >- (fs[cpEval_valid_def] >> metis_tac[strans_pres_wf])
          >- (qexistsl_tac [‘valid_send_dest p2’, ‘p2’] >> rw[]
              >- metis_tac[strans_dest_check']
              >- metis_tac[strans_dest_check']
              >- simp[GSYM send_events_def, send_events_is_stream] >>
              simp[send_invariant]) >>
          irule ffi_eq_pres >>
          goal_assum (first_assum o mp_then (Pos last) mp_tac) >>
          goal_assum (first_assum o mp_then (Pos last) mp_tac) >>
          simp[] >> fs[cpEval_valid_def]) >>
      disch_then (qx_choose_then ‘MC’ assume_tac) >>
      qexists_tac ‘MC’ >> dxrule cEval_equiv_bump_clocks >> simp[])
  >- ((* LReceive *)
      fs[cpFFI_valid_def, GREATER_DEF] >>
      CONV_TAC SWAP_VARS_CONV >> qexists_tac ‘vs1’ >>
      CONV_TAC SWAP_VARS_CONV >> qexists_tac ‘cEnv1’ >>
      simp[RIGHT_EXISTS_AND_THM] >> conj_asm1_tac
      >- (fs[cpEval_valid_def] >>
          rename [‘qpush _ sp msg’] >>
          ‘(∃p1 q1 n1. cSt1.ffi.ffi_state = (p1,q1,n1)) ∧
           (∃p2 q2 n2. cSt2.ffi.ffi_state = (p2,q2,n2))’
            by metis_tac[TypeBase.nchotomy_of “:α#β”] >> fs[] >> rw[] >>
          fs[ffi_state_cor_def] >> cheat) >>
      irule ffi_irrel >> cheat)
  >> cheat
QED

Theorem NPar_trans_l_cases_full:
  ∀p s c s' c' conf n n'.
   trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n')
   ⇒ (s = s' ∧ c = c') ∨
     ∃L. trans conf (NEndpoint p s c) L (NEndpoint p s' c') ∧
         ((n' = n ∧ L = LTau) ∨
          (∃q d. trans conf n (LReceive p d q) n' ∧ L = LSend p d q) ∨
          (∃q d. trans conf n (LSend q d p) n'    ∧ L = LReceive q d p))
Proof
  rw []
  \\ qpat_x_assum `trans _ _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw []
  >- (disj2_tac \\ asm_exists_tac \\ fs []
      \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                      (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
      \\ rw [] \\ metis_tac [])
  >- (disj2_tac \\ asm_exists_tac \\ fs []
      \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                      (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
      \\ rw [] \\ metis_tac [])
  \\ metis_tac []
QED

Theorem NPar_trans_l_cases:
  ∀p s c s' c' conf n n'.
   trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n')
   ⇒ (s = s' ∧ c = c') ∨ ∃L. trans conf (NEndpoint p s c) L (NEndpoint p s' c')
Proof
  metis_tac [NPar_trans_l_cases_full]
QED

Theorem NPar_trans_r_cases:
  ∀conf n n' l l'.
   trans conf (NPar l n) LTau (NPar l' n')
   ⇒ (n = n') ∨ ∃L. trans conf n L n'
Proof
  rw []
  \\ qpat_x_assum `trans _ _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw []
  \\ metis_tac []
QED

Theorem trans_not_same:
  ∀conf n1 l n2 . trans conf n1 l n2 ∧ conf.payload_size > 0 ⇒ n1 ≠ n2
Proof
  rpt gen_tac \\ strip_tac
  \\ rpt (pop_assum mp_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘n2’,‘l’,‘n1’,‘conf’]
  \\ ho_match_mp_tac trans_strongind \\ rw []
  >- (Induct_on ‘e’ \\ rw [] \\ metis_tac [])
  >- rw [payloadLangTheory.state_component_equality]
  >- (disj2_tac \\ Induct_on ‘e’ \\ rw [] \\ metis_tac [])
  >- (Induct_on ‘e1’ \\ rw [] \\ metis_tac [])
  >- (Induct_on ‘e2’ \\ rw [] \\ metis_tac [])
  \\  disj2_tac \\ Induct_on ‘e’ \\ rw [] \\ metis_tac []
QED

Theorem trans_ffi_eq_same:
  ∀p s c l conf n n'.
   ffi_wf (p,s,n) ∧
   conf.payload_size > 0 ∧
   trans conf (NPar (NEndpoint p s c) n ) LTau
              (NPar (NEndpoint p s c) n')
   ⇒ ffi_eq conf (p,s.queues,n) (p,s.queues,n')
Proof
  rw []
  \\ irule internal_trans_equiv_irrel
  \\ fs [ffi_wf_def]
  \\ irule RTC_SINGLE
  \\ fs [internal_trans_def]
  \\ ntac 2 (last_x_assum (K ALL_TAC))
  \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [trans_cases]) \\ fs []
  \\ IMP_RES_TAC trans_not_same \\ rw [] \\ fs []
QED

Theorem network_NPar_forward_correctness:
  ∀conf s c n p s' c' n' st1 vs1 env1 st2.
  trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n') ∧

  (* These assumptions should be dischargable by the static part of the compiler *)
  net_wf n ∧ (* equivalent to ALL_DISTINCT(MAP FST(endpoints n)) *)
  ~net_has_node n p ∧
  normalised s.queues ∧
  conf.payload_size > 0 ∧
  st1.ffi.oracle = comms_ffi_oracle conf ∧
  st1.ffi.ffi_state = (p,s.queues,n) ∧
  st2.ffi.oracle = comms_ffi_oracle conf ∧
  st2.ffi.ffi_state = (p,s'.queues,n') ∧
  pSt_pCd_corr s c ∧

  (* These assumptions can only be discharged by the dynamic part of the compiler *)
  sem_env_cor conf s env1 ∧
  enc_ok conf env1 (letfuns c) vs1
  ⇒
  ∃mc env2 vs2.
    sem_env_cor conf s' env2 ∧
    enc_ok conf env2 (letfuns c') vs2 ∧
    cEval_equiv conf
      (evaluate (st1 with clock := mc) env1
                      [compile_endpoint conf vs1 c])
      (evaluate (st2 with clock := mc) env2
                      [compile_endpoint conf vs2 c'])
Proof
  rw []
  \\ drule_then assume_tac NPar_trans_l_cases_full
  \\ fs [] \\ rveq
  (* p is not involved at all *)
  >- (CONV_TAC SWAP_EXISTS_CONV
      \\ asm_exists_tac \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ irule ffi_irrel \\ fs []
      \\ conj_tac
      >- metis_tac [ffi_wf_def,trans_ffi_eq_same]
      \\ MAP_EVERY qexists_tac [‘p’,‘s’]
      \\ rw [cpEval_valid_def,ffi_state_cor_def]
      \\ fs [sem_env_cor_def]
      >- rw [ffi_wf_def]
      \\ irule internal_trans_pres_wf
      \\ MAP_EVERY qexists_tac [‘n’,‘conf’,‘s.queues’]
      \\ rw [ffi_wf_def] \\ irule RTC_SINGLE
      \\ rw [comms_ffi_consTheory.internal_trans_def]
      \\ last_x_assum (assume_tac o ONCE_REWRITE_RULE [trans_cases]) \\ fs []
      \\ IMP_RES_TAC trans_not_same \\ rw [] \\ fs [])
  (* LTau (only p does something) *)
  >- (drule_then (qspecl_then [‘vs1’,‘env1’,‘st1’,‘st2’] mp_tac) endpoint_forward_correctness
      \\ impl_tac
      >- (rw [cpEval_valid_def,ffi_wf_def,
              ffi_state_cor_def,
              cpFFI_valid_def,some_def]
          \\ fs [] >- fs [sem_env_cor_def]
          >- (drule payload_trans_normalised
              \\ rw [normalised_network_def,normalised_def]
              \\ SELECT_ELIM_TAC \\ rw []
              >- (asm_exists_tac \\ fs [])
              \\ qpat_x_assum ‘_ x’ (K ALL_TAC)
              \\ Cases_on ‘x'’ \\ fs []
              \\ qpat_assum ‘s.queues = _’ (ONCE_REWRITE_TAC o single o GSYM)
              \\ first_assum (mp_then Any mp_tac normalise_queues_dequeue_eq)
              \\ impl_tac >- rw [normalised_def]
              \\ disch_then (ONCE_REWRITE_TAC o single)
              \\ irule (CONJUNCTS strans_rules |> hd)
              \\ fs [qlk_normalise_queues])
          \\ qpat_assum `trans _ (NEndpoint _ _ _) _ _`
                          (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
          \\ fs [] \\ rw []
          \\ fs [state_component_equality] \\ rveq \\ rfs [state_component_equality]
          >- (first_x_assum (qspec_then ‘(p1,d)’ assume_tac) \\ fs []
              \\ fs [normalise_queues_FUPDATE_NONEMPTY]
              \\ first_assum (fn t => reverse (sg ‘¬ ^(concl t)’))
              \\ pop_assum (K ALL_TAC)
              \\ fs [normalised_def]
              \\ ONCE_REWRITE_TAC [GSYM fmap_EQ_THM]
              \\ fs [qlk_def,fget_def]
              \\ EVERY_CASE_TAC
              \\ fs [] \\ rveq \\ rw [FAPPLY_FUPDATE_THM]
              \\ fs [FLOOKUP_DEF,ABSORPTION_RWT])
          >- (first_x_assum (qspec_then ‘(p1,d)’ assume_tac) \\ fs []
              \\ fs [normalise_queues_FUPDATE_NONEMPTY]
              \\ first_assum (fn t => reverse (sg ‘¬ ^(concl t)’))
              \\ pop_assum (K ALL_TAC)
              \\ fs [normalised_def]
              \\ ONCE_REWRITE_TAC [GSYM fmap_EQ_THM]
              \\ fs [qlk_def,fget_def]
              \\ EVERY_CASE_TAC
              \\ fs [] \\ rveq \\ rw [FAPPLY_FUPDATE_THM]
              \\ fs [FLOOKUP_DEF,ABSORPTION_RWT])
          \\ irule qsame_irrel_ffi_eq \\ fs [qsame_def])
       \\ rw []
       \\ MAP_EVERY qexists_tac [‘mc’,‘cEnv2’,‘vs2’]
       \\ fs [cpFFI_valid_def,cpEval_valid_def,ffi_state_cor_def])
   (* LSend *)
  >- (drule_then (qspecl_then [‘vs1’,‘env1’,‘st1’,‘st2’] mp_tac) endpoint_forward_correctness
      \\ impl_tac
      >- (rw [cpEval_valid_def,ffi_wf_def,ffi_state_cor_def,cpFFI_valid_def]
          >- fs [sem_env_cor_def]
          \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                          (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
          \\ fs [] \\ rw []
          \\ metis_tac [strans_rules])
      \\ rw []
      \\ MAP_EVERY qexists_tac [‘mc’,‘cEnv2’,‘vs2’]
      \\ fs [cpFFI_valid_def,cpEval_valid_def,ffi_state_cor_def])
  \\ drule_then (qspecl_then [‘vs1’,‘env1’,‘st1’,‘st2’] mp_tac) endpoint_forward_correctness
  \\ impl_tac
  (* LReceive *)
  >- (rw [cpEval_valid_def,ffi_wf_def,ffi_state_cor_def,cpFFI_valid_def]
      >- fs [sem_env_cor_def]
      \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                      (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
      \\ fs [] \\ rw []
      \\ irule active_trans_equiv_irrel
      \\ fs [ffi_wf_def]
      \\ irule RTC_SINGLE
      \\ fs [comms_ffi_consTheory.active_trans_def]
      \\ disj2_tac \\ fs [comms_ffi_consTheory.emit_trans_def])
  \\ rw []
  \\ MAP_EVERY qexists_tac [‘mc’,‘cEnv2’,‘vs2’]
  \\ fs [cpFFI_valid_def,cpEval_valid_def,ffi_state_cor_def]
QED

Theorem network_NPar_forward_correctness_reduction:
  ∀conf p s c n s' c' n' st1 vs1 env1 st2.
  (reduction conf)⃰ (NPar (NEndpoint p s c) n) (NPar (NEndpoint p s' c') n') ∧

  (* These assumptions should be dischargable by the static part of the compiler *)
  net_wf n ∧
  ~net_has_node n p ∧
  conf.payload_size > 0 ∧
  normalised s.queues ∧
  st1.ffi.oracle = comms_ffi_oracle conf ∧
  st1.ffi.ffi_state = (p,s.queues,n) ∧
  st2.ffi.oracle = comms_ffi_oracle conf ∧
  st2.ffi.ffi_state = (p,s'.queues,n') ∧
  pSt_pCd_corr s c ∧

  (* These assumptions can only be discharged by the dynamic part of the compiler *)
  sem_env_cor conf s env1 ∧
  enc_ok conf env1 (letfuns c) vs1
  ⇒
  ∃mc env2 vs2.
    sem_env_cor conf s' env2 ∧
    enc_ok conf env2 (letfuns c') vs2 ∧
    cEval_equiv conf
      (evaluate (st1 with clock := mc) env1
                      [compile_endpoint conf vs1 c])
      (evaluate (st2 with clock := mc) env2
                      [compile_endpoint conf vs2 c'])
Proof
  strip_tac
  \\ ‘conf.payload_size > 0
      ⇒ ∀n1 n2. (reduction conf)⃰ n1 n2
         ⇒ ∀p s c n p s' c' n' st1 vs1 env1 st2.
            n1 = (NPar (NEndpoint p s  c)  n)  ∧
            n2 = (NPar (NEndpoint p s' c') n') ∧
            net_wf n ∧  ~net_has_node n p ∧
            st1.ffi.oracle = comms_ffi_oracle conf ∧
            st1.ffi.ffi_state = (p,s.queues,n) ∧
            st2.ffi.oracle = comms_ffi_oracle conf ∧
            st2.ffi.ffi_state = (p,s'.queues,n') ∧
            pSt_pCd_corr s c ∧ normalised s.queues ∧
            sem_env_cor conf s env1 ∧
            enc_ok conf env1 (letfuns c) vs1
            ⇒
            ∃mc env2 vs2.
              sem_env_cor conf s' env2 ∧
              enc_ok conf env2 (letfuns c') vs2 ∧
              cEval_equiv conf
                (evaluate (st1 with clock := mc) env1
                                [compile_endpoint conf vs1 c])
                (evaluate (st2 with clock := mc) env2
                                [compile_endpoint conf vs2 c'])’
    suffices_by metis_tac []
  \\ strip_tac
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw []
  >- (CONV_TAC SWAP_VARS_CONV \\  qexists_tac ‘env1’
      \\ CONV_TAC SWAP_VARS_CONV \\  qexists_tac ‘vs1’
      \\ fs [] \\ irule ffi_irrel
      \\ qspec_then ‘conf’ assume_tac ffi_eq_equivRel
      \\ fs [equivalence_def,reflexive_def]
      \\ map_every qexists_tac [‘p’,‘s’]
      \\ fs [cpEval_valid_def,ffi_wf_def,ffi_state_cor_def,sem_env_cor_def])
  \\ ‘∃s'' c'' n''. n1' = NPar (NEndpoint p s'' c'' ) n''’
      by (fs [reduction_def,Once trans_cases]
          \\ fs [Once trans_cases])
  \\ rveq \\ fs [reduction_def]
  \\ drule network_NPar_forward_correctness \\ fs []
  \\ disch_then (qspecl_then [‘st1’,‘vs1’,‘env1’,
                              ‘st1 with ffi :=
                                   (st1.ffi with ffi_state
                                            := (p,s''.queues,n''))’]
                             mp_tac)
  \\ qpat_abbrev_tac ‘st1' = st1 with ffi := _’
  \\ impl_tac >- fs [Abbr‘st1'’]
  \\ rw []
  \\ ‘∀q. ffi_wf (p,q,n'')’
    by (drule NPar_trans_r_cases \\ rw []
        >- fs [ffi_wf_def]
        \\ drule_then irule trans_pres_ffi_wf
        \\ fs [ffi_wf_def])
  \\ fs [ffi_wf_def]
  \\ first_x_assum (qspecl_then [‘st1'’,‘vs2’,‘env2’,‘st2’] mp_tac)
  \\ impl_tac
  >- (fs [Abbr‘st1'’]
      \\ drule NPar_trans_l_cases
      \\ rw [] \\ fs []
      >- metis_tac [trans_pSt_pCd_corr_pres]
      \\ drule payload_trans_normalised
      \\ rw [normalised_network_def,normalised_def])
  \\ rw []
  \\ CONV_TAC SWAP_VARS_CONV \\  qexists_tac ‘env2'’
  \\ CONV_TAC SWAP_VARS_CONV \\  qexists_tac ‘vs2'’
  \\ fs []
  \\ pop_assum (mp_then Any (qspecl_then [‘mc’,‘mc’] mp_tac) clock_irrel)
  \\ drule_then (qspecl_then [‘mc'’,‘mc'’] assume_tac) clock_irrel
  \\ disch_then assume_tac
  \\ qexists_tac ‘mc + mc'’
  \\ fs []
  \\ metis_tac [cEval_equiv_trans]
QED

Theorem network_forward_correctness:
  ∀conf p s c n p s' c' n' np np' st1 vs1 env1 st2.
  trans conf n LTau n' ∧
  (* These assumptions should be dischargable by the static part of the compiler *)
  REPN n ∧
  net_wf n ∧
  normalised_network n ∧
  conf.payload_size > 0 ∧
  net_has_node n p ∧
  net_find p n  = SOME (NEndpoint p s  c ) ∧
  net_find p n' = SOME (NEndpoint p s' c') ∧
  st1.ffi.oracle = comms_ffi_oracle conf ∧
  st1.ffi.ffi_state = (p,s.queues,net_filter p n) ∧
  st2.ffi.oracle = comms_ffi_oracle conf ∧
  st2.ffi.ffi_state = (p,s'.queues,net_filter p n') ∧
  pSt_pCd_corr s c ∧
  sem_env_cor conf s env1 ∧
  enc_ok conf env1 (letfuns c) vs1
  ⇒
  ∃mc env2 vs2.
    sem_env_cor conf s' env2 ∧
    enc_ok conf env2 (letfuns c') vs2 ∧
    cEval_equiv conf
      (evaluate (st1 with clock := mc) env1
                      [compile_endpoint conf vs1 c])
      (evaluate (st2 with clock := mc) env2
                      [compile_endpoint conf vs2 c'])
Proof
  rw []
  \\ irule network_NPar_forward_correctness
  \\ fs [] \\ qexists_tac ‘s’
  \\ rw []
  >- (drule_all payload_trans_normalised
      \\ drule_all  normalised_network_net_find_filter
      \\ rw [normalised_network_def])
  >- fs [net_wf_filter]
  >- fs [not_net_has_node_net_filter]
  \\ drule_then (qspec_then ‘p’ mp_tac) net_find_filter_trans
  \\ impl_tac >- fs [net_has_node_IS_SOME_net_find]
  \\ rw []
QED

val _ = export_theory ();

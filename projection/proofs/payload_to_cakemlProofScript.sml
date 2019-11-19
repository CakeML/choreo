open preamble;
open optionTheory
     rich_listTheory;
open payloadLangTheory payloadSemanticsTheory payload_to_cakemlTheory;
open comms_ffi_modelTheory
     comms_ffi_propsTheory
     comms_ffi_eqTheory;
open evaluate_toolsTheory
     ckExp_EquivTheory;
open evaluate_rwLib
     state_tacticLib;
open evaluateTheory terminationTheory ml_translatorTheory
     ml_progTheory evaluatePropsTheory namespaceTheory
     semanticPrimitivesTheory ffiTheory;

val _ = new_theory "payload_to_cakemlProof";

val WORD8 = “WORD:word8 -> v -> bool”;
val DATUM = “LIST_TYPE ^WORD8”;

(* ENVIRONMENT CHECK
  - Originally made by others, modified by me (env_asm changes)*)
(* General check environment has something defined with property *)
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
    in_module conf.nil ∧
    in_module conf.cons ∧
    in_module conf.append ∧
    in_module conf.concat ∧
    in_module conf.length ∧
    in_module conf.null ∧
    in_module conf.take ∧
    in_module conf.drop ∧
    in_module conf.fromList ∧
    in_module conf.toList)
End

(* LUPDATE (List Update) HELPER THEOREMS
   - Written by others *)
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

(* FFI MANIPULATION HELPERS
   -- Written by Others *)
(* Construct list of chunks from desired data to send *)
Definition compile_message_def:
  compile_message conf d =
   if conf.payload_size = 0 then [] (*for termination, shouldn't happen*)
   else
     if final(pad conf d) then
       [pad conf d]
     else pad conf d :: compile_message conf (DROP conf.payload_size d)
Termination
  wf_rel_tac ‘inv_image ($<) (λ(conf,d). if conf.payload_size = 0 then 0 else LENGTH d)’ >>
  rpt strip_tac >>
  fs[LENGTH_DROP,final_def,pad_def] >>
  every_case_tac >> fs[final_def]
End
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

(* SENDLOOP CORRECTNESS
   -- Written by others with some
      modifications I have written.
      (sendloop_correct now uses ck_equiv_hol
       instead of basic translation *)
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
  pFv (Receive _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (IfThen fv npCd1 npCd2) = fv INSERT pFv npCd1 ∪ pFv npCd2 ∧
  pFv (Let bv _ fvs npCd) = (pFv npCd DELETE bv) ∪ set fvs
End

Definition pSt_pCd_corr_def:
  pSt_pCd_corr (pSt :payloadLang$state) pCd ⇔ ∀vn. vn ∈ pFv pCd
                              ⇒ ∃vv. FLOOKUP pSt.bindings vn = SOME vv
End

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
  ffi_state_cor cpNum pSt (fNum,fQueue,fNet) ⇔
    cpNum = fNum ∧
    ∀sp.
      isPREFIX (qlk pSt.queues sp) (qlk fQueue sp)
End

(* Combined *)
Definition cpEval_valid_def:
  cpEval_valid conf cpNum cEnv pSt pCd vs cSt ⇔
    conf.payload_size ≠ 0 ∧
    env_asm cEnv conf ∧
    enc_ok conf cEnv (letfuns pCd) vs ∧
    pSt_pCd_corr pSt pCd ∧
    sem_env_cor conf pSt cEnv ∧
    ffi_state_cor cpNum pSt cSt.ffi.ffi_state ∧
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
              pSt1.queues = pSt2.queues |+ (sp,d::qlk pSt2.queues sp)) of
        SOME (sp,d) => strans conf ffi1 (ARecv sp d) ffi2
      | NONE        => ffi_eq conf ffi1 ffi2)
End

(* CAKEML EQUIVALENCE *)
(* Basic Definition *)
Definition cEval_equiv_def:
  cEval_equiv conf (csA,crA) (csB,crB) ⇔
    ffi_eq conf csA.ffi.ffi_state csB.ffi.ffi_state ∧
    crA = crB ∧
    crA ≠ Rerr (Rabort Rtimeout_error)
End
(* Irrelevance of extra time/fuel to equivalence *)
Theorem clock_irrel:
  ∀ conf cSt1 cSt2 cEnv cExps.
    ∀mc eck1 eck2.    
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) cEnv cExps)
        (evaluate (cSt2 with clock := mc) cEnv cExps)
    ⇒ cEval_equiv conf
        (evaluate (cSt1 with clock := eck1 + mc) cEnv cExps)
        (evaluate (cSt2 with clock := eck2 + mc) cEnv cExps)
Proof
  rpt strip_tac >>
  Cases_on ‘evaluate (cSt1 with clock := mc) cEnv cExps’ >>
  Cases_on ‘evaluate (cSt2 with clock := mc) cEnv cExps’ >>
  fs[cEval_equiv_def] >>
  ‘evaluate (cSt1 with clock := eck1 + mc) cEnv cExps
    = (q with clock := eck1 + q.clock,r)’
    by (Q.ISPECL_THEN [‘(cSt1 with clock := mc)’,‘cEnv’, ‘cExps’,‘q’,‘r’,‘eck1’]
                      assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  ‘evaluate (cSt2 with clock := eck2 + mc) cEnv cExps
    = (q' with clock := eck2 + q'.clock,r')’
    by (Q.ISPECL_THEN [‘(cSt2 with clock := mc)’,‘cEnv’, ‘cExps’,‘q'’,‘r'’,‘eck2’]
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
    ffi_state_cor cpNum pSt ckFSt ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor cpNum pSt (update_state ckFSt (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_state_cor cpNum pSt (update_state ckFSt1 _ send_stream)’ >>
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
  qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ ckFSt1’ >>
  rw[]
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> fs[]) >>
  fs[ffi_accepts_rel_def,valid_send_event_format_def] >>
  rfs[] >>
  qpat_x_assum ‘∀a b c d. e’ (K ALL_TAC) >>
  fs[comms_ffi_oracle_def] >>
  ‘s = "send"’
    by fs[valid_send_call_format_def] >>
  fs[ffi_send_def] >> first_x_assum (K ALL_TAC) >>
  Cases_on ‘∃ns. strans conf ckFSt (ASend l (MAP SND d)) ns’ >>
  Cases_on ‘LENGTH d = SUC conf.payload_size’ >>
  fs[some_def] >> rw[] >>
  irule SELECT_ELIM_THM >>
  rw[]
  >- (qpat_x_assum ‘strans _ _ _ ns’ (K ALL_TAC) >>
      qmatch_goalsub_rename_tac ‘ffi_state_cor _  _ ns’ >>
      Cases_on ‘ns’ >> Cases_on ‘ckFSt’ >>
      rename1 ‘strans conf (PN,R) _ (PN',R')’ >>
      ‘PN' = PN’
        by (drule strans_pres_pnum >>
            simp[]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘PN = cpNum’
        by (Cases_on ‘R’ >>
            fs[ffi_state_cor_def]) >>
      fs[] >>
      first_x_assum (K ALL_TAC) >>
      Cases_on ‘R’ >> Cases_on ‘R'’ >>
      rename1 ‘strans conf (_,Q,N) _ (_,Q',N')’ >>
      ‘∀sp.
        isPREFIX (qlk Q sp) (qlk Q' sp)’
        suffices_by (rw[] >> fs[ffi_state_cor_def] >>
                     rw[] >> metis_tac[IS_PREFIX_TRANS]) >>
      metis_tac[strans_queue_pres])
  >- (qexists_tac ‘ns’ >> simp[])
QED
(* send_events cannot break FFI correspondence*)
Theorem ffi_state_cor_send_events_irrel:
  ∀conf cpNum pSt ckFSt l d P.
    ffi_state_cor cpNum pSt ckFSt ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor cpNum pSt (update_state ckFSt (comms_ffi_oracle conf)
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
      ‘ck_equiv_hol cEnv NUM (App Opapp [Var conf.length; Var (Short (ps2cs s))]) (LENGTH ha_s)’
        by (irule ck_equiv_hol_App >>
            qexists_tac ‘^DATUM’ >>
            rw[] >>irule ck_equiv_hol_Var
            >> fs[cpEval_valid_def,env_asm_def,has_v_def,sem_env_cor_def]) >>
      drule_then (qspec_then ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt2 with clock := bc1_2 + dc) cEnv
                  [App Opapp [Var conf.length; Var (Short (ps2cs s))]] =
                (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefs_2|>,
                 Rval [cV_2])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      drule_then (qspec_then ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt1 with clock := bc1_1 + dc) cEnv
                  [App Opapp [Var conf.length; Var (Short (ps2cs s))]] =
                (cSt1 with <|clock := dc + bc2_1; refs := cSt1.refs ++ drefs_1|>,
                 Rval [cV_1])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      fs trans_sl >>
      ntac 3 (first_x_assum (K ALL_TAC)) >>
      unite_nums "dc1" >>
      unite_nums "dc2" >>
      (* BEGIN: DISPOSE REFS CHANGE *)
      qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefs_1’ >>
      qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefs_2’ >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
        by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
        by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
      ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
        by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
      qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt1A = cSt1 with refs := (cSt1).refs ++ drefs_1)’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt2A = cSt2 with refs := (cSt2).refs ++ drefs_2)’ (K ALL_TAC) >>
      rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’ >>
      (* END: DISPOSE REFS CHANGE *)
      rw eval_sl_nf
      >- (last_x_assum (qspecl_then [‘conf’,‘cpNum’,‘cEnv’,
                                    ‘pSt’,‘vs’,‘cSt1’,‘cSt2’]
                                  assume_tac) >>
          rfs[cpEval_valid_def,letfuns_def] >>
          ‘pSt_pCd_corr pSt pCd’
            by fs[pSt_pCd_corr_def,Once pFv_def] >>
          fs[] >>
          qexists_tac ‘mc’ >>
          qspecl_then [‘conf’,‘cSt1’, ‘cSt2’, ‘cEnv’,
                       ‘[compile_endpoint conf vs pCd]’,
                       ‘mc’, ‘dc1’, ‘dc2’]
                      assume_tac clock_irrel >>
          rfs[] >>
          rw[])
      >- (fs[] >>
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
              unite_nums "dc1" >>
              unite_nums "dc2" >>
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
              fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
              qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              simp[nsOptBind_def] >>
              qmatch_goalsub_abbrev_tac ‘∃mc. cEval_equiv conf
                                        (evaluate (cSt1M with clock := dc1 + mc) cEnv _)
                                        (evaluate (cSt2M with clock := dc2 + mc) cEnv _)’ >>
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
                suffices_by (rw[] >> fs[] >> metis_tac[clock_irrel]) >>
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
              qexists_tac ‘valid_send_dest l’ >> simp[])
          >- (qpat_x_assum ‘valid_send_dest _ _ ⇒ _’ (K ALL_TAC) >>
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
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              drule_then (qspec_then ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
              rename [‘∀dc. evaluate (cSt2 with clock := bc1_2 + dc) cEnvBR _ =
                               (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefsD2|>,
                                Rval [cVD2])’] >>
              Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
              simp[] >>
              first_x_assum (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
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
          )
      >- (rw[cEval_equiv_def]))     
  >- ((* Receive Case *)
      cheat)
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
      ‘ffi_state_cor cpNum pStM cSt1M.ffi.ffi_state’
        by (‘ffi_state_cor cpNum pSt cSt1.ffi.ffi_state’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >> qunabbrev_tac ‘cSt1M’ >>
            simp[] >> Cases_on ‘cSt1.ffi.ffi_state’ >>
            qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ (P,R)’ >>
            Cases_on ‘R’ >> fs[ffi_state_cor_def]) >>
      ‘ffi_state_cor cpNum pStM cSt2M.ffi.ffi_state’
        by (‘ffi_state_cor cpNum pSt cSt2.ffi.ffi_state’
              by fs[cpEval_valid_def] >>
            qunabbrev_tac ‘pStM’ >> qunabbrev_tac ‘cSt2M’ >>
            simp[] >> Cases_on ‘cSt2.ffi.ffi_state’ >>
            qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ (P,R)’ >>
            Cases_on ‘R’ >> fs[ffi_state_cor_def]) >>
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

(* FORWARD CORRECTNESS
    Just the spec :) *)
Theorem forward_correctness:
  ∀conf p pSt1 pCd1 L pSt2 pCd2
        vs1 cEnv1 cSt1 vs2 cEnv2 cSt2.
    trans conf (NEndpoint p pSt1 pCd1) L (NEndpoint p pSt2 pCd2) ∧
    cpEval_valid conf p cEnv1 pSt1 pCd1 vs1 cSt1 ∧
    cpEval_valid conf p cEnv2 pSt2 pCd2 vs2 cSt2 ∧
    cpFFI_valid conf pSt1 pSt2 cSt1.ffi.ffi_state cSt2.ffi.ffi_state L ⇒
    ∃mc. cEval_equiv conf
          (evaluate (cSt1 with clock := mc) cEnv1
                    [compile_endpoint conf vs1 pCd1])
          (evaluate (cSt2 with clock := mc) cEnv2
                    [compile_endpoint conf vs2 pCd2])
Proof
  cheat
QED


val _ = export_theory ();
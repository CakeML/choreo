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
      qmatch_goalsub_abbrev_tac ‘evaluate (stCDL with clock := _) envCDL [convDatumList conf l]’ >>
      qspecl_then [‘envCDL’,‘conf’,‘l’] assume_tac convDatumList_corr >>
      ‘env_asm envCDL conf’
        by (qunabbrev_tac ‘envCDL’ >>
            ‘env_asm cEnv conf’
              by fs [cpEval_valid_def,sem_env_cor_def] >>
            pop_assum mp_tac >>
            rpt (pop_assum (K ALL_TAC)) >>
            rw[env_asm_def,has_v_def,receiveloop_def,in_module_def]) >>
      fs[] >>
      qspecl_then [‘envCDL’,‘LIST_TYPE ^DATUM’,‘convDatumList conf l’,‘l’,‘stCDL’]
                    assume_tac ck_equiv_hol_apply_alt >>
      rfs[] >>
      rename1
        ‘∀dc.
          evaluate (stCDL with clock := bc1 + dc) envCDL
            [convDatumList conf l] =
          (stCDL with <|clock := bc2 + dc; refs := stCDL.refs ++ drefs|>,
           Rval [cV])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      rename1 ‘receiveloop conf (MAP (CHR o w2n) src)’ >>
      MAP_EVERY qunabbrev_tac [‘stCDL’,‘envCDL’] >>
      ntac 2 (rw [Once evaluate_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stRL with clock := _) envRL [rec]’ >>
      reverse (Cases_on ‘∃msg. ffi_receives conf stRL.ffi src msg’)
      >- cheat >>
      fs[] >>
      qabbrev_tac ‘bufLoc = LENGTH cSt1.refs’ >>
      qabbrev_tac ‘IenvRL = cEnv with v := nsBind "buff" (Loc bufLoc) cEnv.v’ >>
      qspecl_then [‘conf’,‘msg’,‘envRL’,‘IenvRL’,‘stRL’,‘src’,
                   ‘bufLoc’,‘REPLICATE (conf.payload_size + 1) 0w’]
                  assume_tac
                  receiveloop_correct >>
      rfs[] >>
      ‘conf.payload_size ≠ 0’
        by fs[cpEval_valid_def] >>
      ‘nsLookup envRL.v (Short "receiveloop") =
        SOME
          (Recclosure IenvRL (receiveloop conf (MAP (CHR ∘ w2n) src))
             "receiveloop")’
        by (qunabbrev_tac ‘envRL’ >>
            rw (Abbr ‘IenvRL’::receiveloop_def::eval_sl)) >>
      ‘nsLookup IenvRL.v (Short "buff") = SOME (Loc bufLoc)’
        by rw (Abbr ‘IenvRL’::eval_sl) >>
      ‘store_lookup bufLoc stRL.refs =
        SOME (W8array (REPLICATE (conf.payload_size + 1) 0w))’
        by (rw (Abbr ‘stRL’::Abbr ‘bufLoc’::eval_sl) >>
            ‘cSt1.refs ++ [W8array (REPLICATE (conf.payload_size + 1) 0w)] ++
            drefs = cSt1.refs ++ ([W8array (REPLICATE (conf.payload_size + 1) 0w)]
            ++ drefs)’
              by rw[APPEND_ASSOC] >>
            pop_assum SUBST1_TAC >>
            rw[EL_LENGTH_APPEND,NULL_DEF]) >>
      ‘env_asm IenvRL conf’
        by (qunabbrev_tac ‘IenvRL’ >>
            ‘env_asm cEnv conf’
              suffices_by (rw[] >> fs[env_asm_def,has_v_def,in_module_def] >>
                           rfs[] >> metis_tac[EQ_SYM_EQ]) >>
            fs[cpEval_valid_def]) >>
      fs[] >>
      ntac 5 (pop_assum (K ALL_TAC)) >>
      rename1 ‘evaluate (stRL with clock := ack1) envRL [rec] =
              (stRL with <|clock := _; refs := LUPDATE bufFinl bufLoc stRL.refs ++ drefs2;
                           ffi:= _|>, Rval [ulvM])’ >>
      dxrule_then assume_tac evaluate_add_to_clock >>
      fs[] >>
      Q.REFINE_EXISTS_TAC ‘ack1 + ck1e’ >>
      simp[] >>
      rw[evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘nsLookup nsCNC conf.append’ >>
      ‘has_v nsCNC conf.append (LIST_TYPE ^DATUM --> LIST_TYPE ^DATUM --> LIST_TYPE ^DATUM) $++’
        by fs[env_asm_def,Abbr ‘nsCNC’,Abbr ‘envRL’] >>
      fs[has_v_def,Arrow_def,AppReturns_def] >>
      pop_assum (qspecl_then [‘MAP unpad (compile_message conf msg)’,‘ulvM’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘LUPDATE bufFinl bufLoc stRL.refs ++ drefs2’ strip_assume_tac) >>
      simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1e’ >> fs[dec_clock_def,eval_rel_def,ADD1] >>
      qunabbrev_tac ‘stRL’ >> qmatch_goalsub_abbrev_tac ‘evaluate (stC1 with clock := _) _ _’ >>
      rename1 ‘evaluate (empty_state with <|clock := ack1N; refs := _|>) envC1 [expC1] =
               (empty_state with <|clock := ack2N; refs := LUPDATE _ _ _ ++ drefs2 ++ drefs3|>,
                Rval [uC1])’ >>
      qspecl_then [‘stC1’,‘envC1’,‘expC1’,‘ack1N’,‘ack2N’,‘drefs3’,‘uC1’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := ack1N; refs := stC1.refs|>)
                envC1 [expC1] =
      (empty_state with <|clock := ack2N; refs := stC1.refs ++ drefs3|>,Rval[uC1])’
        by fs[Abbr ‘stC1’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘ack1N + ck1e’ >> simp[] >>
      pop_assum (K ALL_TAC) >>
      first_x_assum (qspecl_then [‘l’,‘cV’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘stC1.refs ++ drefs3’ strip_assume_tac) >>
      simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1e’ >> fs[dec_clock_def,eval_rel_def,ADD1] >>
      qunabbrev_tac ‘stC1’ >> qmatch_goalsub_abbrev_tac ‘evaluate (stC2 with clock := _) _ _’ >>
      rename1 ‘evaluate (empty_state with <|clock := aack1N; refs := _|>) envC2 [expC2] =
               (empty_state with <|clock := aack2N; refs := _ ++ drefs3 ++ drefs4|>,
                Rval [uC2])’ >>
      qspecl_then [‘stC2’,‘envC2’,‘expC2’,‘aack1N’,‘aack2N’,‘drefs4’,‘uC2’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := aack1N; refs := stC2.refs|>)
                envC2 [expC2] =
      (empty_state with <|clock := aack2N; refs := stC2.refs ++ drefs4|>,Rval[uC2])’
        by fs[Abbr ‘stC2’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘aack1N + ck1e’ >> simp[] >>
      ‘has_v nsCNC conf.concat (LIST_TYPE ^DATUM --> ^DATUM) FLAT’
        by fs[env_asm_def,Abbr ‘nsCNC’,Abbr ‘envRL’] >>
      fs[has_v_def,Arrow_def,AppReturns_def] >>
      pop_assum (qspecl_then [‘MAP unpad (compile_message conf msg) ++ l’,‘uC2’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘stC2.refs ++ drefs4’ strip_assume_tac) >>
      simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1e’ >> fs[dec_clock_def,eval_rel_def,ADD1] >>
      qunabbrev_tac ‘stC2’ >> qmatch_goalsub_abbrev_tac ‘evaluate (stC3 with clock := _) _ _’ >>
      fs[] >>
      rename1 ‘evaluate (empty_state with <|clock := aaack1N; refs := _|>) envC3 [expC3] =
               (empty_state with <|clock := aaack2N; refs := _ ++ drefs5|>,
                Rval [uC3])’ >>
      qspecl_then [‘stC3’,‘envC3’,‘expC3’,‘aaack1N’,‘aaack2N’,‘drefs5’,‘uC3’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := aaack1N; refs := stC3.refs|>)
                envC3 [expC3] =
      (empty_state with <|clock := aaack2N; refs := stC3.refs ++ drefs5|>,Rval[uC3])’
        by fs[Abbr ‘stC3’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘aaack1N + ck1e’ >> simp[] >>
      pop_assum (K ALL_TAC) >>
      (* Clean up proof state *)
      MAP_EVERY qunabbrev_tac [‘envRL’,‘bufLoc’,‘IenvRL’,‘nsCNC’,‘stC3’] >>
      ntac 3 (qpat_x_assum ‘∀x. _ ’ (K ALL_TAC)) >>
      qpat_x_assum ‘evaluate _ envC1 [expC1] = _’ (K ALL_TAC) >>
      qpat_x_assum ‘evaluate _ envC2 [expC2] = _’ (K ALL_TAC) >>
      qpat_x_assum ‘evaluate _ envC3 [expC3] = _’ (K ALL_TAC) >>
      rpt (qpat_x_assum ‘do_opapp _ = _’ (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘nsLookup _ _ = _’ (K ALL_TAC)) >>
      qpat_x_assum ‘LIST_TYPE ^DATUM _ cV’ (K ALL_TAC) >>
      qpat_x_assum ‘LIST_TYPE ^DATUM _ ulvM’ (K ALL_TAC) >>
      qpat_x_assum ‘LIST_TYPE ^DATUM _ uC2’ (K ALL_TAC) >>
      ‘ffi_receives conf cSt2.ffi src msg’
        by (‘ffi_receives conf cSt1.ffi = ffi_receives conf cSt2.ffi’
              suffices_by (rw[FUN_EQ_THM] >> metis_tac[]) >>
            irule ffi_eq_receives >>
            fs[cpEval_valid_def]) >>
      qpat_x_assum ‘ffi_receives _ cSt1.ffi _ _’ (K ALL_TAC) >>
      rename1 ‘_ + ack2O’ >> simp[] >> unite_nums "bocA" >> unite_nums "bocB" >>
      (* Evaluate Right Hand Side *)
      ntac 2 (rw[Once evaluate_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stCDL with clock := _) envCDL [convDatumList conf l]’ >>
      qspecl_then [‘envCDL’,‘conf’,‘l’] assume_tac convDatumList_corr >>
      ‘env_asm envCDL conf’
        by (qunabbrev_tac ‘envCDL’ >>
            ‘env_asm cEnv conf’
              by fs [cpEval_valid_def,sem_env_cor_def] >>
            pop_assum mp_tac >>
            rpt (pop_assum (K ALL_TAC)) >>
            rw[env_asm_def,has_v_def,receiveloop_def,in_module_def]) >>
      fs[] >>
      qspecl_then [‘envCDL’,‘LIST_TYPE ^DATUM’,‘convDatumList conf l’,‘l’,‘stCDL’]
                    assume_tac ck_equiv_hol_apply_alt >>
      rfs[] >>
      rename1
        ‘∀dc.
          evaluate (stCDL with clock := bc1 + dc) envCDL
            [convDatumList conf l] =
          (stCDL with <|clock := bc2 + dc; refs := stCDL.refs ++ drefsA|>,
           Rval [cV])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      rename1 ‘receiveloop conf (MAP (CHR o w2n) src)’ >>
      MAP_EVERY qunabbrev_tac [‘stCDL’,‘envCDL’] >>
      ntac 2 (rw [Once evaluate_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stRL with clock := _) envRL [rec]’ >>
      ‘ffi_receives conf stRL.ffi src msg’
        by fs[Abbr ‘stRL’] >>
      fs[] >>
      qabbrev_tac ‘bufLoc = LENGTH cSt2.refs’ >>
      qabbrev_tac ‘IenvRL = cEnv with v := nsBind "buff" (Loc bufLoc) cEnv.v’ >>
      qspecl_then [‘conf’,‘msg’,‘envRL’,‘IenvRL’,‘stRL’,‘src’,
                   ‘bufLoc’,‘REPLICATE (conf.payload_size + 1) 0w’]
                  assume_tac
                  receiveloop_correct >>
      rfs[] >>
      ‘conf.payload_size ≠ 0’
        by fs[cpEval_valid_def] >>
      ‘nsLookup envRL.v (Short "receiveloop") =
        SOME
          (Recclosure IenvRL (receiveloop conf (MAP (CHR ∘ w2n) src))
             "receiveloop")’
        by (qunabbrev_tac ‘envRL’ >>
            rw (Abbr ‘IenvRL’::receiveloop_def::eval_sl)) >>
      ‘nsLookup IenvRL.v (Short "buff") = SOME (Loc bufLoc)’
        by rw (Abbr ‘IenvRL’::eval_sl) >>
      ‘store_lookup bufLoc stRL.refs =
        SOME (W8array (REPLICATE (conf.payload_size + 1) 0w))’
        by (rw (Abbr ‘stRL’::Abbr ‘bufLoc’::eval_sl) >>
            ‘cSt2.refs ++ [W8array (REPLICATE (conf.payload_size + 1) 0w)] ++
            drefsA = cSt2.refs ++ ([W8array (REPLICATE (conf.payload_size + 1) 0w)]
            ++ drefsA)’
              by rw[APPEND_ASSOC] >>
            pop_assum SUBST1_TAC >>
            rw[EL_LENGTH_APPEND,NULL_DEF]) >>
      ‘env_asm IenvRL conf’
        by (qunabbrev_tac ‘IenvRL’ >>
            ‘env_asm cEnv conf’
              suffices_by (rw[] >> fs[env_asm_def,has_v_def,in_module_def] >>
                           rfs[] >> metis_tac[EQ_SYM_EQ]) >>
            fs[cpEval_valid_def]) >>
      fs[] >>
      ntac 5 (pop_assum (K ALL_TAC)) >>
      rename1 ‘evaluate (stRL with clock := ack1) envRL [rec] =
              (stRL with <|clock := _; refs := LUPDATE bufFinlA bufLoc stRL.refs ++ drefs2A;
                           ffi:= _|>, Rval [ulvM])’ >>
      dxrule_then assume_tac evaluate_add_to_clock >>
      fs[] >>
      Q.REFINE_EXISTS_TAC ‘ack1 + ck1e’ >>
      simp[] >>
      rw[evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘nsLookup nsCNC conf.append’ >>
      ‘has_v nsCNC conf.append (LIST_TYPE ^DATUM --> LIST_TYPE ^DATUM --> LIST_TYPE ^DATUM) $++’
        by fs[env_asm_def,Abbr ‘nsCNC’,Abbr ‘envRL’] >>
      fs[has_v_def,Arrow_def,AppReturns_def] >>
      pop_assum (qspecl_then [‘MAP unpad (compile_message conf msg)’,‘ulvM’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘LUPDATE bufFinlA bufLoc stRL.refs ++ drefs2A’ strip_assume_tac) >>
      fs[eval_rel_def] >> simp[] >> qunabbrev_tac ‘stRL’ >>
      rename1 ‘evaluate (empty_state with <|clock := ack1N; refs := _|>) envC1 [expC1] =
               (empty_state with <|clock := ack2N; refs := LUPDATE _ _ _ ++ drefs2A ++ drefs3A|>,
                Rval [uC1])’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stC1 with clock := _) envC1 [expC1]’ >>
      qspecl_then [‘stC1’,‘envC1’,‘expC1’,‘ack1N’,‘ack2N’,‘drefs3A’,‘uC1’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := ack1N; refs := stC1.refs|>)
                envC1 [expC1] =
      (empty_state with <|clock := ack2N; refs := stC1.refs ++ drefs3A|>,Rval[uC1])’
        by fs[Abbr ‘stC1’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘ack1N + ck1e’ >> simp[] >>
      pop_assum (K ALL_TAC) >>
      first_x_assum (qspecl_then [‘l’,‘cV’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘stC1.refs ++ drefs3A’ strip_assume_tac) >>
      simp[] >> fs[eval_rel_def] >>
      qunabbrev_tac ‘stC1’ >>
      rename1 ‘evaluate (empty_state with <|clock := aack1N; refs := _|>) envC2 [expC2] =
         (empty_state with <|clock := aack2N; refs := _ ++ drefs3A ++ drefs4A|>,
          Rval [uC2A])’ >>
      qmatch_goalsub_abbrev_tac ‘evaluate (stC2 with clock := _) envC2 [expC2]’ >>
      qspecl_then [‘stC2’,‘envC2’,‘expC2’,‘aack1N’,‘aack2N’,‘drefs4A’,‘uC2A’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := aack1N; refs := stC2.refs|>)
                envC2 [expC2] =
      (empty_state with <|clock := aack2N; refs := stC2.refs ++ drefs4A|>,Rval[uC2A])’
        by fs[Abbr ‘stC2’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘aack1N + ck1e’ >> simp[] >>
      ‘has_v nsCNC conf.concat (LIST_TYPE ^DATUM --> ^DATUM) FLAT’
        by fs[env_asm_def,Abbr ‘nsCNC’,Abbr ‘envRL’] >>
      fs[has_v_def,Arrow_def,AppReturns_def] >>
      pop_assum (qspecl_then [‘MAP unpad (compile_message conf msg) ++ l’,‘uC2A’] assume_tac) >>
      rfs[] >>
      pop_assum (qspec_then ‘stC2.refs ++ drefs4A’ strip_assume_tac) >>
      simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1e’ >> fs[dec_clock_def,eval_rel_def,ADD1] >>
      rename1 ‘evaluate (empty_state with <|clock := aaack1N; refs := _|>) envC3 [expC3] =
         (empty_state with <|clock := aaack2N; refs := _ ++ drefs5A|>,
          Rval [uC3A])’ >>
      qunabbrev_tac ‘stC2’ >> qmatch_goalsub_abbrev_tac ‘evaluate (stC3 with clock := _) envC3 [expC3]’ >>
      fs[] >>
      qspecl_then [‘stC3’,‘envC3’,‘expC3’,‘aaack1N’,‘aaack2N’,‘drefs5A’,‘uC3A’]
                  assume_tac evaluate_generalise >>
      ‘evaluate (empty_state with <|clock := aaack1N; refs := stC3.refs|>)
                envC3 [expC3] =
      (empty_state with <|clock := aaack2N; refs := stC3.refs ++ drefs5A|>,Rval[uC3A])’
        by fs[Abbr ‘stC3’] >>
      fs[] >> pop_assum (K ALL_TAC) >> Q.REFINE_EXISTS_TAC ‘aaack1N + ck1e’ >> simp[] >>
      pop_assum (K ALL_TAC) >>
      (* Clean up *)
      MAP_EVERY qunabbrev_tac [‘envRL’,‘bufLoc’,‘IenvRL’,‘nsCNC’,‘stC3’] >>
      ntac 3 (qpat_x_assum ‘∀x. _ ’ (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘env_asm _ _’ (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC)) >>
      qunabbrev_tac ‘rec’ >> rw[] >>
      ‘uC3A = uC3’
        by metis_tac[UNCT_def,LIST_TYPE_UNCT,WORD_UNCT] >>
      fs[] >> rw[] >>
      Q.REFINE_EXISTS_TAC ‘aaaacke’ >>
      simp[] >>
      qmatch_goalsub_abbrev_tac
        ‘cEval_equiv conf (evaluate (cSt1A with clock := _ + ce1) cEnv2 cExp2)
                          (evaluate (cSt2A with clock := _ + ce2) cEnv2 cExp2)’ >>
      Q.REFINE_EXISTS_TAC ‘cke’ >> simp[] >>
      ‘∃mc.
        cEval_equiv conf (evaluate (cSt1A with clock := mc) cEnv2 cExp2)
                         (evaluate (cSt2A with clock := mc) cEnv2 cExp2)’
        suffices_by (rw[] >> metis_tac[clock_irrel]) >>
      qunabbrev_tac ‘cExp2’ >> last_x_assum irule >>
      reverse (rw[])
      >- (qmatch_asmsub_abbrev_tac ‘LIST_TYPE ^WORD8 hC3 uC3’ >>
          MAP_EVERY qexists_tac
                   [‘cpNum’,
                    ‘<|bindings := pSt.bindings |+ (s,hC3);
                       queues   := pSt.queues |+
                                   (src, DROP (LENGTH (compile_message conf msg))
                                              (qlk pSt.queues src))|>’] >>
          rw[cpEval_valid_def]
          >- fs[cpEval_valid_def]
          >- (rfs[Abbr ‘cEnv2’,cpEval_valid_def,env_asm_def,has_v_def,in_module_def] >> rfs[] >> rw[])
          >- (fs[Abbr ‘cEnv2’,cpEval_valid_def,letfuns_def] >>
              metis_tac[enc_ok_bind])
          >- (fs[cpEval_valid_def,pSt_pCd_corr_def,pFv_def] >>
              rw[] >> Cases_on ‘vn = s’ >> rw[FLOOKUP_UPDATE])
          >- (fs[Abbr ‘cEnv2’,sem_env_cor_def,cpEval_valid_def,sem_env_cor_def] >>
              rfs[env_asm_def,has_v_def,in_module_def] >> rfs[] >> rw[] >>
              Cases_on ‘n = s’ >> fs[FLOOKUP_UPDATE] >>
              rw[nsLookup_nsBind_compute] >> fs[ps2cs_def]) >>
          cheat) >>
      cheat
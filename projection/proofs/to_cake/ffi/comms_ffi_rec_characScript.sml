open HolKernel boolLib Parse bossLib;
open optionTheory
     relationTheory
     listTheory
     rich_listTheory;
open ffiTheory;
open payloadSemTheory
     payloadLangTheory
     payloadPropsTheory
     payloadConfluenceTheory
     bisimulationTheory
     bisimulation_extTheory
     comms_ffi_modelTheory
     comms_ffi_consTheory
     comms_ffi_propsTheory
     comms_ffi_commTheory
     comms_ffi_eqTheory;

val _ = new_theory "comms_ffi_rec_charac";
(* General Hilbert Choice Helper *)
Theorem some_satisfies_cond:
  ∀P. (some x. P x) = SOME z ⇒ P z
Proof
  rw[some_def] >> SELECT_ELIM_TAC >>
  metis_tac[]
QED

(* FFI State Receive property *)
Definition ffi_receives_def:
  ffi_receives conf st src msg =
    ((conf.payload_size > 0) ∧
    (LENGTH msg > 0) ∧
    (∀s param bytes.
      conf.payload_size > 0 ∧
      LENGTH msg > 0 ∧
      valid_receive_call_format conf src s param bytes ⇒
      ∃nst nbytes.
          call_FFI st s param bytes = FFI_return nst nbytes ∧
          nbytes = pad conf msg ∧
          (final nbytes ∨
           (intermediate nbytes ∧
            ffi_receives conf nst src (DROP conf.payload_size msg)))))
Termination
  WF_REL_TAC ‘measure (λ(_,_,_,msg). LENGTH msg)’ >>
  rw[]
End

Theorem ffi_eq_receives:
  ∀conf x y.
    ffi_wf x.ffi_state ∧
    ffi_wf y.ffi_state ∧
    x.oracle = comms_ffi_oracle conf ∧
    y.oracle = comms_ffi_oracle conf ∧
    ffi_eq conf x.ffi_state y.ffi_state ⇒
    ffi_receives conf x = ffi_receives conf y
Proof
  simp[FUN_EQ_THM,PULL_FORALL] >>
  rpt gen_tac >>
  rename1 ‘ffi_receives conf x src msg = ffi_receives conf y src msg’ >>
  MAP_EVERY qid_spec_tac [‘y’,‘x’] >>
  completeInduct_on ‘LENGTH msg’ >>
  rw[Once ffi_receives_def] >>
  qmatch_goalsub_abbrev_tac ‘LP ⇔ _’ >>
  rw[Once ffi_receives_def] >>
  qunabbrev_tac ‘LP’ >>
  qmatch_goalsub_abbrev_tac ‘PA ∧ PB ∧ PCA ⇔ PA ∧ PB ∧ PCB’ >>
  ‘PCA ⇔ PCB’
    suffices_by rw[] >>
  MAP_EVERY qunabbrev_tac [‘PA’,‘PB’,‘PCA’,‘PCB’] >>
  rw[EQ_IMP_THM] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rw[]
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf x.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf x.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >>
          Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf x.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf x.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[] >> Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          DISJ2_TAC >>
          last_x_assum (qspec_then ‘LENGTH (DROP conf.payload_size msg)’ assume_tac) >>
          rfs[] >> first_x_assum (qspec_then ‘DROP conf.payload_size msg’ assume_tac) >>
          rfs[] >> qmatch_goalsub_abbrev_tac ‘ffi_receives _ nstY _ _’ >>
          first_x_assum (qspecl_then [‘nst’,‘nstY’] assume_tac) >>
          rfs[] >> pop_assum irule >>
          qunabbrev_tac ‘nstY’ >>
          qpat_x_assum ‘_ = nst’ (SUBST1_TAC o GSYM) >>
          rw[] >> metis_tac[strans_pres_wf,ffi_eq_pres])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf y.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf y.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >>
          Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘y2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf y.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf y.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[] >> Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          DISJ2_TAC >>
          last_x_assum (qspec_then ‘LENGTH (DROP conf.payload_size msg)’ assume_tac) >>
          rfs[] >> first_x_assum (qspec_then ‘DROP conf.payload_size msg’ assume_tac) >>
          rfs[] >> qmatch_goalsub_abbrev_tac ‘ffi_receives _ nstX _ _’ >>
          first_x_assum (qspecl_then [‘nst’,‘nstX’] assume_tac) >>
          rfs[] >> pop_assum irule >>
          qunabbrev_tac ‘nstX’ >>
          qpat_x_assum ‘_ = nst’ (SUBST1_TAC o GSYM) >>
          rw[] >>
          metis_tac[strans_pres_wf,ffi_eq_pres,ffi_eq_equivRel,
                    equivalence_def,symmetric_def])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘y2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
QED

Definition ffi_term_stream_def:
  (ffi_term_stream conf st src (c1::c2::cs) =
    (¬final c1 ∧
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
      ∃nst.
        call_FFI st s param bytes = FFI_return nst c1 ∧
        ffi_term_stream conf nst src (c2::cs))) ∧
  (ffi_term_stream conf st src (c1::[]) =
    (final c1 ∧
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
      ∃nst.
        call_FFI st s param bytes = FFI_return nst c1)) ∧
  (ffi_term_stream conf st src [] = F)
End

Theorem ffi_eq_term_stream:
  ∀conf x y.
    ffi_wf x.ffi_state ∧
    ffi_wf y.ffi_state ∧
    x.oracle = comms_ffi_oracle conf ∧
    y.oracle = comms_ffi_oracle conf ∧
    ffi_eq conf x.ffi_state y.ffi_state ⇒
    ffi_term_stream conf x = ffi_term_stream conf y
Proof
  simp[FUN_EQ_THM,PULL_FORALL] >>
  rpt gen_tac >>
  rename1 ‘ffi_term_stream conf x src chnks = ffi_term_stream conf y src chnks’ >>
  MAP_EVERY qid_spec_tac [‘y’,‘x’] >>
  Induct_on ‘chnks’
  >- rw[ffi_term_stream_def] >>
  Cases_on ‘chnks’ >>
  rw[ffi_term_stream_def] >>
  irule (DECIDE “∀a b c. (b ⇔ c) ⇒ ((a ∧ b) ⇔ (a ∧ c))”) >>
  rw[EQ_IMP_THM] >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf x.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf x.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >>
          Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf y.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf y.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >>
          Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf x.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf x.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[] >> Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          qmatch_goalsub_abbrev_tac ‘ffi_term_stream conf nstY param (h::t)’ >>
          ‘ffi_term_stream conf nst param (h::t) ⇔
           ffi_term_stream conf nstY param (h::t)’
            suffices_by metis_tac[] >>
          last_x_assum irule >>
          qunabbrev_tac ‘nstY’ >> fs[] >>
          qpat_x_assum ‘_ = nst’ (fn x => REWRITE_TAC[GSYM x]) >>
          rw[]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[ffi_eq_pres])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
  >- (rfs[call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,ffi_receive_def] >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on ‘some (m,ns). (strans conf y.ffi_state (ARecv param m) ns)’ >>
      fs[] >>
      rename1 ‘(some (m,ns). strans conf y.ffi_state (ARecv param m) ns) = SOME nsb’ >>
      ‘(λ(m,ns). strans conf y.ffi_state (ARecv param m) ns) nsb’
            by metis_tac[some_satisfies_cond] >>
      PairCases_on ‘nsb’ >> fs[]
      >- (rename1 ‘(λ(m,ns). strans conf x.ffi_state (ARecv param m) ns) ns’ >>
          PairCases_on ‘ns’ >> fs[] >>
          ‘nsb0 = ns0’
            by metis_tac[ffi_eq_ARecv] >>
          fs[] >> Cases_on ‘LENGTH ns0 = SUC conf.payload_size’ >> fs[] >>
          qmatch_goalsub_abbrev_tac ‘ffi_term_stream conf nstX param (h::t)’ >>
          ‘ffi_term_stream conf nst param (h::t) ⇔
           ffi_term_stream conf nstX param (h::t)’
            suffices_by metis_tac[] >>
          last_x_assum irule >>
          qunabbrev_tac ‘nstX’ >> fs[] >>
          qpat_x_assum ‘_ = nst’ (fn x => REWRITE_TAC[GSYM x]) >>
          rw[]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[ffi_eq_equivRel,equivalence_def,symmetric_def,
                       ffi_eq_pres])
      >- (rw[pairTheory.EXISTS_PROD] >>
          qexists_tac ‘nsb0’ >>
          rw[GSYM pairTheory.EXISTS_PROD] >>
          qabbrev_tac ‘L = ARecv param nsb0’ >>
          qabbrev_tac ‘x2 = (nsb1,nsb2,nsb3)’ >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]))
QED

Definition ffi_divg_stream_def:
  (ffi_divg_stream conf st src (c1::cs) =
    (¬final c1 ∧
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
      ∃nst.
        call_FFI st s param bytes = FFI_return nst c1 ∧
        ffi_divg_stream conf nst src cs)) ∧
  (ffi_divg_stream conf st src [] =
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
        call_FFI st s param bytes = FFI_final(Final_event s param bytes FFI_diverged))
End

Theorem ffi_eq_divg_stream:
  ∀conf x y.
    ffi_wf x.ffi_state ∧
    ffi_wf y.ffi_state ∧
    x.oracle = comms_ffi_oracle conf ∧
    y.oracle = comms_ffi_oracle conf ∧
    ffi_eq conf x.ffi_state y.ffi_state ⇒
    ffi_divg_stream conf x = ffi_divg_stream conf y
Proof
  simp[FUN_EQ_THM,PULL_FORALL] >>
  rpt gen_tac >>
  rename1 ‘ffi_divg_stream conf x src chnks = ffi_divg_stream conf y src chnks’ >>
  MAP_EVERY qid_spec_tac [‘y’,‘x’] >>
  Induct_on ‘chnks’
  >- (rw[ffi_divg_stream_def,EQ_IMP_THM] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      rfs[call_FFI_def,ffi_receive_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,AllCaseEqs()] >>
      first_x_assum mp_tac >>
      ntac 2 (DEEP_INTRO_TAC some_intro) >>
      rw[pairTheory.EXISTS_PROD] >>
      rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
      PairCases_on ‘XP’ >>
      fs[] >> qexists_tac ‘XP0’ >>
      rw[GSYM pairTheory.EXISTS_PROD] >>
      qabbrev_tac ‘XP = (XP1,XP2,XP3)’ >>
      first_x_assum (K ALL_TAC) >>
      metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]) >>
  rw[ffi_divg_stream_def, EQ_IMP_THM] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rfs[call_FFI_def,ffi_receive_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,AllCaseEqs()] >>
  qpat_x_assum ‘(some (m,ns). strans conf _ (ARecv _ m) ns) = _’ mp_tac >>
  ntac 2 (DEEP_INTRO_TAC some_intro) >>
  rw[pairTheory.EXISTS_PROD]
  >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
      PairCases_on ‘XP’ >>
      fs[] >> rw[]
      >- metis_tac[ffi_eq_ARecv] >>
      qmatch_asmsub_abbrev_tac  ‘ffi_divg_stream conf nstX param chnks’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_divg_stream conf nstY param chnks’ >>
      ‘ffi_divg_stream conf nstX param chnks ⇔
        ffi_divg_stream conf nstY param chnks’
        suffices_by metis_tac[] >>
      first_x_assum irule >>
      MAP_EVERY qunabbrev_tac [‘nstX’,‘nstY’] >>
      fs[] >> qabbrev_tac ‘XP = (XP1,XP2,XP3)’ >>
      first_x_assum (K ALL_TAC) >>
      rw[] >>
      ‘XP0 = h’
        suffices_by (rw[] >> metis_tac[strans_pres_wf,ffi_eq_pres]) >>
      metis_tac[ffi_eq_ARecv])
  >- (fs[pairTheory.FORALL_PROD] >>
      qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
      first_x_assum (qspec_then ‘MO’ assume_tac) >>
      fs[GSYM pairTheory.FORALL_PROD] >>
      metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])
  >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
      PairCases_on ‘XP’ >>
      fs[] >> rw[]
      >- metis_tac[ffi_eq_ARecv] >>
      qmatch_asmsub_abbrev_tac  ‘ffi_divg_stream conf nstX param chnks’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_divg_stream conf nstY param chnks’ >>
      ‘ffi_divg_stream conf nstX param chnks ⇔
        ffi_divg_stream conf nstY param chnks’
        suffices_by metis_tac[] >>
      first_x_assum irule >>
      MAP_EVERY qunabbrev_tac [‘nstX’,‘nstY’] >>
      fs[] >> qabbrev_tac ‘XP = (XP1,XP2,XP3)’ >>
      first_x_assum (K ALL_TAC) >>
      rw[] >>
      ‘XP0 = h’
        suffices_by (rw[] >> metis_tac[strans_pres_wf,ffi_eq_pres,ffi_eq_equivRel,
                                       equivalence_def,symmetric_def]) >>
      metis_tac[ffi_eq_ARecv])
  >- (fs[pairTheory.FORALL_PROD] >>
      qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
      first_x_assum (qspec_then ‘MO’ assume_tac) >>
      fs[GSYM pairTheory.FORALL_PROD] >>
      metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])
QED

Definition ffi_fail_stream_def:
  (ffi_fail_stream conf st src (c1::cs) =
    (¬final c1 ∧
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
      ∃nst.
        call_FFI st s param bytes = FFI_return nst c1 ∧
        ffi_fail_stream conf nst src cs)) ∧
  (ffi_fail_stream conf st src [] =
    ∀s param bytes.
      valid_receive_call_format conf src s param bytes ⇒
        call_FFI st s param bytes = FFI_final(Final_event s param bytes FFI_failed))
End

Theorem ffi_eq_fail_stream:
  ∀conf x y.
    ffi_wf x.ffi_state ∧
    ffi_wf y.ffi_state ∧
    x.oracle = comms_ffi_oracle conf ∧
    y.oracle = comms_ffi_oracle conf ∧
    ffi_eq conf x.ffi_state y.ffi_state ⇒
    ffi_fail_stream conf x = ffi_fail_stream conf y
Proof
  simp[FUN_EQ_THM,PULL_FORALL] >>
  rpt gen_tac >>
  rename1 ‘ffi_fail_stream conf x src chnks = ffi_fail_stream conf y src chnks’ >>
  MAP_EVERY qid_spec_tac [‘y’,‘x’] >>
  Induct_on ‘chnks’
  >- (rw[ffi_fail_stream_def,EQ_IMP_THM] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      rfs[call_FFI_def,ffi_receive_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,AllCaseEqs()] >>
      first_x_assum mp_tac >>
      ntac 2 (DEEP_INTRO_TAC some_intro) >>
      rw[pairTheory.EXISTS_PROD]
      >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
          PairCases_on ‘XP’ >>
          fs[] >> qmatch_asmsub_rename_tac ‘LENGTH BM ≠ SUC conf.payload_size’ >>
          ‘XP0 = BM’
            suffices_by rw[] >>
          qmatch_asmsub_abbrev_tac ‘strans conf y.ffi_state _ TI’ >>
          metis_tac[ffi_eq_ARecv])
      >- (fs[pairTheory.FORALL_PROD] >>
          qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
          first_x_assum (qspec_then ‘MO’ assume_tac) >>
          fs[GSYM pairTheory.FORALL_PROD] >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])
      >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
          PairCases_on ‘XP’ >>
          fs[] >> qmatch_asmsub_rename_tac ‘LENGTH BM ≠ SUC conf.payload_size’ >>
          ‘XP0 = BM’
            suffices_by rw[] >>
          qmatch_asmsub_abbrev_tac ‘strans conf x.ffi_state _ TI’ >>
          metis_tac[ffi_eq_ARecv])
      >- (fs[pairTheory.FORALL_PROD] >>
          qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
          first_x_assum (qspec_then ‘MO’ assume_tac) >>
          fs[GSYM pairTheory.FORALL_PROD] >>
          metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])) >>
  rw[ffi_fail_stream_def, EQ_IMP_THM] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rfs[call_FFI_def,ffi_receive_def,valid_receive_call_format_def,
         comms_ffi_oracle_def,AllCaseEqs()] >>
  qpat_x_assum ‘(some (m,ns). strans conf _ (ARecv _ m) ns) = _’ mp_tac >>
  ntac 2 (DEEP_INTRO_TAC some_intro) >>
  rw[pairTheory.EXISTS_PROD]
  >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
      PairCases_on ‘XP’ >>
      fs[] >> rw[]
      >- metis_tac[ffi_eq_ARecv] >>
      qmatch_asmsub_abbrev_tac  ‘ffi_fail_stream conf nstX param chnks’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_fail_stream conf nstY param chnks’ >>
      ‘ffi_fail_stream conf nstX param chnks ⇔
        ffi_fail_stream conf nstY param chnks’
        suffices_by metis_tac[] >>
      first_x_assum irule >>
      MAP_EVERY qunabbrev_tac [‘nstX’,‘nstY’] >>
      fs[] >> qabbrev_tac ‘XP = (XP1,XP2,XP3)’ >>
      first_x_assum (K ALL_TAC) >>
      rw[] >>
      ‘XP0 = h’
        suffices_by (rw[] >> metis_tac[strans_pres_wf,ffi_eq_pres]) >>
      metis_tac[ffi_eq_ARecv])
  >- (fs[pairTheory.FORALL_PROD] >>
      qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
      first_x_assum (qspec_then ‘MO’ assume_tac) >>
      fs[GSYM pairTheory.FORALL_PROD] >>
      metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])
  >- (rename1 ‘(λ(m,ns). strans _ _ (ARecv param m) ns) XP’ >>
      PairCases_on ‘XP’ >>
      fs[] >> rw[]
      >- metis_tac[ffi_eq_ARecv] >>
      qmatch_asmsub_abbrev_tac  ‘ffi_fail_stream conf nstX param chnks’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_fail_stream conf nstY param chnks’ >>
      ‘ffi_fail_stream conf nstX param chnks ⇔
        ffi_fail_stream conf nstY param chnks’
        suffices_by metis_tac[] >>
      first_x_assum irule >>
      MAP_EVERY qunabbrev_tac [‘nstX’,‘nstY’] >>
      fs[] >> qabbrev_tac ‘XP = (XP1,XP2,XP3)’ >>
      first_x_assum (K ALL_TAC) >>
      rw[] >>
      ‘XP0 = h’
        suffices_by (rw[] >> metis_tac[strans_pres_wf,ffi_eq_pres,ffi_eq_equivRel,
                                       equivalence_def,symmetric_def]) >>
      metis_tac[ffi_eq_ARecv])
  >- (fs[pairTheory.FORALL_PROD] >>
      qmatch_goalsub_rename_tac ‘¬strans conf _ (ARecv _ MO) _’ >>
      first_x_assum (qspec_then ‘MO’ assume_tac) >>
      fs[GSYM pairTheory.FORALL_PROD] >>
      metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def])
QED

Definition netout_trans_def:
  netout_trans conf c n1 n2 ⇔
    ∃sp d. trans conf n1 (LSend sp d c) n2
End

Definition netin_trans_def:
  netin_trans conf c n1 n2 ⇔
    (∃L. trans conf n1 L n2 ∧
      ∀sp d. L ≠ LSend sp d c)
End

Definition netout_limit_def:
  (netout_limit conf c n1 0 ⇔
    ¬∃n2 n3.
      RTC (netin_trans conf c) n1 n2 ∧
      netout_trans conf c n2 n3) ∧
  (netout_limit conf c n1 (SUC i) ⇔
    (∃n2 n3.
      RTC (netin_trans conf c) n1 n2 ∧
      netout_trans conf c n2 n3) ∧
    (∀n2 n3.
      RTC (netin_trans conf c) n1 n2 ∧
      netout_trans conf c n2 n3 ⇒
      netout_limit conf c n3 i)) 
End

Theorem netin_struc_pres_NNil:
  ∀conf c n2.
    RTC (netin_trans conf c) NNil n2 ⇒
    n2 = NNil
Proof
  rw[] >> pop_assum mp_tac >>
  qid_spec_tac ‘n2’ >>
  Induct_on ‘RTC’ >> rw[] >>
  fs[netin_trans_def] >> fs[Once trans_cases]
QED

Theorem netin_struc_pres_NPar:
  ∀conf n1a n1b n2.
    RTC (netin_trans conf c) (NPar n1a n1b) n2 ⇒
    ∃n2a n2b.
      n2 = NPar n2a n2b
Proof
  rw[] >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘n1a’,‘n1b’,‘n2’] >>
  Induct_on ‘RTC’ >> rw[] >>
  fs[netin_trans_def] >> fs[Once trans_cases]
QED

Theorem netin_struc_prop_NPar:
  ∀conf c n1a n1b n2a n2b.
    ¬(net_has_node (NPar n1a n1b) c) ∧
    RTC (netin_trans conf c) (NPar n1a n1b) (NPar n2a n2b) ⇒
    (RTC (netin_trans conf c) n1a n2a ∧
     RTC (netin_trans conf c) n1b n2b)
Proof
  ntac 2 strip_tac >> Induct_on ‘RTC’ >> rw[]
  >- rw[RTC_REFL] >- rw[RTC_REFL] >>
  rename1 ‘netin_trans conf c (NPar n1a n1b) ni’ >>
  ‘∃nia nib. ni = NPar nia nib’
    by metis_tac[RTC_SINGLE,netin_struc_pres_NPar] >>
  ‘¬net_has_node ni c’
    by (fs[netin_trans_def] >> metis_tac[trans_pres_nodes])  >>
  rw[]
  >- (‘RC (netin_trans conf c) n1a nia’
        suffices_by (rw[RC_DEF] >>
                     metis_tac[RTC_REFL,RTC_SINGLE,RTC_TRANSITIVE,
                           transitive_def]) >>
      fs[netin_trans_def,netout_trans_def] >>
      last_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      fs[] >> rw[RC_DEF] >> fs[netin_trans_def]
      >- (DISJ2_TAC >>
          rename1 ‘trans conf _ (LSend p1 d p2) _’ >>
          qexists_tac ‘LSend p1 d p2’ >> rw[] >>
          DISJ2_TAC >> DISJ2_TAC >>
          ‘net_has_node n1b p2’
            suffices_by (fs[net_has_node_def] >> metis_tac[]) >>
          metis_tac[trans_receive_cond])
      >- (DISJ2_TAC >>
          rename1 ‘trans conf _ (LReceive p1 d p2) _’ >>
          qexists_tac ‘LReceive p1 d p2’ >> fs[])
      >- metis_tac[])
  >- (‘RC (netin_trans conf c) n1b nib’
        suffices_by (rw[RC_DEF] >>
                     metis_tac[RTC_REFL,RTC_SINGLE,RTC_TRANSITIVE,
                           transitive_def]) >>
      fs[netin_trans_def,netout_trans_def] >>
      last_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      fs[] >> rw[RC_DEF] >> fs[netin_trans_def]
      >- (DISJ2_TAC >>
          rename1 ‘trans conf _ (LReceive p1 d p2) _’ >>
          qexists_tac ‘LReceive p1 d p2’ >> fs[])
      >- (DISJ2_TAC >>
          rename1 ‘trans conf _ (LSend p1 d p2) _’ >>
          qexists_tac ‘LSend p1 d p2’ >> rw[] >>
          DISJ2_TAC >> DISJ2_TAC >>
          ‘net_has_node n1a p2’
            suffices_by (fs[net_has_node_def] >> metis_tac[]) >>
          metis_tac[trans_receive_cond])
      >- metis_tac[])
QED

Theorem netin_struc_pres_NEndpoint:
  ∀conf c p s e n2.
    RTC (netin_trans conf c) (NEndpoint p s e) n2 ⇒
    ∃s2 e2.
      n2 = NEndpoint p s2 e2
Proof
  rw[] >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘s’,‘e’,‘n2’] >>
  Induct_on ‘RTC’ >> rw[] >>
  fs[netin_trans_def] >> fs[Once trans_cases]
QED

Theorem netout_limit_exists:
  ∀conf c net.
    ¬net_has_node net c ⇒
    ∃n.
      netout_limit conf c net n
Proof
  ntac 2 strip_tac >> Induct_on ‘net’ >> rw[]
  >- (qexists_tac ‘0’ >> rw[netout_limit_def] >>
      reverse (Cases_on ‘RTC (netin_trans conf c) NNil n2’) >>
      rw[] >>
      ‘n2 = NNil’
        suffices_by rw[netout_trans_def, Once trans_cases] >> 
      metis_tac[netin_struc_pres_NNil])
  >- (fs[net_has_node_def] >>
      rename[‘NPar net1 net2’,‘netout_limit conf c net1 i1’,
             ‘netout_limit conf c net2 i2’] >>
      qexists_tac ‘i1 + i2’ >> rpt (pop_assum mp_tac) >>
      MAP_EVERY qid_spec_tac [‘i2’,‘i1’,‘net2’,‘net1’] >>
      Induct_on ‘i1’ >> Induct_on ‘i2’ >> rw[netout_limit_def]
      >- (CCONTR_TAC >> fs[] >>
          drule_all_then strip_assume_tac netin_struc_pres_NPar >>
          fs[] >>
          drule_all_then strip_assume_tac
                        (REWRITE_RULE [net_has_node_def,boolTheory.DE_MORGAN_THM]
                                      netin_struc_prop_NPar) >>
          ‘(∃n3a. netout_trans conf c n2a n3a) ∨
           (∃n3b. netout_trans conf c n2b n3b)’
            suffices_by (rw[] >> metis_tac[]) >>
          qpat_x_assum ‘netout_trans _ _ _ _’ (assume_tac o REWRITE_RULE [netout_trans_def]) >>
          rw[] >> fs[Once trans_cases] >> rw[netout_trans_def] >> metis_tac[])
      >- (qexistsl_tac [‘NPar net1 n2’,‘NPar net1 n3’] >>
          reverse (rw[netout_trans_def])
          >- (rw[Once trans_cases] >> fs[netout_trans_def] >> metis_tac[]) >>
          qpat_x_assum ‘RTC _ _ _’ mp_tac >>
          MAP_EVERY qid_spec_tac [‘net2’,‘n2’] >>
          Induct_on ‘RTC’ >> rw[] >>
          rename1 ‘netin_trans conf c net2ia net2ib’ >>
          ‘netin_trans conf c (NPar net1 net2ia) (NPar net1 net2ib)’
            suffices_by metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def] >>
          rw[netin_trans_def,Once trans_cases] >> fs[netin_trans_def] >>
          metis_tac[])
      >- (drule_all_then strip_assume_tac netin_struc_pres_NPar >>
          fs[] >> rename1 ‘netout_trans conf c (NPar n2a n2b) n3P’ >>
          ‘∃n3a n3b. n3P = NPar n3a n3b’
            by (fs[netout_trans_def] >> fs[Once trans_cases] >> rw[]) >>
          fs[] >> last_x_assum irule >> rw[]
          >- (‘¬net_has_node (NPar n3a n3b) c’
                suffices_by rw[net_has_node_def] >>
              ‘¬net_has_node (NPar n2a n2b) c’
                suffices_by  (fs[netout_trans_def] >> metis_tac[trans_pres_nodes]) >>
              ‘¬net_has_node (NPar net1 net2) c’
                suffices_by (qpat_x_assum ‘RTC _ _ _’ mp_tac >>
                             MAP_EVERY qid_spec_tac [‘net1’,‘net2’,‘n2a’,‘n2b’] >>
                             Induct_on ‘RTC’ >> rw[] >>
                             pop_assum irule >>
                             fs[netin_trans_def,Once trans_cases,net_has_node_def] >>
                             metis_tac[trans_pres_nodes]) >>
              rw[net_has_node_def])
          >- (‘¬net_has_node (NPar n3a n3b) c’
                suffices_by rw[net_has_node_def] >>
              ‘¬net_has_node (NPar n2a n2b) c’
                suffices_by  (fs[netout_trans_def] >> metis_tac[trans_pres_nodes]) >>
              ‘¬net_has_node (NPar net1 net2) c’
                suffices_by (qpat_x_assum ‘RTC _ _ _’ mp_tac >>
                             MAP_EVERY qid_spec_tac [‘net1’,‘net2’,‘n2a’,‘n2b’] >>
                             Induct_on ‘RTC’ >> rw[] >>
                             pop_assum irule >>
                             fs[netin_trans_def,Once trans_cases,net_has_node_def] >>
                             metis_tac[trans_pres_nodes]) >>
              rw[net_has_node_def])
          >- (fs[netout_trans_def] >>
              qpat_x_assum ‘trans _ (NPar _ _) _ (NPar _ _)’
                           (assume_tac o REWRITE_RULE [Once trans_cases]) >>
              fs[]
              >- (last_x_assum (qspec_then ‘n2a’ strip_assume_tac) >>
                  ‘RTC (netin_trans conf c) net1 n2a’
                    by (drule_all_then strip_assume_tac
                                       (REWRITE_RULE [net_has_node_def,boolTheory.DE_MORGAN_THM]
                                                      netin_struc_prop_NPar)) >>
                  metis_tac[]) >>
              rw[netout_limit_def] >> rename1 ‘¬RTC (netin_trans conf c) n2a NI’ >>
              Cases_on ‘RTC (netin_trans conf c) n2a NI’ >> rw[] >>
              last_x_assum (qspec_then ‘NI’ strip_assume_tac) >>
              ‘RTC (netin_trans conf c) net1 NI’
                by (drule_all_then strip_assume_tac
                                   (REWRITE_RULE [net_has_node_def,boolTheory.DE_MORGAN_THM]
                                                  netin_struc_prop_NPar) >>
                    metis_tac[RTC_TRANSITIVE,transitive_def]) >>
              fs[] >> rw[netout_trans_def])
          >- (fs[netout_trans_def] >>
              qpat_x_assum ‘trans _ (NPar _ _) _ (NPar _ _)’
                           (assume_tac o REWRITE_RULE [Once trans_cases]) >>
              reverse (fs[])
              >- (last_x_assum (qspec_then ‘n2b’ strip_assume_tac) >>
                  ‘RTC (netin_trans conf c) net2 n2b’
                    by (drule_all_then strip_assume_tac
                                       (REWRITE_RULE [net_has_node_def,boolTheory.DE_MORGAN_THM]
                                                      netin_struc_prop_NPar)) >>
                  metis_tac[]) >>
              last_x_assum (qspec_then ‘n2a’ strip_assume_tac) >>
              ‘RTC (netin_trans conf c) net1 n2a’
                by (drule_all_then strip_assume_tac
                                   (REWRITE_RULE [net_has_node_def,boolTheory.DE_MORGAN_THM]
                                                  netin_struc_prop_NPar) >>
                    metis_tac[RTC_TRANSITIVE,transitive_def]) >>
              fs[] >> rw[netout_trans_def])
            )
          >- cheat
          >- cheat
          >- cheat
          )
      >- cheat
QED

Theorem netout_limit_unique:
  ∀conf c N n m.
    netout_limit conf c N m ∧
    netout_limit conf c N n ⇒
    (m = n)
Proof
  ntac 2 strip_tac >>
  Induct_on ‘m’ >> Induct_on ‘n’ >>
  rw[netout_limit_def]
  >- metis_tac[]
  >- metis_tac[] >>
  first_x_assum irule >>
  ntac 2 (first_x_assum (drule_all_then assume_tac)) >>
  metis_tac[]
QED

Theorem netout_limit_cond:
  ∀conf c n1 i.
    ¬net_has_node n1 c ∧
    (∃n2 n3.
      RTC (netin_trans conf c) n1 n2 ∧
      netout_trans conf c n2 n3 ∧
      netout_limit conf c n3 i) ⇒
    (netout_limit conf c n1 (SUC i)) 
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘∃m. netout_limit conf c n1 m’
    by metis_tac[netout_limit_exists] >>
  Cases_on ‘m = SUC i’ >> fs[] >> Cases_on ‘m’ >>
  fs[netout_limit_def]
  >- metis_tac[] >>
  pop_assum mp_tac >> simp[] >>
  rename1 ‘netout_limit conf c NF i’ >>
  ‘netout_limit conf c NF n’
    suffices_by metis_tac[netout_limit_unique] >>
  first_x_assum irule >> metis_tac[]
QED

(*
Theorem active_trans_netout_limit_same:
  ∀conf c qA NA qB NB.
    RTC (active_trans conf c) (qA,NA) (qB,NB) ⇒
    ¬net_has_node NA c ⇒
    qsame qA qB ⇒
    netout_limit conf c NA = netout_limit conf c NB
Proof
  ntac 2 strip_tac >>
  Induct_on ‘RTC’ >> rw[] >>
  rename1 ‘active_trans conf c (qA,NA) NI’ >>
  PairCases_on ‘NI’ >> rename1 ‘active_trans conf c (qA,NA) (qI,NI)’ >>
  first_x_assum (qspecl_then [‘qI’,‘NI’] assume_tac) >>
  fs[] >>
  ‘¬net_has_node NI c’
    by (fs[active_trans_def,internal_trans_def,emit_trans_def] >>
        metis_tac[trans_pres_nodes]) >>
  ‘qsame qI qB’
    by (rw[qsame_def] >>
        rename1 ‘qlk _ sp = qlk _ sp’ >> 
        ‘isPREFIX (qlk qI sp) (qlk qB sp) ∧ isPREFIX (qlk qB sp) (qlk qI sp)’
          suffices_by metis_tac[IS_PREFIX_ANTISYM] >>
        rw[]
        >- metis_tac[active_trans_queue_expand] >>
        ‘isPREFIX (qlk qA sp) (qlk qI sp)’
          suffices_by fs[qsame_def] >>
        metis_tac[RTC_SINGLE,active_trans_queue_expand]) >>
  fs[] >>
  ‘netout_limit conf c NA = netout_limit conf c NI’
    suffices_by metis_tac[] >>
  qpat_x_assum ‘netout_limit conf c NI = _’ kall_tac >>
  ‘internal_trans conf c (qA,NA) (qI,NI)’
    by (fs[active_trans_def,emit_trans_def] >> CCONTR_TAC >> fs[] >>
        ‘qsame qA qI’
          suffices_by (rw[qsame_def] >> rename1 ‘qpush qA sp d’ >>
                       qexists_tac ‘sp’ >> rw[]) >>
        fs[qsame_def] >> metis_tac[]) >>
  rpt (qpat_x_assum ‘qsame _ _’ kall_tac) >>
  rpt (qpat_x_assum ‘active_trans _ _ _ _’ kall_tac) >>
  rpt (qpat_x_assum ‘RTC (active_trans _ _) _ _’ kall_tac) >>
  fs[internal_trans_def] >>
  rw[FUN_EQ_THM,EQ_IMP_THM,netout_limit_def]
  >- (CCONTR_TAC >>
      rename1 ‘netout_limit conf c NA x’ >>
      Cases_on ‘x’
      >- (fs[netout_limit_def] >> CCONTR_TAC >>
          fs[] >> qpat_x_assum ‘∀n2 n3. ¬RTC _ _ n2 ∨ ¬_ _ _ n2 n3’ mp_tac >>
          simp[] >> rename [‘RTC (netin_trans conf c) NI N2’,‘netout_trans conf c N2 N3’] >>
          qexistsl_tac [‘N2’,‘N3’] >>
          ‘netin_trans conf c NA NI’
            suffices_by (rw[] >> metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def]) >>
          rw[netin_trans_def] >> qexists_tac ‘LTau’ >> rw[]) >>
      ‘∃y. netout_limit conf c NI y’
        by metis_tac[netout_limit_exists] >>
      rename1 ‘SUC n’ >>
      Cases_on ‘y = SUC n’ >> fs[] >>
      ‘netout_limit conf c NA y’
        suffices_by (rw[] >> metis_tac[met]
      


  first_x_assum (drul)
QED*)

Theorem ffi_gets_stream:
  ∀conf src (st : total_state ffi_state).
    ffi_wf st.ffi_state ∧
    st.oracle = comms_ffi_oracle conf ⇒
    ((∃cs. ffi_term_stream conf st src cs) ∨
     (∃cs. ffi_divg_stream conf st src cs) ∨
     (∃cs. ffi_fail_stream conf st src cs))
Proof
  cheat
(*
  rw[] >>
  ‘∃c q N. st.ffi_state = (c,q,N)’
    by (rename1 ‘ffi_wf ffiSt’ >> PairCases_on ‘ffiSt’ >> rw[]) >>
  fs[] >>
  ‘∃n. netout_limit conf c N n’
    by (irule netout_limit_exists >>
        fs[ffi_wf_def]) >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘st’,‘N’] >>
  Induct_on ‘n’ >>
  Induct_on ‘qlk q src’
  (* Handle empty queue and netout_limit 0 *)
  >- (rw[] >> DISJ2_TAC >> DISJ1_TAC >>
      qexists_tac ‘[]’ >>
      rw[ffi_divg_stream_def,call_FFI_def,
         comms_ffi_oracle_def,valid_receive_call_format_def,
         ffi_receive_def,some_def,AllCaseEqs()] >>
      rename1 ‘¬_ x’ >> PairCases_on ‘x’ >>
      rw[] >> CCONTR_TAC >> fs[] >>
      ‘x1 = c’
        by metis_tac[strans_pres_pnum,pairTheory.FST] >>
      rw[] >>
      drule_all_then strip_assume_tac strans_receive_deconstruct >>
      ‘qi1 ≠ q’
        by (CCONTR_TAC >> fs[output_trans_def] >>
            ‘qlk (normalise_queues q) src = qlk (normalise_queues qi2 |+ (src,x0::qlk qi2 src)) src’
              by (qpat_x_assum ‘normalise_queues q = _’ SUBST1_TAC >> rw[]) >>
            fs[]) >>
      ‘∃n. netout_limit conf c N (SUC n)’
        suffices_by (strip_tac >> fs[] >>
                     ‘SUC n = 0’
                        suffices_by rw[] >>
                     metis_tac[netout_limit_unique]) >>
      pop_assum mp_tac >>
      rename1 ‘RTC (active_trans conf c) (q,N) (qi1,ni)’ >>
      qpat_x_assum ‘ffi_wf (c,q,N)’ mp_tac >>
      qpat_x_assum ‘RTC (active_trans conf c) (q,N) (qi1,ni)’ mp_tac >>
      MAP_EVERY qid_spec_tac [‘q’,‘N’,‘qi1’,‘ni’] >>
      Induct_on ‘RTC’ >> rw[] >> rename1 ‘active_trans conf c (qA,NA) qNB’ >>
      PairCases_on ‘qNB’ >> rename1 ‘RTC (active_trans conf c) (qB,NB) (qC,NC)’ >>
      ‘ffi_wf (c,qB,NB)’
        by metis_tac[RTC_SINGLE,active_trans_pres_wf] >>
      fs[active_trans_def,internal_trans_def,emit_trans_def]
      >- (qpat_x_assum ‘_ ⇒ ∃n. _’ mp_tac >> impl_tac >- metis_tac[] >> rw[] >>
          rename1 ‘netout_limit conf c NB (SUC n)’ >>
          qexists_tac ‘n’ >>
          irule netout_limit_cond >>
          reverse (rw[])
          >- fs[ffi_wf_def] >>
          pop_assum (assume_tac o REWRITE_RULE [netout_limit_def]) >>
          fs[]
          rename [‘RTC (netin_trans conf c) NB NI’,‘netout_trans conf c NI NE’] >>
          qexistsl_tac [‘NI’,‘NE’] >> reverse (rw[])
          >- metis_tac[] >>
          ‘netin_trans conf c NA NB’
            suffices_by metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def] >>
          rw[netin_trans_def] >> qexists_tac ‘LTau’ >> rw[])

          ‘∃m. netout_limit conf c NA m’
            by (irule netout_limit_exists >>
                fs[ffi_wf_def]) >>
          Cases_on ‘m = n’ >> fs[] >> Cases_on ‘n’ >> Cases_on ‘m’ >>
          fs[netout_limit_def] 
          >- (rename [‘RTC (netin_trans conf c) NB NI’,‘netout_trans conf c NI NE’] >>
              first_x_assum (qspecl_then [‘NI’,‘NE’] assume_tac) >>
              rfs[] >>
              ‘netin_trans conf c NA NB’
                suffices_by metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def] >>
              rw[netin_trans_def] >> qexists_tac ‘LTau’ >> rw[]) >>
          rpt (qpat_x_assum ‘RTC _ NA _’ kall_tac) >>
          rename [‘RTC (netin_trans conf c) NB NI’,‘netout_trans conf c NI NE’] >>
          first_x_assum (qspecl_then [‘NI’,‘NE’] mp_tac) >>
          impl_tac
          >- (rw[] >>
              ‘netin_trans conf c NA NB’
                suffices_by metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def] >>
              rw[netin_trans_def] >> qexists_tac ‘LTau’ >> rw[]) >>
          rw[] >> first_x_assum (drule_all_then assume_tac) >>
          CCONTR_TAC >> fs[] >>
          qpat_x_assum ‘_ ≠ _’ mp_tac >> simp[] >>
          metis_tac[netout_limit_unique])

              )
          ‘m ≠ 0’
            by (CCONTR_TAC >> Cases_on ‘n’ >> fs[netout_limit_def]
           Cases_on ‘n’ >>

          ‘∃n2 n3.
            RTC (netin_trans conf c)’
                ‘ffi_wf’

           Cases_on ‘n’ >> rw[netout_limit_def] >>
          fs[]
          >- (fs[netout_limit_def] >>
              rename [‘RTC (netin_trans conf c) NB NI’,‘netout_trans conf c NI NE’] >>
              MAP_EVERY qexists_tac [‘NI’,‘NE’] >> rw[] >>
              ‘netin_trans conf c NA NB’
                suffices_by metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def] >>
              fs[netin_trans_def] >> qexists_tac ‘LTau’ >> rw[]) >>
          CCONTR_TAC
          ‘qC ≠ qB’
            by metis_tac[] >>
          )
  (* Handle non-empty queue inductively *)
  >- (rw[] >> qabbrev_tac ‘fs = st.ffi_state’ >>
      PairCases_on ‘fs’ >> rename1 ‘(c,q,N)’ >> rename1 ‘h::tl’ >>
      first_x_assum (qspecl_then [‘st with ffi_state := (c,normalise_queues (q |+ (src,tl)),N)’,‘src’] assume_tac) >>
      Cases_on ‘LENGTH h ≠ SUC conf.payload_size’
      >- (ntac 2 DISJ2_TAC >> qexists_tac ‘[]’ >>
          rw[ffi_fail_stream_def,call_FFI_def,
              valid_receive_call_format_def,comms_ffi_oracle_def,
              ffi_receive_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rename1 ‘case x of (m,ns) => _’ >>
              PairCases_on ‘x’ >> fs[strans_rules] >>
              ‘∃s2. strans conf (c,q,N) (ARecv src h) s2’
                suffices_by metis_tac[functional_ARecv] >>
              metis_tac[strans_rules])
          >- (fs[strans_rules] >>
              ‘∃s2. strans conf (c,q,N) (ARecv src h) s2’
                by metis_tac[strans_rules] >>
              qexists_tac ‘(h,s2)’ >> rw[])) >>
      Cases_on ‘final h’
      >- (DISJ1_TAC >> qexists_tac ‘[h]’ >>
          rw[ffi_term_stream_def,call_FFI_def,valid_receive_call_format_def,
             comms_ffi_oracle_def, ffi_receive_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rename1 ‘case x of (m,ns) => _’ >>
              PairCases_on ‘x’ >> fs[strans_rules] >>
              ‘∃s2. strans conf (c,q,N) (ARecv src h) s2’
                suffices_by metis_tac[functional_ARecv] >>
              metis_tac[strans_rules])
          >- (fs[strans_rules] >>
              ‘∃s2. strans conf (c,q,N) (ARecv src h) s2’
                by metis_tac[strans_rules] >>
              qexists_tac ‘(h,s2)’ >> rw[])) >>
      rfs[] >>
      ‘ffi_wf (c,normalise_queues (q |+ (src,tl)),N)’
        by fs[ffi_wf_def] >>
      fs[]
      >- (DISJ1_TAC >> qexists_tac ‘h::cs’ >>
          Cases_on ‘cs’ >>
          rw[ffi_term_stream_def,call_FFI_def,valid_receive_call_format_def,
             comms_ffi_oracle_def, ffi_receive_def] >>
          fs[ffi_term_stream_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rename1 ‘case x of (m,ns) => _’ >>
              PairCases_on ‘x’ >> fs[strans_rules] >>
              ‘strans conf (c,q,N) (ARecv src h) (c,normalise_queues (q |+ (src,tl)),N)’
                by metis_tac[strans_rules] >>
              ‘x0 = h’
                by metis_tac[functional_ARecv] >>
              rw[] >>
              ‘ffi_wf (x1,x2,x3)’
                by metis_tac[strans_pres_wf] >>
              ‘ffi_eq conf (x1,x2,x3) (c,normalise_queues (q |+ (src,tl)),N)’
                suffices_by (rw[] >>
                             qmatch_goalsub_abbrev_tac ‘ffi_term_stream _ x _ _’ >>
                             qmatch_asmsub_abbrev_tac  ‘ffi_term_stream _ y _ _’ >>
                             qspecl_then [‘conf’,‘x’,‘y’] assume_tac ffi_eq_term_stream >>
                             MAP_EVERY qunabbrev_tac [‘x’,‘y’] >> rfs[] >>
                             ‘ffi_wf (x1,x2,x3)’
                                by metis_tac[strans_pres_wf] >>
                             qmatch_goalsub_abbrev_tac ‘foo src (h'::t)’ >>
                             fs []) >>
              metis_tac[ffi_eq_pres,ffi_eq_equivRel,equivalence_def,reflexive_def])
          >- (qexists_tac ‘(h,(c,normalise_queues (q|+(src,tl)),N))’ >>
              rw[] >> metis_tac[strans_rules]))
      >- (DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘h::cs’ >>
          rw[ffi_divg_stream_def,call_FFI_def,valid_receive_call_format_def,
             comms_ffi_oracle_def, ffi_receive_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rw[AllCaseEqs()] >>
              rename1 ‘(λ(m,ns). strans _ _ (ARecv src m) ns) x’ >>
              PairCases_on ‘x’ >> fs[] >>
              ‘strans conf (c,q,N) (ARecv src h) (c,normalise_queues (q |+ (src,tl)),N)’
                by metis_tac[strans_rules] >>
              ‘x0 = h’
                by metis_tac[functional_ARecv] >>
              rw[] >>
              ‘ffi_wf (x1,x2,x3)’
                by metis_tac[strans_pres_wf] >>
              ‘ffi_eq conf (x1,x2,x3) (c,normalise_queues (q |+ (src,tl)),N)’
                suffices_by (rw[] >>
                             qmatch_goalsub_abbrev_tac ‘ffi_divg_stream _ x _ _’ >>
                             qmatch_asmsub_abbrev_tac  ‘ffi_divg_stream _ y _ _’ >>
                             qspecl_then [‘conf’,‘x’,‘y’] assume_tac ffi_eq_divg_stream >>
                             MAP_EVERY qunabbrev_tac [‘x’,‘y’] >> rfs[] >>
                             ‘ffi_wf (x1,x2,x3)’
                                by metis_tac[strans_pres_wf] >>
                             fs[]) >>
              metis_tac[ffi_eq_pres,ffi_eq_equivRel,equivalence_def,reflexive_def])
          >- (qexists_tac ‘(h,(c,normalise_queues (q|+(src,tl)),N))’ >>
              rw[] >> metis_tac[strans_rules]))
      >- (DISJ2_TAC >> DISJ2_TAC >> qexists_tac ‘h::cs’ >>
          rw[ffi_fail_stream_def,call_FFI_def,valid_receive_call_format_def,
             comms_ffi_oracle_def, ffi_receive_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rw[AllCaseEqs()] >>
              rename1 ‘(λ(m,ns). strans _ _ (ARecv src m) ns) x’ >>
              PairCases_on ‘x’ >> fs[] >>
              ‘strans conf (c,q,N) (ARecv src h) (c,normalise_queues (q |+ (src,tl)),N)’
                by metis_tac[strans_rules] >>
              ‘x0 = h’
                by metis_tac[functional_ARecv] >>
              rw[] >>
              ‘ffi_wf (x1,x2,x3)’
                by metis_tac[strans_pres_wf] >>
              ‘ffi_eq conf (x1,x2,x3) (c,normalise_queues (q |+ (src,tl)),N)’
                suffices_by (rw[] >>
                             qmatch_goalsub_abbrev_tac ‘ffi_fail_stream _ x _ _’ >>
                             qmatch_asmsub_abbrev_tac  ‘ffi_fail_stream _ y _ _’ >>
                             qspecl_then [‘conf’,‘x’,‘y’] assume_tac ffi_eq_fail_stream >>
                             MAP_EVERY qunabbrev_tac [‘x’,‘y’] >> rfs[] >>
                             ‘ffi_wf (x1,x2,x3)’
                                by metis_tac[strans_pres_wf] >>
                             fs[]) >>
              metis_tac[ffi_eq_pres,ffi_eq_equivRel,equivalence_def,reflexive_def])
          >- (qexists_tac ‘(h,(c,normalise_queues (q|+(src,tl)),N))’ >>
              rw[] >> metis_tac[strans_rules]))) >>
  (* Handle base case empty queue by induction on network *)
  rw[] >>
  qspecl_then [‘conf’,‘(λ(c,_,_). c) st.ffi_state’, ‘(λ(_,_,n). n) st.ffi_state’]
              assume_tac netout_limit_exists >>
  pop_assum mp_tac >> impl_tac
  >- (rename1 ‘(λ(_,_,n).n) ffist’ >> PairCases_on ‘ffist’ >> fs[ffi_wf_def]) >>
  qabbrev_tac ‘c = (λ(c,_,_).c) st.ffi_state’ >>
  qabbrev_tac ‘q = (λ(_,q,_).q) st.ffi_state’ >>
  qabbrev_tac ‘N = (λ(_,_,n).n) st.ffi_state’ >>
  rw[] >> Induct_on ‘n’
  >- (rw[] >> DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘[]’ >> rw[ffi_divg_stream_def] >>
      
  Induct_on ‘(λ(x,y,z). z) st.ffi_state’
  (* Empty queue, Empty Network *)
  >- (rw[] >> DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘[]’ >>
      rw[ffi_divg_stream_def,call_FFI_def,valid_receive_call_format_def,
         comms_ffi_oracle_def, ffi_receive_def] >>
      rename1 ‘some (m,ns). strans conf st.ffi_state (ARecv src m) ns’ >>
      ‘(some (m,ns). strans conf st.ffi_state (ARecv src m) ns) = NONE’
        suffices_by rw[] >>
      rw[some_def] >>
      rename1 ‘¬_ x’ >>
      PairCases_on ‘x’ >>
      rw[] >>
      ‘∀conf s1 L s2.
        strans conf s1 L s2 ⇒
        case s1 of (c1,q1,N1) =>
        case s2 of (c2,q2,N2) =>
        (∀src m.
          ([] ≠ qlk q1 src) ∨
          (N1 ≠ NNil)       ∨
          (L ≠ ARecv src m))’
        suffices_by (rw[] >> CCONTR_TAC >>
                     fs[] >>
                     qmatch_asmsub_abbrev_tac ‘strans _ S1 L S2’ >>
                     first_x_assum (qspecl_then [‘conf’,‘S1’,‘L’,‘S2’] assume_tac) >>
                     MAP_EVERY qunabbrev_tac [‘L’,‘S2’] >>
                     fs[] >> PairCases_on ‘S1’ >> fs[]) >>
      rpt (first_x_assum (K ALL_TAC)) >>
      ho_match_mp_tac strans_ind >>
      rw[] >>
      first_x_assum (qspecl_then [‘src’,‘m’] assume_tac) >>
      rw[] >> TRY (metis_tac[]) >>
      DISJ2_TAC >> DISJ1_TAC >>
      rename1 ‘trans conf NA _ NB’ >>
      MAP_EVERY Cases_on [‘NA’,‘NB’] >>
      fs[Once trans_cases])
  (* Empty queue, Parallel Network (with IH) *)
  >- (* Induct on Parallel structure *)cheat
  (* Empty queue, Single Endpoint network case *)
  >- (rw[] >> reverse (Cases_on ‘l = src’)
      (* Case where node is not the required sender (diverges) *)
      >- (DISJ2_TAC >> DISJ1_TAC >>
          qexists_tac ‘[]’ >>
          rw[ffi_divg_stream_def,call_FFI_def,
             comms_ffi_oracle_def,valid_receive_call_format_def,
             ffi_receive_def] >>
          rename1 ‘some (m,ns). strans conf st.ffi_state (ARecv src m) ns’ >>
          ‘(some (m,ns). strans conf st.ffi_state (ARecv src m) ns) = NONE’
            suffices_by rw[] >>
          rw[some_def] >>
          rename1 ‘¬_ x’ >>
          PairCases_on ‘x’ >>
          rw[] >>
          ‘∀conf s1 L s2.
            strans conf s1 L s2 ⇒
            case s1 of (c1,q1,N1) =>
            case s2 of (c2,q2,N2) =>
            ∀i s e.
            (N1 = NEndpoint i s e) ⇒
            (∀src m.
              ([] ≠ qlk q1 src) ∨
              (i  = src) ∨
              (L  ≠ ARecv src m))’
            suffices_by (rw[] >> CCONTR_TAC >>
                         fs[] >>
                         first_x_assum (drule_all_then assume_tac) >>
                         rename1 ‘ffi_wf S1’ >>
                         PairCases_on ‘S1’ >>
                         fs[] >> metis_tac[]) >>
          rpt (first_x_assum (K ALL_TAC)) >>
          ho_match_mp_tac strans_ind >>
          rw[]
          >- (fs[Once trans_cases] >>
              metis_tac[])
          >- (‘sp = i’
                by (CCONTR_TAC >> fs[Once trans_cases] >>
                    metis_tac[]) >>
              fs[] >> rename1 ‘trans _ _ _ NB’ >>
              ‘∃s2 e2. NB = NEndpoint i s2 e2’
                by (fs[Once trans_cases] >> metis_tac[]) >>
              first_x_assum (drule_all_then assume_tac) >>
              first_x_assum (qspecl_then [‘src’,‘m’] strip_assume_tac) >>
              rw[] >> Cases_on ‘i = src’ >> rw[] >>
              rename1 ‘[] ≠ qlk (qpush q i d) src’ >>
              ‘qlk q src = qlk (qpush q i d) src’
                suffices_by rw[] >>
              rw[qpush_def])) >>
      (* Case where node is required sender, Induct on code *)
      rename1 ‘NEndpoint l s e’ >> Induct_on ‘e’ >> rw[]
      (* Nil case *)
      >- (DISJ2_TAC >> DISJ1_TAC >>
          qexists_tac ‘[]’ >>
          rw[ffi_divg_stream_def,call_FFI_def,
             comms_ffi_oracle_def,valid_receive_call_format_def,
             ffi_receive_def] >>
          rename1 ‘strans conf st.ffi_state (ARecv l _) _’ >>
          ‘(some (m,ns). strans conf st.ffi_state (ARecv l m) ns) = NONE’
            suffices_by rw[] >>
          rw[some_def] >>
          rename1 ‘¬_ x’ >>
          PairCases_on ‘x’ >>
          rw[] >>
          ‘∀conf s1 L s2.
            strans conf s1 L s2 ⇒
            case s1 of (c1,q1,N1) =>
            case s2 of (c2,q2,N2) =>
            ∀i s e.
            (N1 = NEndpoint i s e) ⇒
            (∀src m.
              ([] ≠ qlk q1 src) ∨
              (e  ≠ Nil) ∨
              (L  ≠ ARecv src m))’
            suffices_by (rw[] >> CCONTR_TAC >>
                         fs[] >>
                         first_x_assum (drule_all_then assume_tac) >>
                         rename1 ‘ffi_wf S1’ >>
                         PairCases_on ‘S1’ >>
                         fs[] >> metis_tac[]) >>
          rpt (first_x_assum (K ALL_TAC)) >>
          ho_match_mp_tac strans_ind >>
          rw[] >> fs[Once trans_cases] >>
          metis_tac[])
      (* Send case *)
      >- cheat
      (* Receive case *)
      >- cheat
      (* IfThen case *)
      >- cheat
      >- cheat)
*)
QED

val _ = export_theory ();

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
  reverse (Induct_on ‘qlk ((λ(_,q,_).q) st.ffi_state) src’)
  >- (rw[] >> qabbrev_tac ‘fs = st.ffi_state’ >>
      PairCases_on ‘fs’ >> rename1 ‘(c,q,N)’ >> rename1 ‘h::tl’ >>
      first_x_assum (qspecl_then [‘st with ffi_state := (c,q |+ (src,tl),N)’,‘src’] assume_tac) >>
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
      Cases_on ‘final h’ >>
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
      rfs[ffi_wf_def]
      >- (DISJ1_TAC >> qexists_tac ‘h::cs’ >>
          Cases_on ‘cs’ >>
          rw[ffi_term_stream_def,call_FFI_def,valid_receive_call_format_def,
             comms_ffi_oracle_def, ffi_receive_def] >>
          fs[ffi_term_stream_def] >>
          DEEP_INTRO_TAC some_intro >>
          rw[]
          >- (rename1 ‘case x of (m,ns) => _’ >>
              PairCases_on ‘x’ >> fs[strans_rules] >>
              ‘x0 = h’
                suffices_by rw[]
              ‘strans conf (c,q,N) (ARecv src h) (c,q |+ (src,tl),N)’
                suffices_by metis_tac[functional_ARecv] >>
              metis_tac[strans_rules])


          rw[Once ffi_term_stream_def] >>
          )

          fs[Once strans_cases]
          >- (first_x_assum (assume_tac o GSYM) >>
              last_x_assum (assume_tac o GSYM) >>
              fs[])
          strans_ind
      rfs[ffi_wf_def]
      >- (DISJ1_TAC >> Cases_on ‘final h’
          >- (qexists_tac ‘[h]’ >>
              rw[ffi_term_stream_def,call_FFI_def,valid_receive_call_format_def,
                 comms_ffi_oracle_def,ffi_receive_def] >>
              DEEP_INTRO_TAC some_intro >>
              rw[]
              >- (rename1 ‘case x of (m,ns) => _’ >>
                  PairCases_on ‘x’ >> fs[strans_rules] >>
                  ‘LENGTH x0 = SUC conf.payload_size’
                    suffices_by (rw[])
              >- (‘(λ(m,ns). strans conf (c,q,N) (ARecv src m) ns) (h,(c,q |+ (src,tl),N))’
                    suffices_by metis_tac[] >>
                  rw[strans_rules]) >>
              SELECT_ELIM_TAC)
      Induct_on ‘qlk q src’ >> rw[]
      >- (cheat) >>
      rename1 ‘h::tl’ >>
      first_x_assum (qspecl_then [‘q |+ (src,tl)’,‘src’] assume_tac) >>

      Cases_on ‘st.ffi_state’ >> rename1 ‘(q,r)’ >>
      Cases_on ‘qlk q src’
      rw[] >>
      Cases_on ‘∃cs. ffi_divg_stream conf st src cs’ >> 
      rw[] >>
      fs[ffi_term_stream_def,ffi_divg_stream_def] >>
      CCONTR_TAC >> rw[] >> fs[] >> 
*)
QED

val _ = export_theory ();
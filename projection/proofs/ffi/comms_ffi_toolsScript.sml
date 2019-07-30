open HolKernel boolLib Parse bossLib;
open optionTheory
     relationTheory;
open ffiTheory;
open bisimulationTheory
     payloadSemanticsTheory
     payloadLangTheory
     comms_ffi_modelTheory;

val _ = new_theory "comms_ffi_tools";

val JSPEC_THEN =
  fn spTr => fn nxTc => fn spTh => 
    FIRST[qspec_then spTr nxTc spTh, Q.ISPEC_THEN spTr nxTc spTh];

fun JSPECL_THEN []            = (fn nxTc => (fn spTh => nxTc spTh))
  | JSPECL_THEN (spTr::spTrs) =
    (fn nxTc =>
      (fn spTh =>
        let
          val recFunc = (JSPECL_THEN spTrs nxTc)
        in
          JSPEC_THEN spTr recFunc spTh
        end)
    ); 

(* Invariants under network transformation *)

Definition net_has_node_def:
  (net_has_node NNil              _  = F)                          ∧
  (net_has_node (NPar n1 n2)      nd = (net_has_node n1 nd ∨
                                        net_has_node n2 nd   )) ∧
  (net_has_node (NEndpoint p _ _) nd = (p = nd))
End

Theorem trans_pres_nodes:
  ∀conf s0 l s1.
    trans conf s0 l s1 ⇒
      (∀nd. net_has_node s0 nd ⇔ net_has_node s1 nd)
Proof
  Induct_on ‘trans’ >> rw[net_has_node_def]
QED

Definition net_wf_def:
  (net_wf NNil = T) ∧
  (net_wf (NEndpoint _ _ _) = T) ∧
  (net_wf (NPar n1 n2) = (net_wf n1 ∧ net_wf n2 ∧
                         (∀nd.
                          ¬net_has_node n1 nd ∨
                          ¬net_has_node n2 nd)))
End

Theorem trans_pres_wf:
  ∀conf s0 l s1.
    trans conf s0 l s1 ⇒
      (net_wf s0 ⇔ net_wf s1)
Proof
  Induct_on ‘trans’ >>
  rw[net_wf_def] >>
  metis_tac[trans_pres_nodes,EQ_IMP_THM]
QED

(* Conditions under which networks can receive and send *)

Theorem trans_receive_cond:
  ∀conf sp N d dp.
    (sp ≠ dp ∧ net_has_node N dp) ⇔
    (∃N'. trans conf N (LReceive sp d dp) N') 
Proof
  rw[EQ_IMP_THM]
  >- (Induct_on ‘N’ >> rw[net_has_node_def] >> metis_tac[trans_rules])
  >- (first_x_assum mp_tac >> Induct_on ‘trans’ >> rw[net_has_node_def])
  >- (first_x_assum mp_tac >> Induct_on ‘trans’ >> rw[net_has_node_def])
QED

Theorem trans_send_cond:
  ∀conf sp N d dp.
    (∃N'. trans conf N (LSend sp d dp) N') ⇒
    (sp ≠ dp ∧ net_has_node N sp)
Proof
  rw[] >> first_x_assum mp_tac >>
  Induct_on ‘trans’ >> rw[net_has_node_def]
QED

(* Invariants under ffi state transformation *)

Definition ffi_has_node_def:
  ffi_has_node nd (P,Q,N) =
    net_has_node N nd
End

Theorem strans_pres_pnum:
  ∀conf s1 L s2.
    strans conf s1 L s2 ⇒
      FST s1 = FST s2
Proof
  rw[Once strans_cases] >>
  simp[]
QED

Theorem strans_queue_pres:
  ∀conf P Q1 N1 D M Q2 N2.
    strans conf (P,Q1,N1) (ASend D M) (P,Q2,N2) ⇒
      isPREFIX Q1 Q2
Proof
  Induct_on ‘strans’ >> rw[] >>
  metis_tac [rich_listTheory.IS_PREFIX_APPEND1]
QED

Theorem strans_pres_nodes:
  ∀conf s0 l s1.
    strans conf s0 l s1 ⇒
      (∀nd. ffi_has_node nd s0 ⇔ ffi_has_node nd s1)
Proof
  Induct_on ‘strans’ >> rw[ffi_has_node_def] >>
  metis_tac[trans_pres_nodes]
QED

Definition ffi_wf_def:
  ffi_wf (P,Q,N) = net_wf N
End

Theorem strans_pres_wf:
  ∀conf s1 L s2.
    strans conf s1 L s2 ⇒
      (ffi_wf s1 ⇔ ffi_wf s2)
Proof
  Induct_on ‘strans’ >> rw[ffi_wf_def] >>
  metis_tac[trans_pres_wf]
QED

(* Notion of ffi equivalence *)
Definition ffi_eq_def:
  ffi_eq conf = BISIM_REL (strans conf)
End

Theorem ffi_eq_equivRel:
  ∀conf. equivalence (ffi_eq conf)
Proof
  rw [ffi_eq_def,BISIM_REL_IS_EQUIV_REL]
QED

Theorem ffi_eq_net_ltau:
  ∀conf cpNum q N1 N2.
    trans conf N1 LTau N2 ⇒
    ffi_eq conf (cpNum,q,N1) (cpNum,q,N2)
Proof
  cheat
QED

(* TODO: Put in renames for robustness! *)
Theorem net_functional:
  ∀conf N1 N2A N2B L.
    L ≠ LTau ∧
    trans conf N1 L N2A ∧
    trans conf N1 L N2B ∧
    net_wf N1 ⇒
    N2A = N2B
Proof
  Cases_on ‘L’ >> fs[] >>
  Induct_on ‘trans’ >> rw[]
  >- (fs[Once trans_cases] >>
      ‘LENGTH d' ≤ n + conf.payload_size’
        by fs[pad_def] >>
      fs[])
  >- (fs[Once trans_cases] >>
      ‘LENGTH d' > n + conf.payload_size’
        by fs[pad_def] >>
      fs[])
  >- (fs[net_wf_def] >>
      ‘¬(∃n2a. trans conf n2 (LSend l l0 l1) n2a)’
        by metis_tac[trans_send_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- (fs[net_wf_def] >>
      ‘¬(∃n1a. trans conf n1 (LSend l l0 l1) n1a)’
        by metis_tac[trans_send_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- fs[Once trans_cases]
  >- (fs[net_wf_def] >>
      ‘¬(∃n2a. trans conf n2 (LReceive l l0 l1) n2a)’
        by metis_tac[trans_receive_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- (fs[net_wf_def] >>
      ‘¬(∃n1a. trans conf n1 (LReceive l l0 l1) n1a)’
        by metis_tac[trans_receive_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
QED


Theorem ffi_eq_mutate_self:
  ∀conf SA L SB1 SB2.
    ffi_wf SA ∧
    strans conf SA L SB1 ∧
    strans conf SA L SB2   ⇒
    ffi_eq conf SB1 SB2
Proof
  Cases_on ‘L’ >> fs[] >>
  Induct_on ‘strans’ >> rw[]
  >- (rename1 ‘ffi_wf (c,q,NI)’ >>
      rename1 ‘ffi_wf’ >>
      ‘ffi_wf (c,q,N')’
        by metis_tac[ffi_wf_def,trans_pres_wf] >> 
      fs[] >>
      ‘∃SB2E. strans conf (c,q,N') (ASend l l0) SB2E ∧
              ffi_eq conf SB2 SB2E’
        suffices_by (cheat) >>
      cheat) >>
  cheat
QED

Theorem ffi_eq_pres:
  ∀conf SA1 SA2 L SB1 SB2.
    ffi_wf SA1 ∧
    ffi_wf SA2 ∧
    ffi_eq conf SA1 SA2   ∧
    strans conf SA1 L SB1 ∧
    strans conf SA2 L SB2   ⇒
    ffi_eq conf SB1 SB2
Proof
  rw[] >>
  ‘∃SBI. strans conf SA2 L SBI ∧ ffi_eq conf SB1 SBI’
    suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,
                          transitive_def,ffi_eq_mutate_self] >>
  qmatch_goalsub_abbrev_tac ‘∃SBI. strans conf SA2 L SBI ∧ atP SBI’ >>
  fs[ffi_eq_def,BISIM_REL_def,BISIM_def] >>
  last_assum (drule_then (JSPEC_THEN ‘L’ strip_assume_tac)) >>
  last_x_assum (assume_tac o REWRITE_RULE [GSYM BISIM_def]) >>
  qpat_x_assum ‘∀a. strans conf SA2 L a ⇒ _’ (K ALL_TAC) >>
  first_x_assum (JSPEC_THEN ‘SB1’ strip_assume_tac) >>
  rfs[] >> rename1 ‘R SB1 SBI’ >> qexists_tac ‘SBI’ >>
  fs[] >> qunabbrev_tac ‘atP’ >> simp[BISIM_REL_def] >>
  qexists_tac ‘R’ >> simp[BISIM_def] >> fs[]
QED


(* Notions of send validity, both in terms of format and actual destination *)
Definition valid_send_dest_def:
  valid_send_dest dest ffiSt = ((FST ffiSt ≠ dest) ∧ (ffi_has_node dest ffiSt))
End

Definition valid_send_call_format_def:
  valid_send_call_format conf dest s c bytes =
    ((s = "send") ∧ (c = dest) ∧ (LENGTH bytes = SUC conf.payload_size))
End

Theorem strans_send_cond:
  ∀S1 dest.
    valid_send_dest dest S1 ⇒
    (∀bytes. ∃S2.
      strans conf S1 (ASend dest bytes) S2)
Proof
  rw[] >> Cases_on ‘S1’ >> qmatch_goalsub_rename_tac ‘(P,R)’ >>
  Cases_on ‘R’  >> qmatch_goalsub_rename_tac ‘(P,Q1,N1)’ >>
  ‘∃N2. trans conf N1 (LReceive P bytes dest) N2’
    suffices_by metis_tac[strans_rules] >>
  fs[valid_send_dest_def,ffi_has_node_def] >>
  metis_tac[trans_receive_cond]
QED

Theorem strans_dest_check:
  ∀S1 dest.
    (∃bytes S2.
      strans conf S1 (ASend dest bytes) S2) ⇒
    valid_send_dest dest S1
Proof
  Induct_on ‘strans’ >>
  rw[valid_send_dest_def,ffi_has_node_def] >>
  metis_tac[trans_pres_nodes,trans_receive_cond]
QED

Theorem ffi_eq_sendval:
  ∀conf fs1 fs2.
    ffi_eq conf fs1 fs2 ⇒
    (∀l. valid_send_dest l fs1 ⇔ valid_send_dest l fs2)
Proof
  rw[EQ_IMP_THM] >> 
  qmatch_asmsub_rename_tac ‘valid_send_dest l KS’ >>
  qmatch_goalsub_rename_tac ‘valid_send_dest l US’ >>
  qabbrev_tac ‘ad = REPLICATE (SUC conf.payload_size) (ARB :word8)’ >>
  irule strans_dest_check >>
  drule_then (JSPEC_THEN ‘ad’ strip_assume_tac) strans_send_cond >> 
  rename1 ‘strans conf KS (ASend l ad) S2’ >>
  MAP_EVERY qexists_tac [‘conf’,‘ad’] >>
  metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_def]
QED


(* Modelling invariants on FFI *)
Definition ffi_accepts_rel_def:
  ffi_accepts_rel stpred pred oracle =
  ∀st s conf bytes.
    stpred st.ffi_state ∧ st.oracle = oracle ∧ pred s conf bytes ⇒
    ∃ffi. st.oracle s st.ffi_state conf bytes = Oracle_return ffi bytes ∧
          stpred ffi
End

(* Proving the major send invariant *)
Theorem send_invariant:
  ∀ conf l.
    ffi_accepts_rel (valid_send_dest l) (valid_send_call_format conf l) (comms_ffi_oracle conf)
Proof
  rw[valid_send_dest_def,ffi_accepts_rel_def,valid_send_call_format_def,
     comms_ffi_oracle_def,ffi_send_def] >>
  DEEP_INTRO_TAC some_intro >>
  qmatch_goalsub_abbrev_tac ‘strans _ s _’ >>
  first_x_assum (K ALL_TAC) >>
  qpat_x_assum ‘_ = comms_ffi_oracle conf’ (K ALL_TAC) >>
  rw[]
  >- (rename1 ‘strans _ s _ s2’ >>
      Cases_on ‘s’ >> Cases_on ‘s2’ >>
      metis_tac[strans_pres_pnum])
  >- (rename1 ‘strans _ s _ s2’ >>
      Cases_on ‘s’ >> Cases_on ‘s2’ >>
      metis_tac[strans_pres_nodes])
  >- metis_tac[valid_send_dest_def,strans_send_cond]
QED

(* Modelling limited acceptance on FFI *)
Definition ffi_laccepts_def:
  (ffi_laccepts 0 oracle ipred mpred fpred st =
    ∀s conf bytes.
      ipred s conf bytes ⇒
      ∃ffi nbytes.
          (oracle s st conf bytes = Oracle_return ffi nbytes) ∧
          (fpred nbytes))                                                       ∧
  (ffi_laccepts (SUC n) oracle ipred mpred fpred st =
    ∀s conf bytes.
      ipred s conf bytes ⇒
        ∃ffi nbytes.
          (oracle s st conf bytes = Oracle_return ffi nbytes) ∧
          (mpred nbytes) ∧
          (ffi_laccepts n oracle ipred mpred fpred ffi))
End

val _ = export_theory ();
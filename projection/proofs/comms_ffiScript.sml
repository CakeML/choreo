open    preamble
        relationTheory
        astBakeryTheory
        payloadSemanticsTheory
        ffiTheory;

val _ = new_theory "comms_ffi";

val _ = type_abbrev("message", “: proc # datum”);
val _ = type_abbrev("queue" , “: message list”);
val _ = type_abbrev("total_state" , “: proc # queue # network”);

val _ = Datatype ‘
 action = ASend proc datum
          | ARecv proc datum
’;

val (strans_rules,strans_ind,strans_cases) = Hol_reln
‘
  (* ARecv *)
  (∀conf c q q1 ms mc q2 N.
    (q = q1 ++ [(ms,mc)] ++ q2) ∧
    EVERY (λ(p,_). p ≠ ms) q1 
    ⇒ strans conf (c,q,N) (ARecv ms mc) (c, q1 ++ q2, N))

  (* LTauL *)
∧ (∀conf c q q' N N' N'' α.
     trans conf N LTau N' ∧
     strans conf (c,q,N') α (c,q',N'')
     ⇒  strans conf (c,q,N) α (c,q',N''))

  (* LTauR *)
∧ (∀conf c q q' N N' N'' α.
     strans conf (c,q,N) α (c,q',N') ∧
     trans conf N' LTau N''
     ⇒  strans conf (c,q,N) α (c,q',N''))

  (* LSend *)
∧ (∀conf c q q' N N' N'' sp d α.
     trans conf N (LSend sp d c) N' ∧
     strans conf (c,q++[(sp,d)],N') α (c,q',N'')
     ⇒  strans conf (c,q,N) α (c,q',N''))

  (* ASend *)
∧ (∀conf c q N N' rp d.
     trans conf N (LReceive c d rp) N'
     ⇒  strans conf (c,q,N) (ASend rp d) (c,q,N'))
’;

Definition bisim_def:
  bisim ts R = ∀p q α.
                R p q ⇒
                (∀p'. ts p α p' ⇒ (∃q'. ts q α q' ∧ R p' q')) ∧
                (∀q'. ts q α q' ⇒ (∃p'. ts p α p' ∧ R p' q'))
End

Definition bisimRel_def:
  bisimRel ts p q = ∃R. bisim ts R ∧ R p q
End


Theorem bisimRel_equivRel:
  ∀ts. equivalence (bisimRel ts)
Proof
  rw [equivalence_def]
  >- (rw[reflexive_def, bisimRel_def] >>
      qexists_tac ‘$=’ >>
      rw[bisim_def])
  >- (rw[symmetric_def, bisimRel_def] >>
      rw[EQ_IMP_THM] >>
      qexists_tac ‘SC R’ >>
      fs[bisim_def,SC_DEF] >>
      metis_tac[])
  >- (rw[transitive_def,bisimRel_def] >>
      qexists_tac ‘λa c. ∃b. R a b ∧ R' b c’ >>
      fs[bisim_def] >>
      metis_tac[])
QED

Definition ffi_eq_def:
  ffi_eq conf = bisimRel (strans conf)
End

Theorem ffi_eq_equivRel:
  ∀conf. equivalence (ffi_eq conf)
Proof
  rw [ffi_eq_def,bisimRel_equivRel]
QED

Definition ffi_send_def:
  ffi_send conf os dest data =
    if (∃ns. strans conf os (ASend dest data) ns) then
      Oracle_return (@ns. strans conf os (ASend dest data) ns) data
    else
      Oracle_final FFI_diverged
End

Definition ffi_receive_def:
  ffi_receive conf os src _ =
    if (∃p. strans conf os (ARecv src (FST p)) (SND p)) then
      let (m,ns) = (@p. strans conf os (ARecv src (FST p)) (SND p)) in
        Oracle_return ns m
    else
      Oracle_final FFI_diverged
End

Definition comms_ffi_oracle_def:
  comms_ffi_oracle conf name =
    if name = "send" then
        ffi_send conf
    else if name = "receive" then
        ffi_receive conf
    else
        (λ _ _ _. Oracle_final FFI_failed)
End


val _ = export_theory ();

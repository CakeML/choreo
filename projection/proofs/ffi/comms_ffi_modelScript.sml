open HolKernel boolLib Parse bossLib;
open ffiTheory;
open payloadSemanticsTheory;

val _ = new_theory "comms_ffi_model";

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

Definition ffi_send_def:
  ffi_send conf os dest data =
  if (LENGTH data ≠ SUC conf.payload_size) then
    Oracle_final FFI_failed
  else
    case some ns. strans conf os (ASend dest data) ns of
      SOME ns =>  Oracle_return ns data
    | NONE    =>  Oracle_final FFI_diverged
End

Definition ffi_receive_def:
  ffi_receive conf os src _ =
    case some (m,ns). strans conf os (ARecv src m) ns of
      SOME (m,ns) =>  Oracle_return ns m
    | NONE        =>  Oracle_final FFI_diverged
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

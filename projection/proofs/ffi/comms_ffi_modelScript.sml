open HolKernel boolLib Parse bossLib;
open ffiTheory;
open payloadSemanticsTheory;

val _ = new_theory "comms_ffi_model";

Type queues = “: proc |-> datum list”;
Type total_state = “: proc # queues # network”;

Datatype:
 action = ASend proc datum
          | ARecv proc datum
End

Inductive strans:
  (* ARecv *)
  (∀conf c q ms mc tl N.
    qlk q ms = mc::tl
    ⇒ strans conf (c,q,N) (ARecv ms mc) (c,q |+ (ms,tl), N)) ∧ 

  (* LTauL *)
  (∀conf c q q' N N' N'' α.
     trans conf N LTau N' ∧
     strans conf (c,q,N') α (c,q',N'')
     ⇒  strans conf (c,q,N) α (c,q',N'')) ∧

  (* LTauR *)
  (∀conf c q q' N N' N'' α.
     strans conf (c,q,N) α (c,q',N') ∧
     trans conf N' LTau N''
     ⇒  strans conf (c,q,N) α (c,q',N'')) ∧

  (* LSend *)
  (∀conf c q q' N N' N'' sp d α.
     trans conf N (LSend sp d c) N' ∧
     strans conf (c,qpush q sp d,N') α (c,q',N'')
     ⇒  strans conf (c,q,N) α (c,q',N'')) ∧

  (* ASend *)
  (∀conf c q N N' rp d.
     trans conf N (LReceive c d rp) N'
     ⇒  strans conf (c,q,N) (ASend rp d) (c,q,N'))
End

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

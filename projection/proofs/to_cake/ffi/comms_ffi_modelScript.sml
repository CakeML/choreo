open HolKernel boolLib Parse bossLib;
open ffiTheory;
open payloadSemTheory;

val _ = new_theory "comms_ffi_model";

(* FFI MODEL *)
(* Static Model
    Basic model off FFI or World state at any
    given point in time *)
(* -- Backend Queues *)
Type queues = “: proc |-> datum list”;
(* -- Total FFI State model *)
Type total_state = “: proc # queues # network”;

(* Transition System
    Describes possible transitions of the
    static FFI type based on interaction*)
(* -- FFI interaction actions *)
Datatype:
 action = ASend proc datum
          | ARecv proc datum
End
(* -- Transition system on FFI states *)
Inductive strans:
  (* ARecv *)
  (∀conf c q ms mc tl N.
    qlk q ms = mc::tl
    ⇒ strans conf (c,q,N) (ARecv ms mc) (c,normalise_queues(q |+ (ms,tl)), N)) ∧

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

(* Dynamic Model
     Model of response to FFI calls based on transition system *)
(* -- send call model *)
Definition ffi_send_def:
  ffi_send conf os (dest:word8 list) data =
  if (LENGTH data ≠ SUC conf.payload_size) then
    Oracle_final FFI_failed
  else
    case some ns. strans conf os (ASend (MAP (CHR o w2n) dest) data) ns of
      SOME ns =>  Oracle_return ns data
    | NONE    =>  Oracle_final FFI_diverged
End
(* -- receive call model *)
Definition ffi_receive_def:
  ffi_receive conf os (src:word8 list) _ =
    case some (m,ns). strans conf os (ARecv (MAP (CHR o w2n) src) m) ns of
      SOME (m,ns) =>  Oracle_return ns m
    | NONE        =>  Oracle_final FFI_diverged
End
(* -- total oracle *)
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

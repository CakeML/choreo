open    HolKernel
        Parse
        bossLib
        astBakeryTheory
        ffiTheory;

val _ = new_theory "comms_ffi";

val _ = type_abbrev("message" , “: proc # datum”);

val _ = Datatype‘
  comms_state = <| sent_messages    : message list ;
                   receive_messages : message llist
                 |>
’;

val ffi_send_def =
    Define
    ‘
        ffi_send net_state dest data =
            Oracle_return (net_state with sent_messages updated_by (CONS (dest,data))) data
    ’;

val find_first_def =
    Define
    ‘
    find_first P ll =
        case $OLEAST (λn. ∃x. (LNTH n ll = SOME x) ∧ P x) of
                SOME n => SOME (THE (LTAKE n ll), THE (LNTH n ll), THE (LDROP (SUC n) ll))
            |   NONE   => NONE
    ’;

val ffi_receive_def =
    Define
    ‘
        ffi_receive net_state src _ =
            case find_first (λ(p,_). p = src) net_state.receive_messages of
                    SOME (q1,(p,d),q2)  => Oracle_return (net_state with receive_messages := LAPPEND (fromList q1) q2) d
                |   NONE                => Oracle_final FFI_diverged
    ’;

val comms_ffi_oracle_def = Define
‘
  comms_ffi_oracle name =
    if name = "send" then
        ffi_send
    else if name = "receive" then
        ffi_receive
    else
        (λ _ _ _. Oracle_final FFI_failed)
’;

val _ = export_theory ();

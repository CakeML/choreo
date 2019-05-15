open    HolKernel
        Parse
        bossLib
        astBakeryTheory
        ffiTheory;

val _ = new_theory "comms_ffi2";

val _ = type_abbrev("message" , “: proc # datum”);
val _ = type_abbrev("" , “: message llist”);

val _ = Datatype‘
    action = Send message | Receive proc
’;

val _ = type_abbrev("ext_state" , “: action -> (future # ext_state) option”);


val _ = Datatype‘
  comms_state = <| network     : ext_state ;
                   pres_future : future
                 |>
’;

val ffi_send_def =
    Define
    ‘
        ffi_send cs dest data =
            case cs.network (Send (dest,data)) of
                SOME (f',cs') => Oracle_return (<| network := cs'; pres_future := f' |>) data
            |   NONE          => Oracle_final FFI_failed
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
        ffi_receive cs src _ =
            case find_first (λ(p,_). p = src) cs.pres_future of
                    SOME (q1,(p,data),q2)  => 
                        case cs.network (Receive src) of
                            SOME (f',cs') => if (f' = LAPPEND (fromList q1) q2) then
                                                Oracle_return (<| network := cs'; pres_future := f' |>) data
                                             else
                                                Oracle_final FFI_failed
                        |   NONE => Oracle_final FFI_diverged
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

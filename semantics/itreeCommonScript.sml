open preamble chorLangTheory

val _ = new_theory "itreeCommon";

(* The type of events *)
Datatype:
  event = Send proc datum
        | Receive proc
        | Choose proc bool
        | Select proc
End


(* The type of actions *)
Datatype:
  action = Ok          (* Everything went fine *)
         | Msg datum   (* An incoming message with a value *)
         | Branch bool (* A choice of branch *)
End

(* The type of results  *)
Datatype:
  result = Res unit (* We are finish *)
         | Done     (* A branch has been prune *)
         | Error    (* Something whent wrong *)
End

val _ = export_theory ()

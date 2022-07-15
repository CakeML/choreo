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
  result = End     (* We are finish *)
         | Done    (* A branch has been prune *)
         | Unproj  (* The choreography is unprojectable *)
         | Error   (* Runtime error *)
End

val _ = export_theory ()

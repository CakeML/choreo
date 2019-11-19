open preamble
     astTheory; (* for CakeML syntax-related types in the conf *)
val _ = new_theory "payloadLang";


(* PAYLOAD SYNTAX AND STATE *)
Type varN = “: string”;

Type proc = “: word8 list”;

Type datum = “: word8 list”;


Datatype:
  state = <| bindings : varN |-> datum;
             queues : proc |-> datum list  |>
End

Datatype:
  endpoint = Nil
           | Send proc varN num endpoint
           | Receive proc varN (datum list) endpoint
           | IfThen varN endpoint endpoint
           | Let varN (datum list -> datum) (varN list) endpoint
End         


Datatype:
  network = NNil
          | NPar network network
          | NEndpoint proc state endpoint
End

(* Config type - used in Payload semantics and in CakeML *)
Datatype:
  config = <| payload_size : num;
              length : (modN,varN) id;
              null : (modN,varN) id;
              take : (modN,varN) id;
              drop : (modN,varN) id;
              toList : (modN,varN) id;
              fromList : (modN,varN) id;
              concat : (modN,varN) id;
              append : (modN,varN) id;
              cons : (modN,conN) id;
              nil : (modN,conN) id;
              letModule : modN;                              
              |>
End

val _ = export_theory ()
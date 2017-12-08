open preamble astBakeryTheory (* todo: shouldn't have to depend on astBakery *)

val _ = new_theory "payloadLang";

val _ = Datatype`
endpoint = Nil
         | Send proc (varN + datum) endpoint
         | Receive proc varN (datum list) endpoint
         | IntChoice bool proc endpoint
         | ExtChoice proc endpoint endpoint
         | IfThen varN endpoint endpoint
         | Let varN (datum list -> datum) (varN list) endpoint`

val _ = Datatype `state = <| bindings : varN |-> datum; queue : (proc # datum) list  |>`;
val _ = Datatype `config = <| payload_size : num  |>`;

val _ = Datatype`
network = NNil
        | NPar network network
        | NEndpoint proc state endpoint
`

val _ = export_theory ()

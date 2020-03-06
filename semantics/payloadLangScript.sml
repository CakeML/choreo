open preamble astBakeryTheory (* todo: shouldn't have to depend on astBakery *)
     endpointLangTheory (*for state*)
val _ = new_theory "payloadLang";

val _ = Datatype`
endpoint = Nil
         | Send proc varN num endpoint
         | Receive proc varN (datum list) endpoint
         | IfThen varN endpoint endpoint
         | Let varN (datum list -> datum) (varN list) endpoint`

val _ = Datatype `config = <| payload_size : num  |>`;

val _ = Datatype`
network = NNil
        | NPar network network
        | NEndpoint proc state endpoint
`

val var_names_endpoint_def = Define `
   (var_names_endpoint Nil = [])
/\ (var_names_endpoint (Send p v n e) = v::var_names_endpoint e)
/\ (var_names_endpoint (Receive p v d e) = v::var_names_endpoint e)
/\ (var_names_endpoint (IfThen v e1 e2) = v::var_names_endpoint e1 ++ var_names_endpoint e2)
/\ (var_names_endpoint (Let v f vl e) = v::vl ++ var_names_endpoint e)
`

val free_var_names_endpoint_def = Define `
   (free_var_names_endpoint Nil = [])
/\ (free_var_names_endpoint (Send p v n e) = v::free_var_names_endpoint e)
/\ (free_var_names_endpoint (Receive p v d e) = FILTER ($≠ v) (free_var_names_endpoint e))
/\ (free_var_names_endpoint (IfThen v e1 e2) = v::free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
/\ (free_var_names_endpoint (Let v f vl e) = vl ++ FILTER ($≠ v) (free_var_names_endpoint e))
`

val var_names_network_def = Define `
   (var_names_network NNil = [])
/\ (var_names_network (NEndpoint p s e) = var_names_endpoint e)
/\ (var_names_network (NPar n1 n2) = var_names_network n1 ++ var_names_network n2)`

val free_var_names_network_def = Define `
   (free_var_names_network NNil = [])
/\ (free_var_names_network (NEndpoint p s e) = free_var_names_endpoint e)
/\ (free_var_names_network (NPar n1 n2) = free_var_names_network n1 ++ free_var_names_network n2)`

val final_def = Define `
  final (w::d) = (w = 7w:word8 \/ w = 6w:word8)
  /\ final _ = F
`

val intermediate_def = Define `
  intermediate (w::d) = (w = 2w:word8)
  /\ intermediate _ = F
`

val pad_def = Define `
  pad conf d =
  if LENGTH d = conf.payload_size then       
    7w::d
  else if LENGTH d < conf.payload_size then
    6w::REPLICATE ((conf.payload_size - LENGTH d) - 1) (0w:word8) ++ [1w] ++ d
  else
    2w::TAKE conf.payload_size d
`

val unpad_def = Define `
  (unpad (w::d) =
    if w = 7w \/ w = 2w then d     
    else if w = 6w then
      case SPLITP ($= 1w) d of
        (_,_::d) => d
      | _ => []
    else []
  )
  /\ (unpad _ = [])
  `

val _ = export_theory ()

open preamble astBakeryTheory (* todo: shouldn't have to depend on astBakery *)
     astTheory (* for CakeML syntax-related types in the conf *)
val _ = new_theory "payloadLang";

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

Datatype:
  network = NNil
          | NPar network network
          | NEndpoint proc state endpoint
End

Definition var_names_endpoint_def:
    (var_names_endpoint Nil = [])
  ∧ (var_names_endpoint (Send p v n e) = v::var_names_endpoint e)
  ∧ (var_names_endpoint (Receive p v d e) = v::var_names_endpoint e)
  ∧ (var_names_endpoint (IfThen v e1 e2) = v::var_names_endpoint e1 ++ var_names_endpoint e2)
  ∧ (var_names_endpoint (Let v f vl e) = v::vl ++ var_names_endpoint e)
End

Definition free_var_names_endpoint_def:
    (free_var_names_endpoint Nil = [])
  ∧ (free_var_names_endpoint (Send p v n e) = v::free_var_names_endpoint e)
  ∧ (free_var_names_endpoint (Receive p v d e) = FILTER ($≠ v) (free_var_names_endpoint e))
  ∧ (free_var_names_endpoint (IfThen v e1 e2) = v::free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
  ∧ (free_var_names_endpoint (Let v f vl e) = vl ++ FILTER ($≠ v) (free_var_names_endpoint e))
End

Definition var_names_network_def:
    (var_names_network NNil = [])
  ∧ (var_names_network (NEndpoint p s e) = var_names_endpoint e)
  ∧ (var_names_network (NPar n1 n2) = var_names_network n1 ++ var_names_network n2)
End

Definition free_var_names_network_def:
    (free_var_names_network NNil = [])
  ∧ (free_var_names_network (NEndpoint p s e) = free_var_names_endpoint e)
  ∧ (free_var_names_network (NPar n1 n2) = free_var_names_network n1 ++ free_var_names_network n2)
End

Definition final_def:
    final (w::d) = (w = 7w:word8 ∨ w = 6w:word8)
  ∧ final _ = F
End

Definition intermediate_def:
  intermediate (w::d) = (w = 2w:word8)
  ∧ intermediate _ = F
End

Definition pad_def:
  pad conf d =
  if LENGTH d = conf.payload_size then       
    7w::d
  else if LENGTH d < conf.payload_size then
    6w::REPLICATE ((conf.payload_size - LENGTH d) - 1) (0w:word8) ++ [1w] ++ d
  else
    2w::TAKE conf.payload_size d
End

Definition unpad_def:
  (unpad (w::d) =
    if w = 7w ∨ w = 2w then d     
    else if w = 6w then
      case SPLITP ($= 1w) d of
        (_,_::d) => d
      | _ => []
    else []
  )
  ∧ (unpad _ = [])
End

val _ = export_theory ()

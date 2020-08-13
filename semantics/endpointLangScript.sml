open preamble
(* TODO: shouldn't have to depend on chorLangTheory *)
open chorLangTheory

val _ = new_theory "endpointLang";

Datatype:
  endpoint = Nil
           | Send proc varN endpoint
           | Receive proc varN endpoint
           | IntChoice bool proc endpoint
           | ExtChoice proc endpoint endpoint
           | IfThen varN endpoint endpoint
           | Let varN (datum list -> datum) (varN list) endpoint
           | Fix dvarN endpoint
           | Call dvarN
End

Datatype:
  state = <| bindings : varN |-> datum; queue : (proc # datum) list  |>
End

Datatype:
  network = NNil
          | NPar network network
          | NEndpoint proc state endpoint
End

Definition var_names_endpoint_def:
   (var_names_endpoint Nil = [])
∧ (var_names_endpoint (Send p v e) = v::var_names_endpoint e)
∧ (var_names_endpoint (Receive p v e) = v::var_names_endpoint e)
∧ (var_names_endpoint (IntChoice p b e) = var_names_endpoint e)
∧ (var_names_endpoint (ExtChoice p e1 e2) = var_names_endpoint e1 ++ var_names_endpoint e2)
∧ (var_names_endpoint (IfThen v e1 e2) = v::var_names_endpoint e1 ++ var_names_endpoint e2)
∧ (var_names_endpoint (Let v f vl e) = v::vl ++ var_names_endpoint e)
∧ (var_names_endpoint (Fix dv e) = var_names_endpoint e)
∧ (var_names_endpoint (Call dv) = [])
End

Definition free_var_names_endpoint_def:
   (free_var_names_endpoint Nil = [])
∧ (free_var_names_endpoint (Send p v e) = v::free_var_names_endpoint e)
∧ (free_var_names_endpoint (Receive p v e) = FILTER ($≠ v) (free_var_names_endpoint e))
∧ (free_var_names_endpoint (IntChoice p b e) = free_var_names_endpoint e)
∧ (free_var_names_endpoint (ExtChoice p e1 e2) = free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
∧ (free_var_names_endpoint (IfThen v e1 e2) = v::free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
∧ (free_var_names_endpoint (Let v f vl e) = vl ++ FILTER ($≠ v) (free_var_names_endpoint e))
∧ (free_var_names_endpoint (Fix dv e) = free_var_names_endpoint e)
∧ (free_var_names_endpoint (Call dv) = [])
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

Definition choice_free_endpoint_def:
   (choice_free_endpoint endpointLang$Nil = T)
∧ (choice_free_endpoint (Send p v e) = choice_free_endpoint e)
∧ (choice_free_endpoint (Receive p v e) = choice_free_endpoint e)
∧ (choice_free_endpoint (IntChoice b p e) = F)
∧ (choice_free_endpoint (ExtChoice p e1 e2) = F)
∧ (choice_free_endpoint (IfThen v e1 e2) = (choice_free_endpoint e1 ∧ choice_free_endpoint e2))
∧ (choice_free_endpoint (Let v f vl e) = choice_free_endpoint e)
∧ (choice_free_endpoint (Fix dv e) = choice_free_endpoint e)
∧ (choice_free_endpoint (Call dv) = T)
End

Definition choice_free_network_def:
   (choice_free_network endpointLang$NNil = T)
∧ (choice_free_network (NPar n1 n2) = (choice_free_network n1 ∧ choice_free_network n2))
∧ (choice_free_network (NEndpoint p s e) = choice_free_endpoint e)
End  

Definition net_end_def:
  net_end NNil = T
∧ net_end (NEndpoint _ _ Nil) = T
∧ net_end (NPar l r) = (net_end l ∧ net_end r)
∧ net_end _ = F
End

val _ = export_theory ()

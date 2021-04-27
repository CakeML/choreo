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

Definition dsubst_def:
   dsubst endpointLang$Nil dn e' = endpointLang$Nil
∧ dsubst (Send p v e) dn e' = Send p v (dsubst e dn e')
∧ dsubst (Receive p v e) dn e' = Receive p v (dsubst e dn e')
∧ dsubst (IntChoice b p e) dn e' = IntChoice b p (dsubst e dn e')
∧ dsubst (ExtChoice p e1 e2) dn e' = ExtChoice p (dsubst e1 dn e') (dsubst e2 dn e')
∧ dsubst (IfThen v e1 e2) dn e' = IfThen v (dsubst e1 dn e') (dsubst e2 dn e')
∧ dsubst (Let v f vl e) dn e' = Let v f vl (dsubst e dn e')
∧ dsubst (Fix dn' e) dn e' =
   (if dn = dn' then
      Fix dn' e
    else
      Fix dn' (dsubst e dn e'))
∧ dsubst (Call dn') dn e' =
   (if dn = dn' then
      e'
    else
      Call dn')
End

Definition EP_nodenames_def[simp]:
  EP_nodenames endpointLang$Nil = ∅ ∧
  EP_nodenames (Send dest _ e) = dest INSERT EP_nodenames e ∧
  EP_nodenames (Receive sender _ e) = sender INSERT EP_nodenames e ∧
  EP_nodenames (IfThen _ e1 e2) = EP_nodenames e1 ∪ EP_nodenames e2 ∧
  EP_nodenames (IntChoice _ p e) = p INSERT EP_nodenames e ∧
  EP_nodenames (ExtChoice p e1 e2) = p INSERT (EP_nodenames e1 ∪ EP_nodenames e2) ∧
  EP_nodenames (Let _ _ _ e) = EP_nodenames e ∧
  EP_nodenames (Fix _ e) = EP_nodenames e ∧
  EP_nodenames (Call _) = ∅
End

Definition network_nodenames_def[simp]:
  network_nodenames (NNil) = ∅ ∧
  network_nodenames (NEndpoint p s e) = EP_nodenames e ∧
  network_nodenames (NPar n1 n2) =
  network_nodenames n1 ∪ network_nodenames n2
End

val _ = export_theory ()

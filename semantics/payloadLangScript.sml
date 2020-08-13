open preamble
(* TODO: shouldn't have to depend on chorLangTheory *)
open chorLangTheory
open endpointLangTheory (*for state*)
open astTheory; (* for CakeML syntax-related types in the conf *)

val _ = new_theory "payloadLang";

Datatype:
  state = <| bindings : varN |-> datum;
             funs : (dvarN,'v) alist;
             queues : proc |-> datum list  |>
End

Datatype:
  endpoint = Nil
           | Send proc varN num endpoint
           | Receive proc varN (datum list) endpoint
           | IfThen varN endpoint endpoint
           | Let varN (datum list -> datum) (varN list) endpoint
           | Fix dvarN endpoint
           | Call dvarN
           | Letrec dvarN (varN list) endpoint endpoint
           | FCall dvarN (varN list)
End

Datatype:
 closure = Closure (varN list) ((dvarN,closure) alist # (varN |-> datum)) endpoint
End

Datatype:
  network = NNil
          | NPar network network
          | NEndpoint proc (closure state) endpoint
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

Definition var_names_endpoint_def:
   (var_names_endpoint Nil = [])
∧ (var_names_endpoint (Send p v n e) = v::var_names_endpoint e)
∧ (var_names_endpoint (Receive p v d e) = v::var_names_endpoint e)
∧ (var_names_endpoint (IfThen v e1 e2) = v::var_names_endpoint e1 ++ var_names_endpoint e2)
∧ (var_names_endpoint (Let v f vl e) = v::vl ++ var_names_endpoint e)
∧ (var_names_endpoint (Fix dv e) = var_names_endpoint e)
∧ (var_names_endpoint (Call dv) = [])
∧ (var_names_endpoint (Letrec dv vars e1 e2) = vars ++ var_names_endpoint e1 ++ var_names_endpoint e2)
∧ (var_names_endpoint (FCall dv vars) = vars)
End

Definition free_var_names_endpoint_def:
   (free_var_names_endpoint Nil = [])
∧ (free_var_names_endpoint (Send p v n e) = v::free_var_names_endpoint e)
∧ (free_var_names_endpoint (Receive p v d e) = FILTER ($≠ v) (free_var_names_endpoint e))
∧ (free_var_names_endpoint (IfThen v e1 e2) = v::free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
∧ (free_var_names_endpoint (Let v f vl e) = vl ++ FILTER ($≠ v) (free_var_names_endpoint e))
∧ (free_var_names_endpoint (Fix dv e) = free_var_names_endpoint e)
∧ (free_var_names_endpoint (Call dv) = [])
∧ (free_var_names_endpoint (Letrec dv vars e1 e2) = FILTER (λn. ~MEM n vars) (free_var_names_endpoint e1) ++ free_var_names_endpoint e2)
∧ (free_var_names_endpoint (FCall dv vars) = vars)
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
  final (w::d) = (w = 7w:word8 \/ w = 6w:word8)
  ∧ final _ = F
End

Definition intermediate_def:
  intermediate (w::d) = (w = 2w:word8)
  ∧ intermediate _ = F
End

Definition fget_def:
  fget fm dv k =
    case FLOOKUP fm k of
      SOME kv => kv
    | NONE    => dv
End

Definition qlk_def:
  qlk qs p = fget qs [] p
End

Definition qpush_def:
  qpush qs sp d =
    qs |+ (sp,SNOC d (qlk qs sp))
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

Definition final_def:
    final (w::d) = (w = 7w:word8 ∨ w = 6w:word8)
  ∧ final _ = F
End

Definition intermediate_def:
  intermediate (w::d) = (w = 2w:word8)
  ∧ intermediate _ = F
End

Definition normalise_queues_def:
  normalise_queues q =
  DRESTRICT q (λp. FLOOKUP q p ≠ SOME [])
End

Definition normalised_def:
  normalised q = (normalise_queues q = q)
End

Definition normalised_network_def:
   (normalised_network NNil = T)
∧ (normalised_network (NEndpoint p s e) = normalised(s.queues))
∧ (normalised_network (NPar n1 n2) ⇔ normalised_network n1 ∧ normalised_network n2)
End

Definition endpoints_def:
   (endpoints NNil = [])
∧ (endpoints (NEndpoint p1 s e1) = [(p1,s,e1)])
∧ (endpoints (NPar n1 n2) = endpoints n1 ++ endpoints n2)
End

(* Finds a specific endpoint by name in the network *)
Definition net_find_def:
  net_find p NNil = NONE
∧ net_find p (NPar n1 n2) = OPTION_CHOICE (net_find p n1)
                                          (net_find p n2)
∧ net_find p (NEndpoint p' s c) = (if p = p'
                                   then SOME (NEndpoint p s c)
                                   else NONE)
End

(* Removes a specific (single) endpoint by name in the network.
   Note that if multiple endpoints with the same name exists
   a call to net_filter will only remove 1
*)
Definition net_filter_def:
  net_filter p NNil = NNil
∧ net_filter p (NEndpoint p' s c) =
    (if p = p' then NNil
     else NEndpoint p' s c)
∧ net_filter p (NPar n1 n2) =
    let l = net_filter p n1
    in if n1 ≠ l
       then if l = NNil then n2
            else NPar l n2
       else NPar n1 (net_filter p n2)
End

Definition net_end_def:
  net_end NNil = T
∧ net_end (NEndpoint _ _ Nil) = T
∧ net_end (NPar l r) = (net_end l ∧ net_end r)
∧ net_end _ = F
End

Definition dsubst_def:
   dsubst payloadLang$Nil dn e' = payloadLang$Nil
∧ dsubst (Send p v n e) dn e' = Send p v n (dsubst e dn e')
∧ dsubst (Receive p v d e) dn e' = Receive p v d (dsubst e dn e')
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
∧ dsubst (Letrec dn' vars e1 e2) dn e' =
   Letrec dn' vars (dsubst e1 dn e') (dsubst e2 dn e')
∧ dsubst (FCall dn' vars) dn e' =
   FCall dn' vars
End

val _ = export_theory ()

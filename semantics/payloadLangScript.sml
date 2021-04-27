open preamble
(* TODO: shouldn't have to depend on chorLangTheory *)
open chorLangTheory
open endpointLangTheory (*for state*)
open astTheory; (* for CakeML syntax-related types in the conf *)
open regexpTheory

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
           | Letrec dvarN (varN list) endpoint
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
              reverse : (modN,varN) id;
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
∧ (var_names_endpoint (Letrec dv vars e1) = vars ++ var_names_endpoint e1)
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
∧ (free_var_names_endpoint (Letrec dv vars e1) = vars ++ free_var_names_endpoint e1)
∧ (free_var_names_endpoint (FCall dv vars) = vars)
End

Definition free_fix_names_endpoint_def:
   (free_fix_names_endpoint Nil = [])
∧ (free_fix_names_endpoint (Send p v n e) = free_fix_names_endpoint e)
∧ (free_fix_names_endpoint (Receive p v d e) = free_fix_names_endpoint e)
∧ (free_fix_names_endpoint (IfThen v e1 e2) = free_fix_names_endpoint e1 ++ free_fix_names_endpoint e2)
∧ (free_fix_names_endpoint (Let v f vl e) = free_fix_names_endpoint e)
∧ (free_fix_names_endpoint (Fix dv e) = FILTER ($≠ dv) (free_fix_names_endpoint e))
∧ (free_fix_names_endpoint (Call dv) = [dv])
∧ (free_fix_names_endpoint (Letrec dv vars e1) = free_fix_names_endpoint e1)
∧ (free_fix_names_endpoint (FCall dv vars) = [])
End

Definition free_fun_names_endpoint_def:
   (free_fun_names_endpoint Nil = [])
∧ (free_fun_names_endpoint (Send p v n e) = free_fun_names_endpoint e)
∧ (free_fun_names_endpoint (Receive p v d e) = free_fun_names_endpoint e)
∧ (free_fun_names_endpoint (IfThen v e1 e2) = free_fun_names_endpoint e1 ++ free_fun_names_endpoint e2)
∧ (free_fun_names_endpoint (Let v f vl e) = free_fun_names_endpoint e)
∧ (free_fun_names_endpoint (Fix dv e) = free_fun_names_endpoint e)
∧ (free_fun_names_endpoint (Call dv) = [])
∧ (free_fun_names_endpoint (Letrec dv vars e1) = FILTER ($≠ dv) (free_fun_names_endpoint e1))
∧ (free_fun_names_endpoint (FCall dv vars) = [dv])
End

Definition bound_fun_names_endpoint_def:
   (bound_fun_names_endpoint Nil = [])
∧ (bound_fun_names_endpoint (Send p v n e) = bound_fun_names_endpoint e)
∧ (bound_fun_names_endpoint (Receive p v d e) = bound_fun_names_endpoint e)
∧ (bound_fun_names_endpoint (IfThen v e1 e2) = bound_fun_names_endpoint e1 ++ bound_fun_names_endpoint e2)
∧ (bound_fun_names_endpoint (Let v f vl e) = bound_fun_names_endpoint e)
∧ (bound_fun_names_endpoint (Fix dv e) = bound_fun_names_endpoint e)
∧ (bound_fun_names_endpoint (Call dv) = [])
∧ (bound_fun_names_endpoint (Letrec dv vars e1) = dv::bound_fun_names_endpoint e1)
∧ (bound_fun_names_endpoint (FCall dv vars) = [])
End

Definition bound_fix_names_endpoint_def:
   (bound_fix_names_endpoint Nil = [])
∧ (bound_fix_names_endpoint (Send p v n e) = bound_fix_names_endpoint e)
∧ (bound_fix_names_endpoint (Receive p v d e) = bound_fix_names_endpoint e)
∧ (bound_fix_names_endpoint (IfThen v e1 e2) = bound_fix_names_endpoint e1 ++ bound_fix_names_endpoint e2)
∧ (bound_fix_names_endpoint (Let v f vl e) = bound_fix_names_endpoint e)
∧ (bound_fix_names_endpoint (Fix dv e) = dv::bound_fix_names_endpoint e)
∧ (bound_fix_names_endpoint (Call dv) = [])
∧ (bound_fix_names_endpoint (Letrec dv vars e1) = bound_fix_names_endpoint e1)
∧ (bound_fix_names_endpoint (FCall dv vars) = [])
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

Definition free_fix_names_network_def:
   (free_fix_names_network NNil = [])
∧ (free_fix_names_network (NEndpoint p s e) = free_fix_names_endpoint e)
∧ (free_fix_names_network (NPar n1 n2) = free_fix_names_network n1 ++ free_fix_names_network n2)
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
∧ dsubst (Letrec dn' vars e1) dn e' =
   Letrec dn' vars (dsubst e1 dn e')
∧ dsubst (FCall dn' vars) dn e' =
   FCall dn' vars
End

(* CORRESPONDENCE RESTRICTIONS *)
(* Payload State and Code Coherence *)
(* -- Check the payload code and state make sense wrt. free variables *)
Definition pFv_def[simp]:
  pFv Nil = {} ∧
  pFv (Send _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (Receive _ fv _ npCd) =  pFv npCd DELETE fv ∧
  pFv (IfThen fv npCd1 npCd2) = fv INSERT pFv npCd1 ∪ pFv npCd2 ∧
  pFv (Let bv _ fvs npCd) = (pFv npCd DELETE bv) ∪ set fvs ∧
  pFv (Letrec dv vars e) = set vars ∪ pFv e ∧
  pFv (Fix dv e) = pFv e ∧
  pFv (Call dv) = ∅ ∧
  pFv (FCall dv vars) = set vars
End

Theorem FINITE_pFv[simp]:
  FINITE (pFv e)
Proof
  Induct_on ‘e’ >> simp[]
QED

Theorem pFv_free_var_names_endpoint:
  pFv e = set (free_var_names_endpoint e)
Proof
  Induct_on ‘e’ >> simp[free_var_names_endpoint_def] >>
  simp[EXTENSION, MEM_FILTER] >> metis_tac[]
QED

Theorem pFv_dsubst_E:
  v ∈ pFv (dsubst M dn N) ⇒ v ∈ pFv M ∨ v ∈ pFv N
Proof
  Induct_on ‘M’ >> rw[dsubst_def] >> metis_tac[]
QED

Definition EP_nodenames_def[simp]:
  EP_nodenames Nil = ∅ ∧
  EP_nodenames (Send dest _ _ e) = dest INSERT EP_nodenames e ∧
  EP_nodenames (Receive sender _ _ e) = sender INSERT EP_nodenames e ∧
  EP_nodenames (IfThen _ e1 e2) = EP_nodenames e1 ∪ EP_nodenames e2 ∧
  EP_nodenames (Let _ _ _ e) = EP_nodenames e ∧
  EP_nodenames (Letrec _ _ e) = EP_nodenames e ∧
  EP_nodenames (Fix _ e) = EP_nodenames e ∧
  EP_nodenames (Call _) = ∅ ∧
  EP_nodenames (FCall _ _) = ∅
End

Theorem closure_size_MEM:
  MEM (s,cl) cls ⇒
  closure_size cl < closure2_size cls
Proof
  Induct_on ‘cls’ >>
  rw[definition"closure_size_def"] >>
  rw[definition"closure_size_def"] >>
  res_tac >> DECIDE_TAC
QED

Definition closure_nodenames_def[simp]:
  closure_nodenames (Closure params (funs,bindings) body) =
  EP_nodenames body ∪ LIST_UNION (MAP (closure_nodenames) (MAP SND funs))
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  simp[MEM_MAP,PULL_EXISTS] >>
  simp[FORALL_PROD] >> rw[] >>
  drule closure_size_MEM >>
  intLib.COOPER_TAC
End

Definition network_nodenames_def[simp]:
  network_nodenames (NNil) = ∅ ∧
  network_nodenames (NEndpoint p s e) =
  LIST_UNION (MAP (closure_nodenames o SND) s.funs)
   ∪ EP_nodenames e ∧
  network_nodenames (NPar n1 n2) =
  network_nodenames n1 ∪ network_nodenames n2
End

val _ = export_theory ()

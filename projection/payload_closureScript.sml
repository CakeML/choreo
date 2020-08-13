(* Prepare for compilation to CakeML by switching from substitution semantics to environment semantics
   for function definitions *)
open preamble choreoUtilsTheory payloadLangTheory;
open endpoint_to_choiceTheory; (* For K0 *)

val _ = new_theory "payload_closure";

Definition written_var_names_endpoint_def:
   (written_var_names_endpoint Nil = [])
∧ (written_var_names_endpoint (Send p v n e) = written_var_names_endpoint e)
∧ (written_var_names_endpoint (Receive p v d e) = v::written_var_names_endpoint e)
∧ (written_var_names_endpoint (IfThen v e1 e2) = written_var_names_endpoint e1 ++ written_var_names_endpoint e2)
∧ (written_var_names_endpoint (Let v f vl e) = v::written_var_names_endpoint e)
∧ (written_var_names_endpoint (Fix dv e) = written_var_names_endpoint e)
∧ (written_var_names_endpoint (Call dv) = [])
∧ (written_var_names_endpoint (Letrec dv vars e1 e2) = written_var_names_endpoint e1 ++ written_var_names_endpoint e2)
∧ (written_var_names_endpoint (FCall dv vars) = vars)
End

Definition compile_endpoint_def:
    (compile_endpoint ar payloadLang$Nil = payloadLang$Nil) ∧
    (compile_endpoint ar (Send p v n e) = Send p v n (compile_endpoint ar e)) ∧
    (compile_endpoint ar (Receive p v l e) = Receive p v l (compile_endpoint ar e)) ∧
    (compile_endpoint ar (IfThen v e1 e2) =
     IfThen v (compile_endpoint ar e1) (compile_endpoint ar e2)) ∧
    (compile_endpoint ar (Let v f vl e) =
     Let v f vl (compile_endpoint ar e)) ∧
    (compile_endpoint ar (Letrec dn vars e1 e2) = Nil (* Source term should use fixpoint style *)) ∧
    (compile_endpoint ar (FCall dn vars) = Nil (* Source term should use fixpoint style *)) ∧
    (compile_endpoint ar (Fix dn e) =
     let vars = nub'(written_var_names_endpoint e);
         e' = compile_endpoint ((dn,vars)::ar) e
     in
       Letrec dn vars e' (FCall dn vars)
    ) ∧
    (compile_endpoint ar (Call dn) =
     case ALOOKUP ar dn of
       SOME vars =>
         FCall dn vars
     | NONE => Nil (* Should never happen *)
    )
End

Definition compile_network_def:
  compile_network NNil = NNil
∧ compile_network (NPar n1 n2) = NPar (compile_network n1) (compile_network n2)
∧ compile_network (NEndpoint p s e) =
  let
    (* In order to avoid having to deal with closures under potentiall undefined variables,
       make sure all variables that will be written to are initialised. *)
    undefined_writes = FILTER (λx. x ∉ (FDOM s.bindings)) (nub'(written_var_names_endpoint e))
  in
    NEndpoint p s
      (FOLDL (λe v. Let v K0 [] e) (compile_endpoint [] e) undefined_writes)
End

val _ = export_theory ();

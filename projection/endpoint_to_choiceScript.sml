open preamble endpointLangTheory

val _ = new_theory "endpoint_to_choice";

Definition gen_fresh_name_def :
   (gen_fresh_name [] = "a")
∧ (gen_fresh_name (n::ns) = #"a" :: FOLDL (λe b. if LENGTH e ≥ LENGTH b then e else b) n ns)
End

(* TODO: use these *)
Definition K0_def :
  K0 args = [0w:word8]
End

Definition K1_def :
  K1 args = [1w:word8]
End

Definition compile_endpoint_def :
   (compile_endpoint fv Nil = Nil)
∧ (compile_endpoint fv (Send p v e) = Send p v (compile_endpoint fv e))
∧ (compile_endpoint fv (Receive p v e) = Receive p v (compile_endpoint fv e))
∧ (compile_endpoint fv (IntChoice b p e) =
   if b then
     Let fv K1 [] (Send p fv (compile_endpoint fv e))
    else Let fv K0 [] (Send p fv (compile_endpoint fv e)))
∧ (compile_endpoint fv (ExtChoice p e1 e2) =
    Receive p fv (IfThen fv (compile_endpoint fv e1) (compile_endpoint fv e2)))
∧ (compile_endpoint fv (IfThen v e1 e2) = IfThen v (compile_endpoint fv e1) (compile_endpoint fv e2))
∧ (compile_endpoint fv (Let v f vl e) = Let v f vl (compile_endpoint fv e))
∧ (compile_endpoint fv (Fix dn e) = Fix dn (compile_endpoint fv e))
∧ (compile_endpoint fv (Call dn) = Call dn)
End

Definition compile_network_fv_def :
   (compile_network_fv fv endpointLang$NNil = NNil)
∧ (compile_network_fv fv (NPar n1 n2) = NPar (compile_network_fv fv n1)
                                                  (compile_network_fv fv n2))
∧ (compile_network_fv fv (NEndpoint p s e) = NEndpoint p s (compile_endpoint fv e))
End

Definition compile_network_def :
   compile_network n = compile_network_fv (gen_fresh_name (var_names_network n)) n
End

val _ = export_theory ()

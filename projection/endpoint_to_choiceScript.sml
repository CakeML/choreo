open preamble endpointLangTheory

val _ = new_theory "endpoint_to_choice";

val gen_fresh_name_def = Define `
   (gen_fresh_name [] = "a")
/\ (gen_fresh_name (n::ns) = #"a" :: FOLDL (λe b. if LENGTH e ≥ LENGTH b then e else b) n ns)
`

val compile_endpoint_def = Define `
   (compile_endpoint fv Nil = Nil)
∧ (compile_endpoint fv (Send p v e) = Send p v (compile_endpoint fv e))
∧ (compile_endpoint fv (Receive p v e) = Receive p v (compile_endpoint fv e))
∧ (compile_endpoint fv (IntChoice b p e) =
   if b then
     Let fv (K [1w]) [] (Send p fv (compile_endpoint fv e))
    else Let fv (K [0w]) [] (Send p fv (compile_endpoint fv e)))
∧ (compile_endpoint fv (ExtChoice p e1 e2) =
    Receive p fv (IfThen fv (compile_endpoint fv e1) (compile_endpoint fv e2)))
∧ (compile_endpoint fv (IfThen v e1 e2) = IfThen v (compile_endpoint fv e1) (compile_endpoint fv e2))
∧ (compile_endpoint fv (Let v f vl e) = Let v f vl (compile_endpoint fv e))`

val compile_network_fv_def = Define `
   (compile_network_fv fv endpointLang$NNil = NNil)
∧ (compile_network_fv fv (NPar n1 n2) = NPar (compile_network_fv fv n1)
                                                  (compile_network_fv fv n2))
∧ (compile_network_fv fv (NEndpoint p s e) = NEndpoint p s (compile_endpoint fv e))`

val compile_network_def = Define `
   compile_network n = compile_network_fv (gen_fresh_name (var_names_network n)) n`

val _ = export_theory ()

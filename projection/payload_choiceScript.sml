open preamble payloadLangTheory

val _ = new_theory "payload_choice";

val var_names_endpoint_def = Define `
   (var_names_endpoint Nil = [])
/\ (var_names_endpoint (Send p v n e) = v::var_names_endpoint e)
/\ (var_names_endpoint (Receive p v d e) = v::var_names_endpoint e)
/\ (var_names_endpoint (IntChoice b p e) = var_names_endpoint e)
/\ (var_names_endpoint (ExtChoice p e1 e2) = var_names_endpoint e1 ++ var_names_endpoint e2)
/\ (var_names_endpoint (IfThen v e1 e2) = v::var_names_endpoint e1 ++ var_names_endpoint e2)
/\ (var_names_endpoint (Let v f vl e) = v::vl ++ var_names_endpoint e)
`

val free_var_names_endpoint_def = Define `
   (free_var_names_endpoint Nil = [])
/\ (free_var_names_endpoint (Send p v n e) = v::free_var_names_endpoint e)
/\ (free_var_names_endpoint (Receive p v d e) = FILTER ($= v) (free_var_names_endpoint e))
/\ (free_var_names_endpoint (IntChoice b p e) = free_var_names_endpoint e)
/\ (free_var_names_endpoint (ExtChoice p e1 e2) = free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
/\ (free_var_names_endpoint (IfThen v e1 e2) = v::free_var_names_endpoint e1 ++ free_var_names_endpoint e2)
/\ (free_var_names_endpoint (Let v f vl e) = vl ++ FILTER ($= v) (free_var_names_endpoint e))
`

val var_names_network_def = Define `
   (var_names_network NNil = [])
/\ (var_names_network (NEndpoint p s e) = var_names_endpoint e)
/\ (var_names_network (NPar n1 n2) = var_names_network n1 ++ var_names_network n2)`

val free_var_names_network_def = Define `
   (free_var_names_network NNil = [])
/\ (free_var_names_network (NEndpoint p s e) = free_var_names_endpoint e)
/\ (free_var_names_network (NPar n1 n2) = free_var_names_network n1 ++ free_var_names_network n2)`

val gen_fresh_name_def = Define `
   (gen_fresh_name [] = "a")
/\ (gen_fresh_name (n::ns) = #"a" :: FOLDR (λe b. if LENGTH e ≥ LENGTH b then e else b) n ns)
`

val compile_endpoint_def = Define `
   (compile_endpoint fv Nil = Nil)
∧ (compile_endpoint fv (Send p v n e) = Send p v n (compile_endpoint fv e))
∧ (compile_endpoint fv (Receive p v dl e) = Receive p v dl (compile_endpoint fv e))
∧ (compile_endpoint fv (IntChoice b p e) =
   if b then
     Let fv (K [1w]) [] (Send p fv 0 (compile_endpoint fv e))
    else Let fv (K [0w]) [] (Send p fv 0 (compile_endpoint fv e)))
∧ (compile_endpoint fv (ExtChoice p e1 e2) =
    Receive p fv [] (IfThen fv (compile_endpoint fv e1) (compile_endpoint fv e2)))
∧ (compile_endpoint fv (IfThen v e1 e2) = IfThen v (compile_endpoint fv e1) (compile_endpoint fv e2))
∧ (compile_endpoint fv (Let v f vl e) = Let v f vl (compile_endpoint fv e))`

val compile_network_fv_def = Define `
   (compile_network_fv conf fv payloadLang$NNil = NNil)
∧ (compile_network_fv conf fv (NPar n1 n2) = NPar (compile_network_fv conf fv n1)
                                                  (compile_network_fv conf fv n2))
∧ (compile_network_fv conf fv (NEndpoint p s e) = NEndpoint p s (compile_endpoint fv e))`

val compile_network_def = Define `
   compile_network conf n = compile_network_fv conf (gen_fresh_name (var_names_network n)) n`

val _ = export_theory ()

open preamble endpointLangTheory payloadLangTheory payloadSemanticsTheory

val _ = new_theory "endpoint_to_payload";

val compile_endpoint_def = Define `
   (compile_endpoint endpointLang$Nil = payloadLang$Nil)
∧ (compile_endpoint (Send p v e) = Send p v 0 (compile_endpoint e))
∧ (compile_endpoint (Receive p v e) = Receive p v [] (compile_endpoint e))
∧ (compile_endpoint (IntChoice b p e) = Nil)
∧ (compile_endpoint (ExtChoice p e1 e2) = Nil)
∧ (compile_endpoint (IfThen v e1 e2) = IfThen v (compile_endpoint e1) (compile_endpoint e2))
∧ (compile_endpoint (Let v f vl e) = Let v f vl (compile_endpoint e))`

val compile_message_def = tDefine "compile_message" `
  compile_message conf d =
   if conf.payload_size = 0 then [] (*for termination, shouldn't happen*)
   else
     if final(pad conf d) then
       [pad conf d]
     else pad conf d :: compile_message conf (DROP conf.payload_size d)`
  (wf_rel_tac `inv_image ($<) (λ(conf,d). if conf.payload_size = 0 then 0 else LENGTH d)`
   >> rpt strip_tac
   >> fs[LENGTH_DROP,final_def,pad_def]
   >> every_case_tac >> fs[final_def]);

val compile_queue_def = Define `
   compile_queue conf [] = []
∧ (compile_queue conf ((p,d)::q) =
    MAP (λd. (p,d)) (compile_message conf d) ++ compile_queue conf q)
`

Definition compile_state_def:
  compile_state (es : endpointLang$state) = (ARB : payloadLang$state)
End

val compile_network_def = Define `
   (compile_network conf endpointLang$NNil = payloadLang$NNil)
∧ (compile_network conf (NPar n1 n2) = NPar (compile_network conf n1) (compile_network conf n2))
∧ (compile_network conf (NEndpoint p s e) = NEndpoint p
                                                       (compile_state s)
                                                       (compile_endpoint e))`

val _ = export_theory ()

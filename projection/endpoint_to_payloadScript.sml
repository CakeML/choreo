open preamble endpointLangTheory payloadLangTheory

val _ = new_theory "endpoint_to_payload";

val compile_endpoint_def = Define `
   (compile_endpoint endpointLang$Nil = payloadLang$Nil)
∧ (compile_endpoint (Send p v e) = Send p (INL v) (compile_endpoint e))
∧ (compile_endpoint (Receive p v e) = Receive p v [] (compile_endpoint e))
∧ (compile_endpoint (IntChoice b p e) = IntChoice b p (compile_endpoint e))
∧ (compile_endpoint (ExtChoice p e1 e2) = ExtChoice p (compile_endpoint e1) (compile_endpoint e2))
∧ (compile_endpoint (IfThen v e1 e2) = IfThen v (compile_endpoint e1) (compile_endpoint e2))
∧ (compile_endpoint (Let v f vl e) = Let v f vl (compile_endpoint e))`

val compile_message_def = tDefine "compile_message" `
  compile_message conf d =
   if conf.payload_size = 0 then [] (*for termination, shouldn't happen*)
   else if LENGTH d <= conf.payload_size then
     [6w::d]
   else
     (2w::TAKE conf.payload_size d) :: compile_message conf (DROP conf.payload_size d)`
  (wf_rel_tac `inv_image ($<) (λ(conf,d). if conf.payload_size = 0 then 0 else LENGTH d)`
   >> rpt strip_tac
   >> fs[LENGTH_DROP])

val compile_queue_def = Define `
   compile_queue conf [] = []
∧ compile_queue conf ((p,[])::q) = ARB
∧ (compile_queue conf ((p,d)::q) =
    MAP (λd. (p,d)) (compile_message conf d) ++ compile_queue conf q)
`

val compile_network_def = Define `
   (compile_network conf endpointLang$NNil = payloadLang$NNil)
∧ (compile_network conf (NPar n1 n2) = NPar (compile_network conf n1) (compile_network conf n2))
∧ (compile_network conf (NEndpoint p s e) = NEndpoint p
                                                       (s with queue := compile_queue conf s.queue)
                                                       (compile_endpoint e))`

val _ = export_theory ()

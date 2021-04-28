open preamble chor_to_endpointTheory
              endpoint_to_choiceTheory
              endpoint_to_payloadTheory
              payload_closureTheory
              payload_to_cakemlTheory

val _ = new_theory "projection";

Definition project_choice_def[simp]:
  project_choice fv s c l = endpoint_to_choice$compile_network_fv fv (compile_network s c l)
End

Definition new_fv_def[simp]:
  new_fv s c = gen_fresh_name (var_names_network (compile_network s c (procsOf c)))
End

Definition projection_def:
  projection conf s c l =
    payload_closure$compile_network_alt
      (endpoint_to_payload$compile_network conf
        (endpoint_to_choice$compile_network
           (compile_network s c l)))
End

Definition compilation_def:
  compilation vs p conf s c l =
    (case net_find p (projection conf s c l) of
       SOME (NEndpoint p0 s c) => SOME (compile_endpoint conf vs c)
     | _ => NONE)
End

Definition projection_top_def:
  projection_top conf s c l =
    payload_closure$compile_network
      (endpoint_to_payload$compile_network conf
        (endpoint_to_choice$compile_network
           (compile_network s c l)))
End

Definition compilation_top_def:
  compilation vs p conf s c l =
    (case net_find p (projection conf s c l) of
       SOME (NEndpoint p0 s c) => SOME (compile_endpoint conf vs c)
     | _ => NONE)
End

val _ = export_theory ()

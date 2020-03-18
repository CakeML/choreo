open preamble chor_to_endpointTheory
              endpoint_to_choiceTheory
              endpoint_to_payloadTheory

val _ = new_theory "projection";

Definition project_choice_def[simp]:
  project_choice fv s c l = endpoint_to_choice$compile_network_fv fv (compile_network s c l)
End

Definition new_fv_def[simp]:
  new_fv s c = gen_fresh_name (var_names_network (compile_network s c (procsOf c)))
End

Definition projection_def:
  projection conf s c l =
    endpoint_to_payload$compile_network conf
      (endpoint_to_choice$compile_network
         (compile_network s c l))
End

val _ = export_theory ()

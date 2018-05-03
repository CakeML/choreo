open preamble endpointLangTheory bakery_to_endpointTheory
              endpointSemanticsTheory endpointPropsTheory
              semBakeryTheory;

val _ = new_theory "bakery_to_endpointProof";

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ ∃q. reduction^* (compile_network s  c  (procsOf c) FEMPTY)
                      (compile_network s' c' (procsOf c) q)`,
  cheat
);

val _ = export_theory ()

open preamble

open semBakeryTheory

val _ = new_theory "confluence";

(* TODO: move to somewhere nicer *)
val free_variables_def = Define `
  (free_variables (Nil) = {}) /\
  (free_variables (IfThen v p c1 c2) = {(v,p)} ∪ (free_variables c1 ∪ free_variables c2)) /\
  (free_variables (Com p1 v1 p2 v2 c) = {(v1,p1)} ∪ (free_variables c DELETE (v2,p2))) /\
  (free_variables (Let v p f vl c) = set(MAP (λv. (v,p)) vl) ∪ (free_variables c DELETE (v,p))) /\
  (free_variables (Sel p b q c) = free_variables c)
`

val defined_vars_def = Define `
  defined_vars (s,c) = FDOM s`

val no_undefined_vars_def = Define `
  no_undefined_vars (s,c) = (free_variables c ⊆ FDOM s)`

val defined_vars_mono = Q.store_thm("defined_vars_mono",
  `!sc alpha sc'. trans sc alpha sc' ==> defined_vars sc ⊆ defined_vars sc'`,
  ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[defined_vars_def,SUBSET_OF_INSERT]);

val free_vars_mono = Q.store_thm("free_vars_mono",
  `!sc alpha sc'. trans sc alpha sc' ==> (free_variables(SND sc') DIFF defined_vars sc' ⊆ free_variables(SND sc) DIFF defined_vars sc)`,
  ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> fs[free_variables_def,defined_vars_def,DIFF_INSERT] >> rw[]
  >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> rpt strip_tac
  >> fs[] >> metis_tac[]);

val no_undefined_vars_trans_pres = Q.store_thm("no_undefined_vars_trans_pres",
  `!sc alpha sc'. no_undefined_vars sc /\ trans sc alpha sc' ==> no_undefined_vars sc'`,
  rpt gen_tac >> disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  >> qpat_x_assum `no_undefined_vars _` mp_tac
  >> qpat_x_assum `trans _ _ _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> imp_res_tac free_vars_mono
  >> fs[no_undefined_vars_def,free_variables_def,DELETE_SUBSET_INSERT,defined_vars_def,SUBSET_OF_INSERT]
  >> fs[SUBSET_DEF,INSERT_DEF,DIFF_DEF] >> metis_tac[]);

val semantics_deterministic = Q.store_thm("semantics_deterministic",
`!sc alpha l l' sc' sc''. trans sc (alpha,l) sc' /\ trans sc (alpha,l') sc'' ==> (sc' = sc'')`,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev(_)` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc''`,`alpha`,`l`,`l'`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def])
  >- (* Sel *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def])
  >- (* Let *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def])
  >- (* If *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def])
  >- (* Else *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def])
  >- (* If-swap *)
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> ntac 2 (first_x_assum drule)
      >> rpt strip_tac
      >> fs[])
  >- (* Com-swap *)     
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> first_x_assum drule
      >> rpt strip_tac
      >> fs[])
  >- (* Sel-swap *)     
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> first_x_assum drule
      >> rpt strip_tac
      >> fs[])
  >- (* Let-swap *)     
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> first_x_assum drule
      >> rpt strip_tac
      >> fs[])
  >- (* Asynch *)     
     (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> first_x_assum drule
      >> rpt strip_tac
      >> fs[])
  >> (* Asynch *)     
     qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
      >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
      >> first_x_assum drule
      >> rpt strip_tac
      >> fs[]);

val map_the_flookup_update_lemma = Q.prove(
  `!vl s p p' v' d. p' ≠ p ==>
  (MAP (THE ∘ FLOOKUP (s |+ ((v',p'),d))) (MAP (λv. (v,p)) vl)
   = MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl))`,
  Induct >> fs[FLOOKUP_UPDATE]);

val map_the_flookup_update_lemma2 = Q.prove(
  `!vl s p p' v' d. ¬MEM (v',p') (MAP (λv. (v,p)) vl) ==>
  (MAP (THE ∘ FLOOKUP (s |+ ((v',p'),d))) (MAP (λv. (v,p)) vl)
   = MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl))`,
  Induct >> rpt strip_tac >> fs[FLOOKUP_UPDATE]);

val every_flookup_update_lemma = Q.prove(
  `!vl s p p' v' d. p' ≠ p ==>
  (EVERY IS_SOME (MAP (FLOOKUP (s |+ ((v',p'),d))) (MAP (λv. (v,p)) vl))
   = EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl)))`,
  Induct >> fs[FLOOKUP_UPDATE]);

val every_flookup_update_lemma2 = Q.prove(
  `!vl s p p' v' d. ¬MEM (v',p') (MAP (λv. (v,p)) vl) ==>
  (EVERY IS_SOME (MAP (FLOOKUP (s |+ ((v',p'),d))) (MAP (λv. (v,p)) vl))
   = EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl)))`,
  Induct >> rpt strip_tac >> fs[FLOOKUP_UPDATE]);

val semantics_add_irrelevant_state = Q.store_thm("semantics_add_irrelevant_state",
  `!s c alpha s' c' p v d. trans (s,c) alpha (s',c') /\ p ∉ freeprocs(FST alpha) ==>
       trans (s |+ ((v,p),d),c) alpha (s' |+ ((v,p),d),c')
  `,
  rpt GEN_TAC
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> qpat_x_assum `_ ∉ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`,`c'`,`v`,`d`,`p`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- (* Com *)
     (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
      >> match_mp_tac trans_com >> fs[FLOOKUP_UPDATE])
  >- (* Sel *)
     (match_mp_tac trans_sel >> last_x_assum MATCH_ACCEPT_TAC)
  >- (* Let *)
     (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
      >> metis_tac[trans_let,map_the_flookup_update_lemma,every_flookup_update_lemma])
  >- (* If *)
     (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
      >> match_mp_tac trans_if_true >> fs[FLOOKUP_UPDATE])
  >- (* Else *)
     (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
      >> match_mp_tac trans_if_false >> fs[FLOOKUP_UPDATE])
  >- (* If-swap *)
    (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_if_swap])
  >- (* Com-swap *)
    (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_com_swap])
  >- (* Sel-swap *)
    (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_sel_swap])
  >- (* Let-swap *)
    (fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_let_swap])
  >> (* Asynch *)
    fs[freeprocs_def] >> fs[FUPDATE_COMMUTES]
    >> (match_mp_tac trans_com_async ORELSE match_mp_tac trans_sel_async)
    >> fs[]);

val semantics_add_irrelevant_state_tup = Q.store_thm("semantics_add_irrelevant_state_tup",
  `!s c alpha l s' c' p v d. trans (s,c) (alpha,l) (s',c') /\ p ∉ freeprocs alpha ==>
       trans (s |+ ((v,p),d),c) (alpha,l) (s' |+ ((v,p),d),c')
  `,
  metis_tac[semantics_add_irrelevant_state,FST]);

val notin_singleton_eq = Q.prove(
  `!a b. a ∉ {b} <=> (a ≠ b)`, fs[])

val semantics_add_irrelevant_state2 = Q.store_thm("semantics_add_irrelevant_state2",
  `!s c alpha s' c' p v d. trans (s,c) alpha (s',c') /\ (v,p) ∉ read(FST alpha)
        /\ written(FST alpha) ≠ SOME (v,p) ==>
       trans (s |+ ((v,p),d),c) alpha (s' |+ ((v,p),d),c')
  `,
  rpt GEN_TAC
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> qpat_x_assum `_ ∉ _` mp_tac
  >> qpat_x_assum `_ ≠ _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`,`c'`,`v`,`d`,`p`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- (* Com *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> match_mp_tac trans_com >> fs[FLOOKUP_UPDATE])
  >- (* Sel *)
     (match_mp_tac trans_sel >> last_x_assum MATCH_ACCEPT_TAC)
  >- (* Let *)
     (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
      >> metis_tac[trans_let,map_the_flookup_update_lemma,every_flookup_update_lemma,
                   map_the_flookup_update_lemma2,every_flookup_update_lemma2])
  >- (* If *)
     (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
      >> match_mp_tac trans_if_true >> fs[FLOOKUP_UPDATE])
  >- (* Else *)
     (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
      >> match_mp_tac trans_if_false >> fs[FLOOKUP_UPDATE])
  >- (* If-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_if_swap])
  >- (* Com-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_com_swap])
  >- (* Sel-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_sel_swap])
  >- (* Let-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_let_swap])
  >> (* Asynch *)
    fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
    >> (match_mp_tac trans_com_async ORELSE match_mp_tac trans_sel_async)
    >> fs[]);

val semantics_add_irrelevant_state3 = Q.store_thm("semantics_add_irrelevant_state3",
  `!s c alpha s' c' p v d. trans (s,c) alpha (s',c') /\ (v,p) ∉ read(FST alpha)
        /\ written(FST alpha) = SOME (v,p) ==>
       trans (s |+ ((v,p),d),c) alpha (s',c')
  `,
  rpt GEN_TAC
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> qpat_x_assum `_ ∉ _` mp_tac
  >> qpat_x_assum `_ = _` mp_tac  
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`,`c'`,`v`,`d`,`p`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[] >> rveq
  >- (* Com *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> rveq >> `FLOOKUP (s |+ ((v,p),d')) (v1,p1) = SOME d` by (fs[FLOOKUP_UPDATE])
     >> drule trans_com >> disch_then(qspecl_then [`v`,`p`,`c`] assume_tac)
     >> fs[FUPDATE_EQ]
    )
  >- (* Sel *)
     fs[written_def]
  >- (* Let *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES] >> rveq
     >> rveq >> imp_res_tac every_flookup_update_lemma2
     >> rpt(first_x_assum(qspec_then `d` assume_tac))
     >> drule trans_let >> fs[map_the_flookup_update_lemma2]
     >> disch_then (qspec_then `v` mp_tac)
     >> fs[FUPDATE_EQ])
  >- (* If *)
     (fs[written_def])
  >- (* Else *)
     (fs[written_def])
  >- (* If-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_if_swap])
  >- (* Com-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_com_swap])
  >- (* Sel-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_sel_swap])
  >- (* Let-swap *)
    (fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
     >> metis_tac[trans_let_swap])
  >> (* Asynch *)
    fs[written_def,read_def] >> fs[FUPDATE_COMMUTES]
    >> (match_mp_tac trans_com_async ORELSE match_mp_tac trans_sel_async)
    >> fs[]);

val semantics_add_irrelevant_state4 = Q.store_thm("semantics_add_irrelevant_state4",
  `!s c alpha s' c' p v d. trans (s,c) alpha (s',c') /\ (v,p) ∉ read(FST alpha) ==>
       trans (s |+ ((v,p),d),c) alpha (if written(FST alpha) = SOME (v,p) then s' else s' |+ ((v,p),d),c')
  `,
  metis_tac[semantics_add_irrelevant_state2,semantics_add_irrelevant_state3])

val semantics_add_irrelevant_state4_tup = Q.store_thm("semantics_add_irrelevant_state4_tup",
  `!s c alpha l s' c' p v d. trans (s,c) (alpha,l) (s',c') /\ (v,p) ∉ read alpha ==>
       trans (s |+ ((v,p),d),c) (alpha,l) (if written alpha = SOME (v,p) then s' else s' |+ ((v,p),d),c')
  `,
  metis_tac[semantics_add_irrelevant_state4,FST])


                                                     
val lookup_fresh_after_trans = Q.store_thm("lookup_fresh_after_trans",
  `!s c alpha s' c' p v. trans (s,c) alpha (s',c') /\ p ∉ freeprocs(FST alpha) ==>
   FLOOKUP s' (v,p) = FLOOKUP s (v,p)
  `,
  rpt GEN_TAC
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> qpat_x_assum `_ ∉ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`,`c'`,`v`,`p`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[] >> rveq >> fs[FLOOKUP_UPDATE,freeprocs_def]);

val map_lookup_fresh_after_trans = Q.store_thm("map_lookup_fresh_after_trans",
  `!s c alpha s' c' p vl. trans (s,c) alpha (s',c') /\ p ∉ freeprocs(FST alpha) ==>
   (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,p)) vl) = MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl))
  `,
  Induct_on `vl`
  >> rpt strip_tac
  >> fs[] >> metis_tac[lookup_fresh_after_trans]);

val map_lookup_fresh_after_trans_tup = Q.store_thm("map_lookup_fresh_after_trans_tup",
  `!s c alpha l s' c' p vl. trans (s,c) (alpha,l) (s',c') /\ p ∉ freeprocs alpha ==>
   (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,p)) vl) = MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl))
  `,
  metis_tac[FST,map_lookup_fresh_after_trans]);

val map_lookup_fresh_after_trans' = Q.store_thm("map_lookup_fresh_after_trans'",
  `!s c alpha s' c' p vl. trans (s,c) alpha (s',c') /\ p ∉ freeprocs(FST alpha) ==>
   (MAP (FLOOKUP s') (MAP (λv. (v,p)) vl) = MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
  `,
  Induct_on `vl`
  >> rpt strip_tac
  >> fs[] >> metis_tac[lookup_fresh_after_trans]);

val lookup_unwritten_after_trans = Q.store_thm("lookup_unwritten_after_trans",
  `!s c alpha s' c' p v. trans (s,c) alpha (s',c') /\ written(FST alpha) ≠ SOME(v,p) ==>
   FLOOKUP s' (v,p) = FLOOKUP s (v,p)
  `,
  rpt GEN_TAC
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> qpat_x_assum `_ ≠ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`,`c'`,`v`,`p`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[] >> rveq >> fs[FLOOKUP_UPDATE,written_def]);

val lookup_unwritten_after_trans_tup = Q.store_thm("lookup_unwritten_after_trans_tup",
  `!s c alpha l s' c' p v. trans (s,c) (alpha,l) (s',c') /\ written alpha ≠ SOME(v,p) ==>
   FLOOKUP s' (v,p) = FLOOKUP s (v,p)
`, metis_tac[lookup_unwritten_after_trans,FST]);
  
val sender_receiver_freeprocs = Q.store_thm("sender_receiver_freeprocs",
  `!alpha p p'. sender alpha = SOME p /\ receiver alpha = SOME p' ==> (freeprocs alpha = {p;p'})`,
  Induct >> fs[sender_def,receiver_def,freeprocs_def])

val no_written_same_state = Q.store_thm("no_written_same_state",
  `!sc alpha sc'. trans sc alpha sc' /\ (written(FST alpha) = NONE) ==> (FST sc' = FST sc)`,
  simp[satTheory.AND_IMP]
  >> ho_match_mp_tac trans_strongind
  >> fs[written_def])

val trans_add_relevant_state_com = Q.store_thm("trans_add_relevant_state_com",
  `!s c v1 p1 v2 p2 l s' c' d.
  trans (s,c) (LCom v1 p1 v2 p2,l) (s',c')
  ==> trans (s |+ ((p1,v1),d),c) (LCom v1 p1 v2 p2,l) (s' |+ ((p1,v1),d) |+ ((p2,v2),d),c')
`,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (LCom _ _ _ _,l)`
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sc' = (s',c')`
  >> rpt strip_tac
  >> rpt(qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`v1`,`p1`,`v2`,`p2`,`l`,`s'`,`c'`,`d`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com *)
    (Cases_on `(p1',p1) = (p2',p2) `
     >> simp[trans_com,FUPDATE_COMMUTES] >> metis_tac[FLOOKUP_UPDATE,FUPDATE_EQ,trans_com])
  >- (* If-swap *)
    metis_tac[trans_if_swap]
  >- (* Com-swap *)
    metis_tac[trans_com_swap]
  >- (* Sel-swap *)
    metis_tac[trans_sel_swap]
  >- (* Let-swap*)
    metis_tac[trans_let_swap]
  >> (* Asynch *)
    (match_mp_tac trans_com_async ORELSE match_mp_tac trans_sel_async) >> fs[]);

val concurrent_events_write_neq = Q.store_thm("concurrent_events_write_neq",
  `!sc alpha beta l l' sc' sc''.
    trans sc (alpha,l) sc' /\ trans sc (beta,l') sc'' /\ alpha ≠ beta /\ IS_SOME(written alpha) ==> written alpha ≠ written beta
  `,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> ntac 4 (pop_assum mp_tac)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`beta`,`l'`,`sc''`,`alpha`,`l`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> fs[freeprocs_def,sender_def,receiver_def,written_def]
  >> Cases_on `beta` >> fs[written_def,freeprocs_def] >> rveq >> fs[]
  >> TRY(metis_tac[written_def])
  >> Cases_on `alpha` >> fs[written_def,freeprocs_def] >> rveq >> fs[]);

val no_write_same_state = Q.store_thm("no_write_same_state",
  `!sc alpha l sc' sc''.
    trans sc (alpha,l) sc' /\ written alpha = NONE ==> FST sc = FST sc'
  `,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc''`,`alpha`,`l`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq >> fs[written_def]);

val some_write_update_state = Q.store_thm("some_write_update_state",
  `!sc alpha l sc' sc'' v p.
    trans sc (alpha,l) sc' /\ written alpha = SOME(v,p) ==> ?d. FST sc' = FST sc |+ ((v,p),d)
  `,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`v`,`p`,`sc''`,`alpha`,`l`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq >> fs[written_def] >> metis_tac[]);

val same_label_same_asyncs = Q.store_thm("same_label_same_asyncs",
  `!s c alpha l s' l' sc' sc''.
    trans (s,c) (alpha,l) sc' /\ trans (s',c) (alpha,l') sc'' ==> l = l'
  `,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> qpat_abbrev_tac `sc = (s,c)`
  >> rpt strip_tac
  >> ntac 2 (qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc''`,`s'`,`c`,`alpha`,`l'`,`l`,`s`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
  >> metis_tac[]);

val asynch_trans_filter_labels = Q.store_thm("asynch_trans_filter_labels",
  `!sc alpha beta l l' l'' sc' sc'' sc'''.
    trans sc (alpha,l) sc'
     /\ trans sc' (beta,l'') sc'''
     /\ trans sc (beta,l') sc''
     /\ alpha ≠ beta
     ==> l'' τ≅ lrm l' alpha`,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> ntac 3 (pop_assum mp_tac)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`beta`,`l'`,`l''`,`sc''`,`sc'''`,`alpha`,`l`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> TRY
    ((* Base If cases *)
     EVERY_ASSUM (fn thm => if is_forall (concl thm) then NO_TAC else ALL_TAC)
     >> qpat_assum `trans (_,IfThen _ _ _ _) _ _` kall_tac
     >> qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> last_x_assum (ASSUME_TAC o MATCH_MP trans_valid_actions)
     >> IMP_RES_TAC valid_actions_not_ltau
     >> match_mp_tac lcong_refl
     >> rw [mem_lrm_id,lcong_sym])
  >> TRY
    ((* Base cases *)
     EVERY_ASSUM (fn thm => if is_forall (concl thm) then NO_TAC else ALL_TAC)
     >> qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> fs[lrm_def,lcong_sym]
     >> match_mp_tac lcong_refl
     >> imp_res_tac trans_valid_actions >> pop_assum mp_tac
     >> rpt(qpat_x_assum `_ ∉ _` mp_tac)
     >> rpt(pop_assum kall_tac)
     >> Induct_on `l'` >> rpt strip_tac
                       >> fs[lrm_def,valid_actions_def,valid_action_def]
                       >> rw[lcong_sym]
                       >> fs[sender_def,receiver_def,lcong_cons])
  >> TRY (* If *)
    (qpat_x_assum `trans (_, IfThen _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> fs[lrm_def]
     >> qpat_x_assum `trans (_, IfThen _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def] >> metis_tac[lcong_rules])
  >> TRY (* Com *)
    (qpat_x_assum `trans (_, Com _ _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> fs[lrm_def]
     >> qpat_x_assum `trans (_, Com _ _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> rw[] >> fs[freeprocs_def] >> metis_tac[lcong_cons,lcong_rules])
  >> TRY (* Sel *)
    (qpat_x_assum `trans (_, Sel _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> fs[lrm_def]
     >> qpat_x_assum `trans (_, Sel _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> rw[] >> fs[freeprocs_def] >> metis_tac[lcong_cons,lcong_rules])
    >> TRY
    (qpat_x_assum `trans (_, Let _ _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> imp_res_tac same_label_same_asyncs >> rveq
     >> fs[lrm_def]
     >> qpat_x_assum `trans (_, Let _ _ _ _ _) _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
     >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
     >> metis_tac[lcong_cons,lcong_rules])
);

val semantics_locally_confluent = Q.store_thm("semantics_locally_confluent",
  `!sc alpha beta l l' sc' sc''.
    trans sc (alpha,l) sc' /\ trans sc (beta,l') sc'' /\ alpha ≠ beta ==> ?sc''' l'' l'''. trans sc' (beta,l'') sc''' /\ trans sc'' (alpha,l''') sc'''
  `,
  rpt gen_tac
  >> qpat_abbrev_tac `al = (alpha,l)`
  >> rpt strip_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> ntac 2 (pop_assum mp_tac)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`beta`,`l'`,`sc''`,`alpha`,`l`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`al`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Com *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> fs[] >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> asm_exists_tac >> simp[] >> qexists_tac `[]`
        >> match_mp_tac trans_com
        >> metis_tac[lookup_fresh_after_trans,FST])
    >> rveq
    >> reverse(Cases_on `(v2,p2) ∈ read beta`)
    >- (imp_res_tac semantics_add_irrelevant_state4_tup
        >> pop_assum(qspec_then `d` assume_tac)
        >> asm_exists_tac
        >> fs[] >> rw[]
        >> Cases_on `beta` >> fs[freeprocs_def,written_def] >> rveq
        >> fs[] >> qexists_tac `[]`
        >> match_mp_tac trans_com >> fs[] >> imp_res_tac lookup_unwritten_after_trans_tup
        >> fs[written_def])
    >> Cases_on `beta` >> fs[read_def,freeprocs_def,written_def,MEM_MAP])
  >- (* Sel *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> fs[] >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> asm_exists_tac >> simp[] >> qexists_tac `[]`
        >> match_mp_tac trans_sel
        >> metis_tac[lookup_fresh_after_trans,FST])
    >> rveq
    >> asm_exists_tac >> fs[] >> qexists_tac `[]`
    >> match_mp_tac trans_sel >> Cases_on `beta` >> fs[freeprocs_def])
  >- (* Let *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >> imp_res_tac semantics_add_irrelevant_state_tup
    >> first_x_assum (qspec_then `v` assume_tac)
    >> qpat_abbrev_tac `a1 = f _ `
    >> first_x_assum (qspec_then `a1` assume_tac)
    >> asm_exists_tac
    >> fs[] >> qexists_tac `[]`
    >> unabbrev_all_tac
    >> metis_tac[FST,map_lookup_fresh_after_trans,map_lookup_fresh_after_trans',trans_let])
  >- (* If-true *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >> asm_exists_tac >> fs[]
    >> qexists_tac `[]`
    >> match_mp_tac trans_if_true
    >> metis_tac[lookup_fresh_after_trans,FST])
  >- (* If-false *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >> asm_exists_tac >> fs[]
    >> qexists_tac `[]`
    >> match_mp_tac trans_if_false
    >> metis_tac[lookup_fresh_after_trans,FST])
  >- (* If-swap *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq >> rpt(first_x_assum drule >> disch_then assume_tac) >> fs[]
    >- metis_tac[trans_if_true,lookup_fresh_after_trans,FST]
    >- metis_tac[trans_if_false,lookup_fresh_after_trans,FST]
    (* TODO: proof script depends on generated names *)
    >> `l'' = remove1 alpha l'` by(metis_tac[asynch_trans_filter_labels])
    >> `l''' = remove1 beta l` by(metis_tac[asynch_trans_filter_labels])
    >> `l'''' = remove1 alpha l'` by(metis_tac[asynch_trans_filter_labels])
    >> `l''''' = remove1 beta l` by(metis_tac[asynch_trans_filter_labels])
    >> rveq
    >> Cases_on `sc'''`
    >> Cases_on `sc''''`
    >> Cases_on `written alpha`
    >- (imp_res_tac no_written_same_state >> rfs[] >> rveq
        >> metis_tac [trans_if_swap])
    >> Cases_on `written beta`
    >- (imp_res_tac no_written_same_state >> rfs[] >> rveq
        >> metis_tac [trans_if_swap])
    >> `written alpha ≠ written beta` by(metis_tac[concurrent_events_write_neq,IS_SOME_DEF])
    >> Cases_on `x` >> Cases_on `x'`
    >> Cases_on `q'' = q'''`
    >> imp_res_tac some_write_update_state >> fs[] >> rveq
    >> imp_res_tac FUPD_SAME_KEY_UNWIND >> rveq >> fs[FUPDATE_EQ] >> rfs[]
    >> imp_res_tac FUPD_SAME_KEY_UNWIND >> rveq >> fs[FUPDATE_EQ] >> rfs[]
    >> rfs[FUPDATE_COMMUTES]
    >> imp_res_tac FUPD_SAME_KEY_UNWIND >> rveq >> fs[FUPDATE_EQ] >> rfs[]
    >> fs[]
    >> `d'''''' = d''` by metis_tac[FUPDATE_COMMUTES,FUPD_SAME_KEY_UNWIND,FST,SND]
    >> rveq
    >> `d'' = d` by metis_tac[FUPDATE_COMMUTES,FUPD_SAME_KEY_UNWIND,FST,SND]
    >> rveq
    >> CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `remove1 alpha l'`
    >> CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `remove1 beta l`
    >> rename1 `(s |+ ((v1,p1),d1) |+ ((v2,p2),d2),_)`
    >> metis_tac[trans_if_swap,FUPDATE_COMMUTES])
  >- (* Com-swap *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> simp[Once CONJ_SYM] >> asm_exists_tac
        >> fs[]
        >> qexists_tac `[]`
        >> match_mp_tac trans_com
        >> metis_tac[lookup_fresh_after_trans,FST])
    >> first_x_assum drule >> disch_then drule >> strip_tac
    >> Cases_on `sc'''` >> metis_tac[lookup_fresh_after_trans,FST,trans_com_swap,trans_com_async])
  >- (* Sel-swap *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> simp[Once CONJ_SYM] >> asm_exists_tac
        >> fs[]
        >> qexists_tac `[]`
        >> match_mp_tac trans_sel
        >> metis_tac[lookup_fresh_after_trans,FST])
    >> first_x_assum drule >> disch_then drule >> strip_tac
    >> Cases_on `sc'''` >> metis_tac[lookup_fresh_after_trans,FST,trans_sel_swap,trans_sel_async])
  >- (* Let-swap *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> qpat_abbrev_tac `a1 = f _`
        >> rpt(first_x_assum (qspecl_then [`v`,`a1`] assume_tac))
        >> simp[Once CONJ_SYM] >> asm_exists_tac
        >> fs[]
        >> qexists_tac `[]` >> unabbrev_all_tac
        >> pop_assum kall_tac
        >> drule(GSYM map_lookup_fresh_after_trans_tup)
        >> disch_then drule >> disch_then assume_tac
        >> simp[]
        >> match_mp_tac trans_let
        >> drule map_lookup_fresh_after_trans' >> fs[])
    >> first_x_assum drule >> disch_then drule >> strip_tac
    >> Cases_on `sc'''` >> metis_tac[lookup_fresh_after_trans,FST,trans_let_swap])
  >- (* Com-asynch *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> simp[Once CONJ_SYM] >> asm_exists_tac
        >> fs[]
        >> qexists_tac `[]`
        >> match_mp_tac trans_com
        >> metis_tac[lookup_unwritten_after_trans,FST])
    >> first_x_assum drule >> disch_then drule >> strip_tac
    >> Cases_on `sc'''` >> metis_tac[lookup_fresh_after_trans,FST,trans_com_swap,trans_com_async])
  >- (* Sel-asynch *)
   (qpat_x_assum `trans _ _ _` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
    >> fs[] >> fs[freeprocs_def,sender_def,receiver_def]
    >> rveq
    >- (imp_res_tac semantics_add_irrelevant_state_tup
        >> rpt(first_x_assum (qspecl_then [`v2`,`d`] assume_tac))
        >> simp[Once CONJ_SYM] >> asm_exists_tac
        >> fs[]
        >> qexists_tac `[]`
        >> match_mp_tac trans_sel >> fs[])
    >> first_x_assum drule >> disch_then drule >> strip_tac
    >> Cases_on `sc'''` >> metis_tac[trans_sel_swap,trans_sel_async]));
  
val _ = export_theory ()

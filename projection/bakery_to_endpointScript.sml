open preamble semBakeryTheory endpointLangTheory

val _ = new_theory "bakery_to_endpoint";

val split_sel_def = Define `
  (split_sel proc p (Sel p1 b p2 c) =
   if proc = p2  then
     if p1 = p then
       SOME(b,c)
     else NONE
   else if proc ≠ p1 then
     split_sel proc p c
   else NONE)
∧ (split_sel proc _ _ = NONE)`

val mapRPair_def = Define `
  mapRPair f p = (FST p,f (SND p))
`;

val mapRPP_def = Define `
  mapRPP f p1 p2 = (FST p1 ∧ FST p2,f (SND p1) (SND p2))
`;

val _ = Parse.add_infix("<Γ>",425,Parse.NONASSOC);
val _ = Parse.overload_on("<Γ>",``mapRPair``);
val _ = export_rewrites ["mapRPair_def","mapRPP_def"];

val chor_size_def = Define`
  chor_size Nil                = (1 : num)
∧ chor_size (Com _ _ _ _ c)    = 1 + chor_size c
∧ chor_size (Sel _ _ _ c)      = 1 + chor_size c
∧ chor_size (Let _ _ _ _ c)    = 1 + chor_size c
∧ chor_size (IfThen _ _ c1 c2) = 1 + chor_size c1 + chor_size c2
`;

val project_def = tDefine "project" `
   project proc Nil = (T,Nil)
∧ (project proc (Com p1 v1 p2 v2 c) =
    if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      Send p2 v1 <Γ> project proc c
    else if proc = p2 then
      Receive p1 v2 <Γ> project proc c
    else
      project proc c)
∧ (project proc (Let v p1 f vs c) =
    if proc = p1 then
      Let v f vs <Γ> project proc c
    else
      project proc c)
∧ (project proc (IfThen v p1 c1 c2) =
    if proc = p1 then
      mapRPP (IfThen v) (project proc c1) (project proc c2)
    else
      case (split_sel proc p1 c1,split_sel proc p1 c2) of
        | (SOME(T,c1'),SOME(F,c2')) =>
           mapRPP (ExtChoice p1) (project proc c1') (project proc c2')
        | (NONE,NONE) =>
          if project proc c1 = project proc c2 then
            project proc c1
          else
            (F,Nil)
        | _ => (F,Nil)) (* shouldn't happen *)
∧ (project proc (Sel p1 b p2 c) =
    if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      IntChoice b p2 <Γ> project proc c
    else if proc = p2 then
      if b then
        (λx. ExtChoice p1 x Nil) <Γ> project proc c
      else
        ExtChoice p1 Nil <Γ> project proc c
   else
     project proc c)`
(WF_REL_TAC `measure (chor_size o SND)`
\\ rw [chor_size_def]
>- (`chor_size p_2 ≤ chor_size c1`suffices_by rw []
   \\ Induct_on `c1` >> fs [split_sel_def,chor_size_def]
   \\ rw [] >> fs [])
>- (`chor_size p_2' ≤ chor_size c2`suffices_by rw []
   \\ Induct_on `c2` >> fs [split_sel_def,chor_size_def]
   \\ rw [] >> fs []))
;

(* Project a global state `(proc,var) |-> val` into a single process
   state `var |-> val`
*)
val projectS_def = Define`
  projectS p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
`;

(* The domain of a state `s` projected to a process `p` is the set of
   all variable names associated with `p` in the domain of `s`
*)
val fdom_projectS = Q.store_thm("fdom_projectS",
  `∀p s. FDOM (projectS p s) = { v | (v,p) ∈ FDOM s }`,
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF,IMAGE_DEF,FUN_EQ_THM]
  \\ EQ_TAC >> rw [] >> fs [] >> Q.EXISTS_TAC `(x,p)` >> rw [] );


(* If a key `(v,p)` is in the domain of a global state `s` then
   one can expect the application of the projected key `v` over
   a projected state `projectS p s` to be equal to an original
   (un-projected) application
*)
val fapply_projectS = Q.store_thm("fapply_projectS",
  `∀p v (s : β # α |-> γ). (v,p) ∈ FDOM s ⇒ projectS p s ' v = s ' (v,p)`,
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF]
  \\ sg `INJ FST (FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ]
  \\ IMP_RES_TAC (MAP_KEYS_def |> CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV) |> CONJUNCT2)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `(v,p)`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
);

(* If a value is available on a state `s` with key `(v,p)` then it
   should also be available in a projected state `projectS p s` with
   key `v`
*)
val lookup_projectS = Q.store_thm("lookup_projectS",
  `∀p v s d. FLOOKUP s (v,p) = SOME d ⇒ FLOOKUP (projectS p s) v = SOME d`,
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
);

(* Alternative version of lookup_projectS *)
val lookup_projectS' = Q.store_thm("lookup_projectS'",
  `∀p v s d. FLOOKUP s (v,p) = FLOOKUP (projectS p s) v`,
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
);

(* If a state is updated with bindings for a process (`p2`) this does not
   affect the projection of any other process (`p1`)
*)
val fupdate_projectS = Q.store_thm("fupdate_projectS",
  `∀p1 p2 s v d. p1 ≠ p2 ⇒ projectS p1 (s |+ ((v,p2),d)) = projectS p1 s`,
  rw [projectS_def]
);

(*  Updating a projected state is equivalent to updating
    a global state with the corresponding process

*)
val projectS_fupdate = Q.store_thm("projectS_fupdate",
  `∀p v d s. projectS p (s |+ ((v,p),d)) = projectS p s |+ (v,d)`,
  rw [projectS_def]
  \\ sg `INJ FST ((v,p) INSERT FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- REPEAT (rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ])
  \\ IMP_RES_TAC (MAP_KEYS_FUPDATE)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `d`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
);

val compile_network_gen_def = Define`
  compile_network_gen s c []  = (T,NNil)
∧ compile_network_gen s c (p::lp) =
       let mkState = (λp. <| bindings := projectS p s;
                             queue    := [] |>);
           mkEP    = (λp. project p c);
           mkNEP   = (λp. NEndpoint p (mkState p) <Γ> mkEP p)
       in  mapRPP NPar (mkNEP p)  (compile_network_gen s c lp)
`;

val _ = overload_on("compile_network",
  ``(λs c l. SND (compile_network_gen s c l))``
);

val _ = overload_on("compile_network_ok",
  ``(λs c l. FST (compile_network_gen s c l))``
);

(* TODO: Comments! *)
val cn_ignore_com = Q.store_thm("cn_ignore_com",
  `∀p1 v1 p2 v2 s c' pl.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Com p1 v1 p2 v2 c') pl = compile_network s c' pl`,
  Induct_on `pl`
  \\ rw [ compile_network_gen_def
        , project_def,projectS_def]
);

(* TODO: Comments! *)
val cn_ignore_sel = Q.store_thm("cn_ignore_sel",
  `∀p1 b p2 s c' pl.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Sel p1 b p2 c') pl = compile_network s c' pl`,
  Induct_on `pl`
  \\ rw [ project_def,projectS_def
        , compile_network_gen_def
        , FLOOKUP_UPDATE]
);

(* TODO: Comments! *)
val cn_ignore_let = Q.store_thm("cn_ignore_let",
  `∀p s v f vl c pl.
    ¬MEM p pl
    ⇒ compile_network s (Let v p f vl c) pl = compile_network s c pl`,
  Induct_on `pl`
  \\ rw [ compile_network_gen_def,project_def,projectS_def
        , FLOOKUP_UPDATE]
);

(* TODO: Comments! *)
val cn_ignore_state_update = Q.store_thm("cn_ignore_state_update",
  `∀p v d s c pl.
    ¬MEM p pl
    ⇒ compile_network (s |+ ((v,p),d)) c pl = compile_network s c pl`,
  Induct_on `pl`
  \\ rw [ compile_network_gen_def,project_def,projectS_def
        , FLOOKUP_UPDATE]
);

val _ = export_theory ()

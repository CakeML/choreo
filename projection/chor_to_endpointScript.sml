open preamble chorSemTheory endpointLangTheory

val _ = new_theory "chor_to_endpoint";

val split_sel_def = Define `
  (split_sel proc p (Sel p1 b p2 c) =
   if p1 = p then
     if proc = p2 then
       SOME(b,c)
     else split_sel proc p c
   else NONE)
∧ (split_sel proc _ _ = NONE)`

val top_sels_def = Define `
  (top_sel proc p (Sel p1 b p2 c) =
   if p1 = p then
     if proc = p2 then
       SOME(b,c)
     else split_sel proc p c
   else NONE)
∧ (top_sels proc _ _ = NONE)`

Definition pre_sel_def:
  pre_sel p (Sel p1 b p2 c) =
    (if p1 = p then
       let (l,c) = pre_sel p c in
         ((b,p2)::l,c)      
     else ([],Sel p1 b p2 c))
∧ pre_sel _ c = ([],c)
End

val projPre_def = Define`
  projPre p ((b,q)::l) ep = IntChoice b q (projPre p l ep)
∧ projPre p [] ep = ep
`

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

Theorem chor_size_pre_sel:
  !p c. chor_size(SND(pre_sel p c)) <= chor_size c
Proof
  strip_tac >> Induct_on `c` >> rw[pre_sel_def,chor_size_def,ELIM_UNCURRY]
QED

val project_def = tDefine "project" `
   project proc banlist Nil = (T,Nil)
∧ (project proc banlist (Com p1 v1 p2 v2 c) =
    if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      Send p2 v1 <Γ> project proc banlist c
    else if proc = p2 then
      Receive p1 v2 <Γ> project proc banlist c
    else
      project proc banlist c)
∧ (project proc banlist (Let v p1 f vs c) =
    if proc = p1 then
      Let v f vs <Γ> project proc banlist c
    else
      project proc banlist c)
∧ (project proc banlist (IfThen v p1 c1 c2) =
   let (ps1,c1') = pre_sel p1 c1;
        (ps2,c2') = pre_sel p1 c2
      in
        if EVERY FST ps1 /\ EVERY ($¬ o FST) ps2 /\ MAP SND ps1 = MAP SND ps2 /\
           ALL_DISTINCT(MAP SND ps2)
        then
          if proc = p1 then
            mapRPP (IfThen v)
                   (projPre p1 ps1 <Γ> project p1 (p1::banlist) c1')
                   (projPre p1 ps2 <Γ> project p1 (p1::banlist) c2')
          else if MEM proc (MAP SND ps2) then
            mapRPP (ExtChoice p1)
                   (project proc (p1::banlist) c1')
                   (project proc (p1::banlist) c2')
          else if project proc (p1::banlist) c1' = project proc (p1::banlist) c2' then
            project proc (p1::banlist) c2'
          else
            (F,Nil)
        else
          (F,Nil)) (* shouldn't happen *)
∧ (project proc banlist (Sel p1 b p2 c) =
    if MEM proc banlist then
      (F,Nil)
    else if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      IntChoice b p2 <Γ> project proc banlist c
    else if proc = p2 then
      if b then
        (λx. ExtChoice p1 x Nil) <Γ> project proc banlist c
      else
        ExtChoice p1 Nil <Γ> project proc banlist c
   else
     project proc banlist c)`
(WF_REL_TAC `measure (chor_size o SND o SND)`
\\ rw [chor_size_def]
\\ rpt(qpat_x_assum `(_,_) = _` (assume_tac o GSYM))
\\ qspecl_then [`p1`,`c1`] assume_tac chor_size_pre_sel
\\ qspecl_then [`p1`,`c2`] assume_tac chor_size_pre_sel
\\ rfs[]);

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
           mkEP    = (λp. project p [] c);
           mkNEP   = (λp. NEndpoint p (mkState p) <Γ> mkEP p)
       in  mapRPP NPar (mkNEP p)  (compile_network_gen s c lp)
`;

val _ = overload_on("compile_network",
  ``(λs c l. SND (compile_network_gen s c l))``
);

val _ = overload_on("compile_network_ok",
  ``(λs c l. FST (compile_network_gen s c l))``
);

val _ = overload_on("project'",
  ``(λp banlist c. SND (project p banlist c))``
);

val _ = overload_on("project_ok",
  ``(λp banlist c. FST (project p banlist c))``
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

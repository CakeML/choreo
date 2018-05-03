open preamble semBakeryTheory endpointLangTheory

val _ = new_theory "bakery_to_endpoint";

val split_sel_def = Define `
   (split_sel proc (Sel p1 b p2 c) =
    if proc = p2 then
      SOME(b,c)
    else
      split_sel proc c)
/\ (split_sel proc _ = NONE)`

val project_def = Define `
   (project proc Nil = Nil)
/\ (project proc (Com p1 v1 p2 v2 c) =
    if proc = p1 /\ proc = p2 then
      Let v2 HD [v1] (project proc c) (*TODO: does it make sense to compile self-communication to let? *)
    else if proc = p1 then
      Send p2 v1 (project proc c)
    else if proc = p2 then
      Receive p1 v2 (project proc c)
    else
      project proc c)
/\ (project proc (Let v p1 f vs c) =
    if proc = p1 then
      Let v f vs (project proc c)
    else
      project proc c)
/\ (project proc (IfThen v p1 c1 c2) =
    if proc = p1 then
      IfThen v (project proc c1) (project proc c2)
    else
      case (split_sel proc c1,split_sel proc c2) of
        | (SOME(T,c1'),SOME(F,c2')) =>
            ExtChoice p1 (project proc c1) (project proc c2)
        | (NONE,NONE) => project proc c1
        | _ => Nil (* shouldn't happen *)
   )
/\ (project proc (Sel p1 b p2 c) =
    if proc = p1 then
      IntChoice b p2 (project proc c)
    else
      project proc c)`

(* Project a global state `(proc,var) |-> val` into a single process
   state `var |-> val`
*)
val projectS_def = Define`
  projectS p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
`;

(*Crates a network of projections from a choreography *)
val compile_network_def = Define`
  compile_network s c =
       let mkState = (λp. <| bindings := (projectS p s); queue := [] |>);
           mkEP = (λp. project p c);
           mkProcs = SET_TO_LIST (procsOf c);
           listNetwork = MAP (λp. NEndpoint p (mkState p) (mkEP p)) mkProcs
       in FOLDL (λx nt. if x = NNil then nt else NPar nt x) NNil listNetwork
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

val _ = export_theory ()

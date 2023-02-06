open preamble chorLangTheory endpointLangTheory choreoUtilsTheory

val _ = new_theory "chor_to_endpoint";

val split_sel_def = Define `
  (split_sel proc p (Sel p1 b p2 c) =
   if p1 = p then
     if proc = p2 then
       SOME(b,c)
     else split_sel proc p c
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

Definition chor_size_def:
  chor_size Nil                = (1 : num)
∧ chor_size (Com _ _ _ _ c)    = 1 + chor_size c
∧ chor_size (Sel _ _ _ c)      = 1 + chor_size c
∧ chor_size (Let _ _ _ _ c)    = 1 + chor_size c
∧ chor_size (IfThen _ _ c1 c2) = 1 + chor_size c1 + chor_size c2
∧ chor_size (Fix dn c) = 1 + chor_size c
∧ chor_size (Call dn) = 1
End

Definition project_def:
   project proc dvars Nil = (T,Nil)
∧ (project proc dvars (Com p1 v1 p2 v2 c) =
    if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      Send p2 v1 <Γ> project proc dvars c
    else if proc = p2 then
      Receive p1 v2 <Γ> project proc dvars c
    else
      project proc dvars c)
∧ (project proc dvars (Let v p1 f vs c) =
    if proc = p1 then
      Let v f vs <Γ> project proc dvars c
    else
      project proc dvars c)
∧ (project proc dvars (IfThen v p1 c1 c2) =
    if proc = p1 then
      mapRPP (IfThen v) (project proc dvars c1) (project proc dvars c2)
    else
      case (split_sel proc p1 c1,split_sel proc p1 c2) of
        | (SOME(T,c1'),SOME(F,c2')) =>
           mapRPP (ExtChoice p1) (project proc dvars c1') (project proc dvars c2')
        | (NONE,NONE) =>
          if project proc dvars c1 = project proc dvars c2 then
            project proc dvars c1
          else
            (F,Nil)
        | _ => (F,Nil)) (* shouldn't happen *)
∧ (project proc dvars (Sel p1 b p2 c) =
    if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      IntChoice b p2 <Γ> project proc dvars c
    else if proc = p2 then
      if b then
        (λx. ExtChoice p1 x Nil) <Γ> project proc dvars c
      else
        ExtChoice p1 Nil <Γ> project proc dvars c
   else
     project proc dvars c)
∧ (project proc dvars (Fix dn c) =
   (if MEM proc (dprocsOf ((dn,[])::dvars) c) then
      Fix dn <Γ> project proc ((dn,dprocsOf ((dn,[])::dvars) c)::dvars) c
    else
      (T,Nil)
    )
   )
∧ (project proc dvars (Call dn) =
    case ALOOKUP dvars dn of
      NONE => (F,Nil)
    | SOME pvars =>
      if MEM proc pvars then
       (T,Call dn)
      else
       (T, Nil))
Termination
(WF_REL_TAC `measure (chor_size o SND o SND)`
\\ rw [chor_size_def]
>- (`chor_size p_2 ≤ chor_size c1`suffices_by rw []
   \\ Induct_on `c1` >> fs [split_sel_def,chor_size_def]
   \\ rw [] >> fs [])
>- (`chor_size p_2' ≤ chor_size c2`suffices_by rw []
   \\ Induct_on `c2` >> fs [split_sel_def,chor_size_def]
   \\ rw [] >> fs []))
End

Definition compile_network_gen_def:
  compile_network_gen s c []  = (T,NNil)
∧ compile_network_gen s c (p::lp) =
       let mkState = (λp. <| bindings := projectS p s;
                             queue    := [] |>);
           mkEP    = (λp. project p [] c);
           mkNEP   = (λp. NEndpoint p (mkState p) <Γ> mkEP p)
       in  mapRPP NPar (mkNEP p)  (compile_network_gen s c lp)
End

Overload compile_network = “λs c l. SND (compile_network_gen s c l)”

Overload compile_network_ok = “λs c l. FST (compile_network_gen s c l)”

Overload project' = “λp dvars c. SND (project p dvars c)”

Overload project_ok = “λp dvars c. FST (project p dvars c)”

(* Network projection can ignore communications that do not involve
   processes in (pl) the process list
*)
Theorem cn_ignore_com:
  ∀p1 v1 p2 v2 s c' pl.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Com p1 v1 p2 v2 c') pl = compile_network s c' pl
Proof
  Induct_on `pl`
  \\ rw [ compile_network_gen_def
        , project_def,projectS_def]
QED

(* Network projection can ignore selections that do not involve
   processes in (pl) the process list
*)
Theorem cn_ignore_sel:
  ∀p1 b p2 s c' pl.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Sel p1 b p2 c') pl = compile_network s c' pl
Proof
  Induct_on `pl`
  \\ rw [ project_def,projectS_def
        , compile_network_gen_def
        , FLOOKUP_UPDATE]
QED

(* Network projection can ignore let bindings that do not involve
   processes in (pl) the process list
*)
Theorem cn_ignore_let:
  ∀p s v f vl c pl.
    ¬MEM p pl
    ⇒ compile_network s (Let v p f vl c) pl = compile_network s c pl
Proof
  Induct_on `pl`
  \\ rw [ compile_network_gen_def,project_def,projectS_def
        , FLOOKUP_UPDATE]
QED

(* Network projection can ignore update to the state that do not
   involve processes in (pl) the process list
*)
Theorem cn_ignore_state_update:
  ∀p v d s c pl.
    ¬MEM p pl
    ⇒ compile_network (s |+ ((v,p),d)) c pl = compile_network s c pl
Proof
  Induct_on `pl`
  \\ rw [ compile_network_gen_def,project_def,projectS_def
        , FLOOKUP_UPDATE]
QED

Theorem compile_network_ok_project_ok:
  !s c pn. compile_network_ok s c pn <=> (!p. MEM p pn ==> project_ok p [] c)
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >> conj_tac >>
  Induct_on `pn` >>
  rw[compile_network_gen_def] >> simp[] >>
  res_tac
QED

val _ = export_theory ()

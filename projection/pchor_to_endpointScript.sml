open preamble pchorLangTheory endpointLangTheory endpointPropsTheory

val _ = new_theory "pchor_to_endpoint";

val _ = set_grammar_ancestry
  ["chorLang","endpointProps","endpointLang","pchorLang"];


Definition split_sel_def:
  (split_sel proc p (Sel p1 b p2 c) =
   if p1 = p then
     if proc = p2 then
       SOME(b,c)
     else split_sel proc p c
   else NONE)
∧ (split_sel proc _ _ = NONE)
End

(* The OK monad *)

Definition ok_return_def[simp]:
  ok_return a = (T,a)
End

Definition ok_fmap_def[simp]:
  ok_fmap f a = (FST a, f (SND a))
End

Definition ok_seq_def[simp]:
  ok_seq f a = (FST a ∧ FST f,(SND f) (SND a))
End

Definition ok_liftA2_def[simp]:
  ok_liftA2 f p1 p2 = (FST p1 ∧ FST p2,f (SND p1) (SND p2))
End

Definition ok_bind_def[simp]:
  ok_bind ma f =
    let (f1,f2) = f (SND ma)
    in (FST ma ∧ f1, f2)
End

val _ = set_fixity "<Γ>" (Infix(NONASSOC, 425))
Overload "<Γ>" = “ok_fmap”
Overload "<*>" = “ok_seq”
Overload "Γ2>" = “ok_liftA2”


(* A more simplistic size_metric for pchor *)
Definition pchor_ssize_def:
  pchor_ssize Nil                = (1 : num)
∧ pchor_ssize (Com _ _ _ _ c)    = 1 + pchor_ssize c
∧ pchor_ssize (PCom _ _ _ c)     = 1 + pchor_ssize c
∧ pchor_ssize (Sel _ _ _ c)      = 1 + pchor_ssize c
∧ pchor_ssize (PSel _ _ c)       = 1 + pchor_ssize c
∧ pchor_ssize (Let _ _ _ _ c)    = 1 + pchor_ssize c
∧ pchor_ssize (IfThen _ _ c1 c2) = 1 + pchor_ssize c1 + pchor_ssize c2
End

(* TODO: comments *)
Definition project_def:
   project proc Nil = (T,Nil)
∧ project proc (Com p1 v1 p2 v2 c) =
   (if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      Send p2 v1 <Γ> project proc c
    else if proc = p2 then
      Receive p1 v2 <Γ> project proc c
    else
      project proc c)
∧ project proc (PCom p2 v (p1,_) c) =
   (if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p2 then
      Receive p1 v <Γ> project proc c
    else
      project proc c)
∧ project proc (Let v p1 f vs c) =
   (if proc = p1 then
      Let v f vs <Γ> project proc c
    else
      project proc c)
∧ project proc (IfThen v p1 c1 c2) =
   (if proc = p1 then
      Γ2> (IfThen v) (project proc c1) (project proc c2)
    else
      case (split_sel proc p1 c1,split_sel proc p1 c2) of
        | (SOME(T,c1'),SOME(F,c2')) =>
            Γ2> (ExtChoice p1) (project proc c1') (project proc c2')
        | (NONE,NONE) =>
          if project proc c1 = project proc c2 then
            project proc c1
          else
            (F,Nil)
        | _ => (F,Nil)) (* shouldn't happen *)
∧ project proc (Sel p1 b p2 c) =
   (if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p1 then
      IntChoice b p2 <Γ> project proc c
    else if proc = p2 then
      if b then
        (λx. ExtChoice p1 x Nil) <Γ> project proc c
      else
        ExtChoice p1 Nil <Γ> project proc c
    else
      project proc c)
∧ project proc (PSel p2 (p1,b) c) =
   (if proc = p1 ∧ proc = p2 then
      (F,Nil)
    else if proc = p2 then
      if b then
       (λx. ExtChoice p1 x Nil) <Γ> project proc c
      else
       ExtChoice p1 Nil <Γ> project proc c
    else
      project proc c)
Termination
  WF_REL_TAC `measure (pchor_ssize o SND)`
  \\ rw [pchor_ssize_def]
  >- (`pchor_ssize p_2 ≤ pchor_ssize c1`suffices_by rw []
     \\ Induct_on `c1` >> fs [split_sel_def,pchor_ssize_def]
     \\ rw [] >> fs [])
  \\ `pchor_ssize p_2' ≤ pchor_ssize c2`suffices_by rw []
  \\ Induct_on `c2` >> fs [split_sel_def,pchor_ssize_def]
  \\ rw [] >> fs []
End

(* Project a global state `(proc,var) |-> val` into a single process
   state `var |-> val`
*)
Definition projectS_def:
  projectS p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
End

(* The domain of a state `s` projected to a process `p` is the set of
   all variable names associated with `p` in the domain of `s`
*)
Theorem fdom_projectS:
  ∀p s. FDOM (projectS p s) = { v | (v,p) ∈ FDOM s }
Proof
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF,IMAGE_DEF,FUN_EQ_THM]
  \\ EQ_TAC >> rw [] >> fs [] >> Q.EXISTS_TAC `(x,p)` >> rw []
QED


(* If a key `(v,p)` is in the domain of a global state `s` then
   one can expect the application of the projected key `v` over
   a projected state `projectS p s` to be equal to an original
   (un-projected) application
*)
Theorem fapply_projectS:
  ∀p v (s : β # α |-> γ). (v,p) ∈ FDOM s ⇒ projectS p s ' v = s ' (v,p)
Proof
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF]
  \\ sg `INJ FST (FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ]
  \\ IMP_RES_TAC (MAP_KEYS_def |> CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV) |> CONJUNCT2)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `(v,p)`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
QED

(* If a value is available on a state `s` with key `(v,p)` then it
   should also be available in a projected state `projectS p s` with
   key `v`
*)
Theorem lookup_projectS:
  ∀p v s d. FLOOKUP s (v,p) = SOME d ⇒ FLOOKUP (projectS p s) v = SOME d
Proof
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
QED

(* Alternative version of lookup_projectS *)
Theorem lookup_projectS':
  ∀p v s d. FLOOKUP s (v,p) = FLOOKUP (projectS p s) v
Proof
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
QED

(* If a state is updated with bindings for a process (`p2`) this does not
   affect the projection of any other process (`p1`)
*)
Theorem fupdate_projectS:
  ∀p1 p2 s v d. p1 ≠ p2 ⇒ projectS p1 (s |+ ((v,p2),d)) = projectS p1 s
Proof
  rw [projectS_def]
QED

(*  Updating a projected state is equivalent to updating
    a global state with the corresponding process

*)
Theorem projectS_fupdate:
  ∀p v d s. projectS p (s |+ ((v,p),d)) = projectS p s |+ (v,d)
Proof
  rw [projectS_def]
  \\ sg `INJ FST ((v,p) INSERT FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- REPEAT (rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ])
  \\ IMP_RES_TAC (MAP_KEYS_FUPDATE)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `d`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
QED

Inductive qlcong:
(* Congruence rules for queues *)

  (* Symmetric *)
  (∀q. qlcong q q)

  (* Reflexive *)
∧ (∀q1 q2.
    qlcong q1 q2
    ⇒ qlcong q2 q1)
  (* Transitive *)
∧ (∀q1 q2 q3.
     qlcong q1 q2
     ∧ qlcong q2 q3
     ⇒ qlcong q1 q3)

  (* Reorder *)
∧ (∀h t m1 m2.
    FST m1 ≠ FST m2
    ⇒ qlcong (h ++ [m1;m2] ++ t) (h ++ [m2;m1] ++ t))
End

(*  Projects from a partial choreography (‘c’) and a given process (‘proc’)
    the current message queue. This is done by collecting all partial
    operations (PCom,PSel) that involve ‘proc’, paying special attentions
    to ‘IfThen’ branches whose queues should be equal upto (‘qlcong’)
    reordering
*)
Definition projectQ_def:
  projectQ proc q Nil                  = (T,q)
∧ projectQ proc q (PCom p2 x (p1,d) c) =
   (if p1 = p2 then (F,q)
    else if p2 = proc then
     projectQ proc (SNOC (p1,d) q) c
   else
    projectQ proc q c)
∧ projectQ proc q (PSel p2 (p1,b) c)   =
   (if p1 = p2 then (F,q)
    else if p2 = proc then
     projectQ proc (SNOC (p1,if b then [1w] else [0w]) q) c
   else
     projectQ proc q c)
∧ projectQ proc q (Com _ _ _ _ c)    = projectQ proc q c
∧ projectQ proc q (Sel _ _ _ c)      = projectQ proc q c
∧ projectQ proc q (Let _ _ _ _ c)    = projectQ proc q c
∧ projectQ proc q (IfThen _ _ c1 c2) =
    (let (b1,q1) = projectQ proc q c1;
         (b2,q2) = projectQ proc q c2
         in (b1 ∧ b2 ∧ qlcong q1 q2, q1))
End

Definition compile_network_gen_def:
  compile_network_gen s c []  = (T,NNil)
∧ compile_network_gen s c (p::lp) =
       let mkQueue = (λp. projectQ p [] c);
           mkState = (λp q. <| bindings := projectS p s;
                               queue    := q |>);
           mkEP    = (λp. project p c);
           mkNEP   = (λp. Γ2> (NEndpoint p) (mkState p <Γ> mkQueue p) (mkEP p))
       in  Γ2> NPar (mkNEP p)  (compile_network_gen s c lp)
End

val _ = overload_on("compile_network",
  ``(λs c l. SND (compile_network_gen s c l))``
);

val _ = overload_on("compile_network_ok",
  ``(λs c l. FST (compile_network_gen s c l))``
);

val _ = overload_on("projectQ'",
  ``(λp l c. SND (projectQ p l c))``
);

val _ = overload_on("project'",
  ``(λp c. SND (project p c))``
);

val _ = overload_on("project_ok",
  ``(λp c. FST (project p c))``
);

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
        , project_def,projectS_def,projectQ_def]
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
  \\ rw [ project_def,projectS_def,projectQ_def
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
  \\ rw [ compile_network_gen_def,project_def,projectS_def,projectQ_def
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
  \\ rw [ compile_network_gen_def,project_def,projectS_def,projectQ_def
        , FLOOKUP_UPDATE]
QED

val _ = export_theory ()

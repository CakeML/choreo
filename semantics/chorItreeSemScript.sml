open preamble chorLangTheory itreeTheory itreeCommonTheory

val _ = new_theory "chorItreeSem";

(* The error choreography:

   (1) Projectable choreography should not contain it.
   (2) It always produces an error result
 *)
Definition CERROR:
  CERROR = Call "ERROR"
End

(* The Finish branch choreography

   (1) Projectable choreography should not contain it.
   (2) It marks when a branch has been ruled out by selection

 *)

Definition CDONE:
  CDONE = Call "DONE"
End

(* Auxiliary functions for dealing with actions.
   In all cases if a wrong action is given by the environment
   the Itree simply stops with Nil.

   NOTE: We may need to differentiate this from a choreography
         that is terminating normally, however, conceptually
         there is nothing one can do once the environment
         messes up its response.
*)

Definition chor_itree_list_merge_def:
  chor_itree_list_merge (Ret' Done,    Ret' t)       = Ret' t
∧ chor_itree_list_merge (Ret' Done,    Tau' t)       = Tau' t
∧ chor_itree_list_merge (Ret' Done,    Vis' e f)     = Vis' e f
∧ chor_itree_list_merge (Ret' t   ,    Ret' Done)    = Ret' t
∧ chor_itree_list_merge (Tau' t   ,    Ret' Done)    = Tau' t
∧ chor_itree_list_merge (Vis' e f ,    Ret' Done)    = Vis' e f
∧ chor_itree_list_merge (Ret' l   ,    Ret' r)       = (if l = r then Ret' l else Ret' Error)
∧ chor_itree_list_merge (Tau' l   ,    Tau' r)       = Tau' (l ++ r)
∧ chor_itree_list_merge ((Vis' e1 f1),(Vis' e2 f2))  =
  (if e1 = e2
   then Vis' e1 (λa. f1 a ++ f2 a)
   else Ret' Error)
∧ chor_itree_list_merge _ = Ret' Error
End

Definition chor_itree_send_aux_def[simp]:
  chor_itree_send_aux s c Ok = [(s,c)]
∧ chor_itree_send_aux s _ _  = [(s,CERROR)]
End

Definition chor_itree_recv_aux_def[simp]:
  chor_itree_recv_aux s v c (Msg x) = [(s |+ (v,x),c)]
∧ chor_itree_recv_aux s _ _ _       = [(s,CERROR)]
End

Definition chor_itree_select_aux_def[simp]:
  chor_itree_select_aux s b1 c (Branch b2) =
  (if (b1 = b2)
   then [(s,c)]
   else [(s,CDONE)])
∧ chor_itree_select_aux s _ _ _ = [(s,CERROR)]
End

Definition chor_itree_list_def:
  chor_itree_list p [] = Ret' Done
∧ chor_itree_list p [(s,Nil)]      = Ret' (Res ())
∧ chor_itree_list p [(s,(Call f))] = (if f = "DONE"
                                      then Ret' Done
                                      else Ret' Error)
∧ chor_itree_list p [(s,Let v q f vl c)] =
  (if p = q
   then if EVERY IS_SOME (MAP (FLOOKUP s) vl)
        then Tau' [(s |+ (v,f (MAP (THE o FLOOKUP s) vl)), c)]
        else Ret' Error
   else chor_itree_list p [(s,c)])
∧ chor_itree_list p [(s,Fix f c)] = Tau' [(s,dsubst c f (Fix f c))]
∧ chor_itree_list p [(s,IfThen v q l r)] =
  (if p = q
   then if FLOOKUP s v = SOME [1w]
        then Tau' [(s,l)]
        else Tau' [(s,r)]
   else chor_itree_list p [(s,l);(s,r)])
∧ chor_itree_list p [(s,Com q1 v1 q2 v2 c)] =
  (if p = q1 then
     if IS_SOME (FLOOKUP s v1)
     then Vis' (Send q2 (THE (FLOOKUP s v1))) (chor_itree_send_aux s c)
     else Ret' Error
   else if p = q2
        then Vis' (Receive q1) (chor_itree_recv_aux s v2 c)
        else chor_itree_list p [(s,c)])
∧ chor_itree_list p [(s,Sel q1 b q2 c)] =
  (if p = q1
     then Vis' (Choose q2 b) (chor_itree_send_aux s c)
     else if p = q2
          then Vis' (Select q1) (chor_itree_select_aux s b c)
          else chor_itree_list p [(s,c)])
∧ chor_itree_list p (c1::c2::cs) =
    chor_itree_list_merge ((chor_itree_list p [c1]),
                           (chor_itree_list p (c2::cs)))
Termination
  WF_REL_TAC ‘inv_image $<  (list$SUM o (MAP (size_chor o SND)) o SND)’
  \\ rw[] \\ simp[size_chor_def]
  \\ Cases_on ‘p_2’ \\ simp[size_chor_def]
End

Definition chor_itree_aux_def:
  chor_itree p s c = itree_unfold (chor_itree_list p) [(s,c)]
End

Definition chor_itree_merge_aux1_def:
  chor_itree_merge_aux (Ret Done, Ret t)    = Ret' t
∧ chor_itree_merge_aux (Ret Done, Tau t)    = Tau' (Ret Done, t)
∧ chor_itree_merge_aux (Ret Done, Vis e f)  = Vis' e (λa. (Ret Done, f a))
∧ chor_itree_merge_aux (Ret t   , Ret Done) = Ret' t
∧ chor_itree_merge_aux (Tau t   , Ret Done) = Tau' (Ret Done, t)
∧ chor_itree_merge_aux (Vis e f , Ret Done) = Vis' e (λa. (Ret Done, f a))
∧ chor_itree_merge_aux (Ret l   , Ret r)    = (if l = r then Ret' l else Ret' Error)
∧ chor_itree_merge_aux (Tau l   , Tau r)    = Tau' (l,r)
∧ chor_itree_merge_aux ((Vis e1 f1),(Vis e2 f2)) =
  (if e1 = e2
   then Vis' e1 (λa. (f1 a,f2 a))
   else Ret' Error)
∧ chor_itree_merge_aux _ = Ret' Error
End

Definition chor_itree_merge_aux_def:
  chor_itree_merge l r = itree_unfold chor_itree_merge_aux (l,r)
End

Theorem chor_itree_merge_def:
∀t l r e1 f1 e2 f2 e f.
  (* Ret cases *)
  chor_itree_merge (Ret Done)       t            = t
∧ chor_itree_merge  t             (Ret Done)     = t
∧ chor_itree_merge (Ret Error)     t             = Ret Error
∧ chor_itree_merge  t             (Ret Error)    = Ret Error
∧ chor_itree_merge (Ret (Res ())) (Ret (Res ())) = Ret (Res ())
  (* Tau *)
∧ chor_itree_merge (Tau l) (Tau r)               = Tau (chor_itree_merge l r)
  (* Vis *)
∧ chor_itree_merge (Vis e1 f1) (Vis e2 f2) =
  (if e1 = e2
   then Vis e1 (λa. chor_itree_merge (f1 a) (f2 a))
   else Ret Error)
  (* Error cases *)
∧ chor_itree_merge (Ret (Res ())) (Tau r)        = Ret Error
∧ chor_itree_merge (Ret (Res ())) (Vis e f)      = Ret Error
∧ chor_itree_merge (Tau l)        (Ret (Res ())) = Ret Error
∧ chor_itree_merge (Tau l)        (Vis e f)      = Ret Error
∧ chor_itree_merge (Vis e f)      (Ret (Res ())) = Ret Error
∧ chor_itree_merge (Vis e f)      (Tau l)        = Ret Error
Proof
  rw[chor_itree_merge_aux_def]
  \\ simp[Once itree_unfold,chor_itree_merge_aux1_def]
  >- (Cases_on ‘t’ \\ rw[chor_itree_merge_aux1_def]
      >- (Q.SPEC_TAC (‘u’,‘u’) \\ simp[itree_el_eqv]
          \\ ho_match_mp_tac itree_el_ind \\ rw[]
          \\ Cases_on ‘u’ \\ rw[itree_el_def,Once itree_unfold,chor_itree_merge_aux1_def])
      >- (rw[FUN_EQ_THM] \\ qmatch_goalsub_abbrev_tac ‘_ = u’
          \\ pop_assum kall_tac
          \\ Q.SPEC_TAC (‘u’,‘u’) \\ simp[itree_el_eqv]
          \\ ho_match_mp_tac itree_el_ind \\ rw[]
          \\ Cases_on ‘u’ \\ rw[itree_el_def,Once itree_unfold,chor_itree_merge_aux1_def]))
  >- (Cases_on ‘t’ \\ rw[chor_itree_merge_aux1_def]
      >- (Cases_on ‘x’ \\ simp[chor_itree_merge_aux1_def])
      >- (Q.SPEC_TAC (‘u’,‘u’) \\ simp[itree_el_eqv]
          \\ ho_match_mp_tac itree_el_ind \\ rw[]
          \\ Cases_on ‘u’ \\ rw[itree_el_def,Once itree_unfold,chor_itree_merge_aux1_def])
      >- (rw[FUN_EQ_THM] \\ qmatch_goalsub_abbrev_tac ‘_ = u’
          \\ pop_assum kall_tac
          \\ Q.SPEC_TAC (‘u’,‘u’) \\ simp[itree_el_eqv]
          \\ ho_match_mp_tac itree_el_ind \\ rw[]
          \\ Cases_on ‘u’ \\ rw[itree_el_def,Once itree_unfold,chor_itree_merge_aux1_def]))
  >- (Cases_on ‘t’ \\ rw[chor_itree_merge_aux1_def]
      \\ Cases_on ‘x’ \\ rw[chor_itree_merge_aux1_def])
  >- (Cases_on ‘t’ \\ rw[chor_itree_merge_aux1_def]
      \\ Cases_on ‘x’ \\ rw[chor_itree_merge_aux1_def])
  >- (rw [FUN_EQ_THM] \\ Cases_on ‘x’ \\ simp[chor_itree_aux_def])
QED

Definition chor_itree_send_def[simp]:
  chor_itree_send p s c Ok = chor_itree p s c
∧ chor_itree_send _ _ _ _  = Ret Error
End

Definition chor_itree_recv_def[simp]:
  chor_itree_recv p s v c (Msg x) = chor_itree p (s |+ (v,x)) c
∧ chor_itree_recv p s _ _ _       = Ret Error
End

Definition chor_itree_select_def[simp]:
  chor_itree_select p s b1 c (Branch b2) =
  (if (b1 = b2)
   then chor_itree p s c
   else Ret Done)
∧ chor_itree_select _ s _ _ _ = Ret Error
End

Triviality chor_itree_list_nil:
∀p. itree_unfold (chor_itree_list p) [] = Ret Done
Proof
  rw[Once itree_unfold,chor_itree_list_def]
QED


Triviality chor_itree_list_merge_done:
  (∀x. chor_itree_list_merge (x,Ret' Done) = x)
∧ (∀x. chor_itree_list_merge (Ret' Done,x) = x)
Proof
  rw[] \\ Cases_on ‘x’ \\ rw[chor_itree_list_merge_def]
  \\ Cases_on ‘r’ \\ rw[chor_itree_list_merge_def]
QED

Triviality chor_itree_list_merge_assoc:
∀x y z.
  chor_itree_list_merge (x,chor_itree_list_merge (y,z))
  = chor_itree_list_merge (chor_itree_list_merge (x,y), z)
Proof
  rw[]
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ Cases_on ‘z’
  \\ rw[chor_itree_list_merge_def]
  \\ TRY (Cases_on ‘r’)
  \\ TRY (Cases_on ‘r'’)
  \\ TRY (Cases_on ‘r''’)
  \\ rw[chor_itree_list_merge_def]
QED

Triviality chor_itree_list_append:
∀l r p.
  chor_itree_list p (l ++ r)
  = chor_itree_list_merge (chor_itree_list p l, chor_itree_list p r)
Proof
  Induct
  \\ rw[chor_itree_list_def,chor_itree_list_merge_def
       ,chor_itree_list_merge_done]
  \\ Cases_on ‘l’ \\ Cases_on ‘r’
  \\ rw[chor_itree_list_def,chor_itree_list_merge_done]
  \\ first_x_assum (qspecl_then [‘h''::t'’,‘p’] assume_tac)
  \\ gs[] \\ qabbrev_tac ‘r = h''::t'’ \\ pop_assum kall_tac
  \\ simp[chor_itree_list_merge_assoc]
QED

Theorem chor_itree_list_is_merge:
  ∀p l r.
    itree_unfold (chor_itree_list p) (l ++ r)
    = chor_itree_merge (itree_unfold (chor_itree_list p) l) (itree_unfold (chor_itree_list p) r)
Proof
  simp[itree_el_eqv]
  \\ Induct_on ‘path’
  \\ rw[]
  \\ simp[Once itree_unfold,chor_itree_list_def]
  \\ qmatch_goalsub_abbrev_tac ‘itree_el gg1 _ = itree_el (chor_itree_merge gg2 _) _’
  \\ simp[Once itree_unfold,chor_itree_list_def]
  \\ qunabbrev_tac ‘gg2’
  \\ qmatch_goalsub_abbrev_tac ‘itree_el gg1 _ = itree_el (chor_itree_merge _ gg3) _’
  \\ simp[Once itree_unfold,chor_itree_list_def]
  \\ UNABBREV_ALL_TAC
  \\ simp[chor_itree_list_append]
  \\ qmatch_goalsub_abbrev_tac ‘chor_itree_list_merge (ll,rr)’
  \\ ntac 2 (pop_assum kall_tac)
  >- (rw [] \\ Cases_on ‘ll’ \\ Cases_on ‘rr’
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ TRY (Cases_on ‘r’)
      \\ TRY (Cases_on ‘r'’)
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ rw [itree_el_def])
  \\ rw[] \\ Cases_on ‘h’ \\ rw [itree_el_def]
  >- (rw [] \\ Cases_on ‘ll’ \\ Cases_on ‘rr’
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ TRY (Cases_on ‘r’)
      \\ TRY (Cases_on ‘r'’)
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ rw [itree_el_def])
  >- (rw [] \\ Cases_on ‘ll’ \\ Cases_on ‘rr’
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ TRY (Cases_on ‘r’)
      \\ TRY (Cases_on ‘r'’)
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ rw [itree_el_def])
QED

Theorem chor_itree_def:
∀vl v2 v1 v s r q2 q1 q p l f' f c b.
  chor_itree p s Nil       = Ret (Res ())
∧ chor_itree p s (Call f')  = (if f' = "DONE"
                               then Ret Done
                               else Ret Error)
∧ chor_itree p s (Let v q f vl c) =
  (if p = q then
     if EVERY IS_SOME (MAP (FLOOKUP s) vl) then
       Tau (chor_itree p (s |+ (v,f (MAP (THE ∘ FLOOKUP s) vl))) c)
     else Ret Error
   else chor_itree p s c)
∧ chor_itree p s (Fix f' c) = Tau (chor_itree p s (dsubst c f' (Fix f' c)))
∧ chor_itree p s (IfThen v q l r) =
  (if p = q then
     if FLOOKUP s v = SOME [1w]
     then Tau (chor_itree p s l)
     else Tau (chor_itree p s r)
   else chor_itree_merge (chor_itree p s l) (chor_itree p s r))
∧ chor_itree p s (Com q1 v1 q2 v2 c) =
  (if p = q1 then
     if IS_SOME (FLOOKUP s v1)
     then Vis (Send q2 (THE (FLOOKUP s v1))) (chor_itree_send p s c)
     else Ret Error
   else if p = q2
        then Vis (Receive q1) (chor_itree_recv p s v2 c)
        else chor_itree p s c)
∧ chor_itree p s (Sel q1 b q2 c) =
  if p = q1 then Vis (Choose q2 b) (chor_itree_send p s c)
  else if p = q2 then Vis (Select q1) (chor_itree_select p s b c)
  else chor_itree p s c
Proof
  rw[chor_itree_aux_def]
  >~[‘chor_itree_merge _’]
  >- (simp[Once itree_unfold,chor_itree_list_def]
      \\ qmatch_goalsub_abbrev_tac ‘gg1 = chor_itree_merge gg2 _’
      \\ simp[Once itree_unfold,chor_itree_list_def]
      \\ qunabbrev_tac ‘gg2’
      \\ qmatch_goalsub_abbrev_tac ‘gg1 = chor_itree_merge _ gg3’
      \\ simp[Once itree_unfold,chor_itree_list_def]
      \\ UNABBREV_ALL_TAC
      \\ qmatch_goalsub_abbrev_tac ‘chor_itree_list_merge (ll,rr)’
      \\ ntac 2 (pop_assum kall_tac)
      \\ Cases_on ‘ll’ \\ Cases_on ‘rr’
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ TRY (Cases_on ‘r’)
      \\ TRY (Cases_on ‘r'’)
      \\ rw[chor_itree_list_merge_def,chor_itree_merge_def]
      \\ simp[FUN_EQ_THM,chor_itree_list_is_merge])
  (* Send, Receive, Choose *)
  \\ simp[Once itree_unfold,chor_itree_list_def]
  \\ rw [FUN_EQ_THM]
  (* Handles cases where the process is not related *)
  \\ qmatch_goalsub_abbrev_tac ‘gg = _’
  \\ simp[Once itree_unfold,chor_itree_list_def]
  \\ UNABBREV_ALL_TAC
  \\ Cases_on ‘x’ \\ simp[chor_itree_aux_def,CERROR,chor_itree_list_def]
  \\ simp[Once itree_unfold,chor_itree_list_def]
  (* Select *)
  \\ Cases_on ‘b ⇔ b'’ \\ simp[]
  >- (irule EQ_SYM \\ simp[Once itree_unfold,chor_itree_list_def])
  \\ simp[chor_itree_list_def,CDONE]
QED

val _ = export_theory ()

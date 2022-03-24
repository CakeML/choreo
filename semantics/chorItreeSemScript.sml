open preamble choreoUtilsTheory libTheory

open chorLangTheory itreeTheory iforestTheory llistTheory

(* The type of events *)
Datatype:
  event = Send proc datum
        | Receive proc
        | Choose proc bool
        | Select proc
End


(* The type of actions *)
Datatype:
  action = Ok          (* Everything went fine *)
         | Msg datum   (* An incoming message with a value *)
         | Branch bool (* A choice of branch *)
End

(* The type of results  *)
Datatype:
  result = Res unit (* We are finish or the environment gave us a useles action *)
         | Error    (* Something whent wrong *)
End

(* Filters out all the parts of the choreography that do not concern a
   the given process
*)
Definition chor_filter_def:
  chor_filter p Nil = Nil
∧ chor_filter p (Call f) = Call f
∧ chor_filter p (Fix f c) = Fix f (chor_filter p c)
∧ chor_filter p (Let v q f vl c) =
  (if p = q
  then Let v q f vl (chor_filter p c)
  else chor_filter p c)
∧ chor_filter p (Com q1 v1 q2 v2 c) =
  (if p = q1 ∨ p = q2
   then Com q1 v1 q2 v2 (chor_filter p c)
   else chor_filter p c)
∧ chor_filter p (Sel q1 b q2 c) =
  (if p = q1 ∨ p = q2
   then Sel q1 b q2 (chor_filter p c)
   else chor_filter p c)
∧ chor_filter p (IfThen v q c1 c2) =
  IfThen v q (chor_filter p c1) (chor_filter p c2)
End

(* Auxiliary functions for dealing with actions.
   In all cases if a wrong action is given by the environment
   the Itree simply stops with Nil.

   NOTE: We may need to differentiate this from a choreography
         that is terminating normally, however, conceptually
         there is nothing one can do once the environment
         messes up its response.
*)


Definition chor_itree_if_aux_def[simp]:
  chor_itree_if_aux s l r (Branch b) = (s,if b then l else r)
∧ chor_itree_if_aux s l r _          = (s,Nil)
End

Definition chor_itree_send_aux_def[simp]:
  chor_itree_send_aux s c Ok = (s,c)
∧ chor_itree_send_aux s _ _  = (s,Nil)
End

Definition chor_itree_recv_aux_def[simp]:
  chor_itree_recv_aux s v c (Msg x) = (s |+ (v,x),c)
∧ chor_itree_recv_aux s _ _ _       = (s,Nil)
End

Definition chor_itree_select_aux_def[simp]:
  chor_itree_select_aux s b1 c (Branch b2) =
  (if (b1 = b2)
   then (s,c)
   else (s,Nil))
∧ chor_itree_select_aux s _ _ _            = (s,Nil)
End

Definition chor_itree_aux1_def:
  chor_itree_aux p (s,Nil)              = Ret' (Res ())
∧ chor_itree_aux p (s,(Call f))         = Ret' Error
∧ chor_itree_aux p (s,Let v q f vl c)   =
  (if p = q
   then if EVERY IS_SOME (MAP (FLOOKUP s) vl)
        then Tau' (s |+ (v,f (MAP (THE o FLOOKUP s) vl)), c)
        else Ret' Error
   else Tau' (s,c))
∧ chor_itree_aux p (s,Fix f c)        = Tau' (s,dsubst c f (Fix f c))
∧ chor_itree_aux p (s,IfThen v q l r) =
  (if p = q
   then if FLOOKUP s v = SOME [1w]
        then Tau' (s,l)
        else Tau' (s,r)
   (* NOTE: This is weird/wrong as it is not the case that
            If statement alone cause a Select event, that is what
            selections do.

            One idea to deal with this is to "zip" the two
            branches so that either both produce the same events,
            selections are used to remove a branch, or
            there is a missmatch and we throw an error.
    *)
   else if chor_filter p l = chor_filter p r
        then Tau' (s,l)
        else Vis' (Select q) (chor_itree_if_aux s l r))
∧ chor_itree_aux p (s,Com q1 v1 q2 v2 c) =
  (if p = q1 then
     if IS_SOME (FLOOKUP s v1)
     then Vis' (Send q2 (THE (FLOOKUP s v1))) (chor_itree_send_aux s c)
     else Ret' Error
   else if p = q2
        then Vis' (Receive q1) (chor_itree_recv_aux s v2 c)
        else Tau' (s,c))
∧ chor_itree_aux p (s,Sel q1 b q2 c) =
  (if p = q1
     then Vis' (Choose q2 b) (chor_itree_send_aux s c)
     else if p = q2
          then Vis' (Select q1) (chor_itree_select_aux s b c)
          else Tau' (s,c))
End

Definition chor_itree_aux_def:
  chor_itree p s c = itree_unfold (chor_itree_aux p) (s,c)
End

Definition chor_itree_if_def[simp]:
  chor_itree_if p s l r (Branch b) = chor_itree p s (if b then l else r)
∧ chor_itree_if p s l r _          = Ret (Res ())
End

Definition chor_itree_send_def[simp]:
  chor_itree_send p s c Ok = chor_itree p s c
∧ chor_itree_send _ _ _ _  = Ret (Res ())
End

Definition chor_itree_recv_def[simp]:
  chor_itree_recv p s v c (Msg x) = chor_itree p (s |+ (v,x)) c
∧ chor_itree_recv p s _ _ _       = Ret (Res ())
End

Definition chor_itree_select_def[simp]:
  chor_itree_select p s b1 c (Branch b2) =
  (if (b1 = b2)
   then chor_itree p s c
   else Ret (Res ()))
∧ chor_itree_select _ s _ _ _ = Ret (Res ())
End

Theorem chor_itree_def:
∀vl v2 v1 v s r q2 q1 q p l f' f c b.
  chor_itree p s Nil       = Ret (Res ())
∧ chor_itree p s (Call f')  = Ret Error
∧ chor_itree p s (Let v q f vl c) =
  (if p = q then
     if EVERY IS_SOME (MAP (FLOOKUP s) vl) then
       Tau (chor_itree p (s |+ (v,f (MAP (THE ∘ FLOOKUP s) vl))) c)
     else Ret Error
   else Tau (chor_itree p s c))
∧ chor_itree p s (Fix f' c) = Tau (chor_itree p s (dsubst c f' (Fix f' c)))
∧ chor_itree p s (IfThen v q l r) =
  (if p = q then
     if FLOOKUP s v = SOME [1w]
     then Tau (chor_itree p s l)
     else Tau (chor_itree p s r)
   else if chor_filter p l = chor_filter p r
   then Tau (chor_itree p s l)
   else Vis (Select q) (chor_itree_if p s l r))
∧ chor_itree p s (Com q1 v1 q2 v2 c) =
  (if p = q1 then
     if IS_SOME (FLOOKUP s v1)
     then Vis (Send q2 (THE (FLOOKUP s v1))) (chor_itree_send p s c)
     else Ret Error
   else if p = q2
        then Vis (Receive q1) (chor_itree_recv p s v2 c)
        else Tau (chor_itree p s c))
∧ chor_itree p s (Sel q1 b q2 c) =
  if p = q1 then Vis (Choose q2 b) (chor_itree_send p s c)
  else if p = q2 then Vis (Select q1) (chor_itree_select p s b c)
  else Tau (chor_itree p s c)
Proof
  rw[chor_itree_aux_def]
  \\ simp[Once itree_unfold,chor_itree_aux1_def]
  \\ rw [FUN_EQ_THM]
  \\ Cases_on ‘x’ \\ simp[chor_itree_aux_def]
  \\ simp[Once itree_unfold,chor_itree_aux1_def]
  \\ Cases_on ‘b ⇔ b'’ \\ simp[]
  >- (irule EQ_SYM \\ simp[Once itree_unfold,chor_itree_aux1_def])
  \\ simp[Once itree_unfold,chor_itree_aux1_def]
QED

val _ = new_theory "chorItreeSem";

val _ = export_theory ()

open preamble endpointLangTheory itreeTheory itreeCommonTheory

val _ = new_theory "endpointItreeSem";


Definition EPERROR:
  EPERROR = Call "ERROR"
End

Definition endpoint_itree_send_aux_def[simp]:
  endpoint_itree_send_aux s e Ok = (s,e)
∧ endpoint_itree_send_aux s _ _  = (s,EPERROR)
End

Definition endpoint_itree_recv_aux_def[simp]:
  endpoint_itree_recv_aux s v e (Msg x) = (s |+ (v,x),e)
∧ endpoint_itree_recv_aux s _ _ _       = (s,EPERROR)
End

Definition endpoint_itree_select_aux_def[simp]:
  endpoint_itree_select_aux s l r (Branch b) =
  (if b then (s,l) else (s,r))
∧ endpoint_itree_select_aux s _ _ _ = (s,EPERROR)
End

Definition endpoint_itree_aux1_def:
  endpoint_itree_aux (s,Nil)    = Ret' Done
∧ endpoint_itree_aux (s,Call f) = Ret' Error
∧ endpoint_itree_aux (s,Let v f vl e) =
    (if EVERY IS_SOME (MAP (FLOOKUP s) vl)
     then Tau' (s |+ (v,f (MAP (THE o FLOOKUP s) vl)),e)
     else Ret' Error)
∧ endpoint_itree_aux (s,Fix f e) = Tau' (s, dsubst e f (Fix f e))
∧ endpoint_itree_aux (s,IfThen v l r) =
    (if IS_SOME (FLOOKUP s v)
     then if FLOOKUP s v = SOME [1w]
          then Tau' (s,l)
          else Tau' (s,r)
     else Ret' Error)
∧ endpoint_itree_aux (s,Send p v e) =
    (if IS_SOME (FLOOKUP s v)
     then Vis' (Send p (THE (FLOOKUP s v))) (endpoint_itree_send_aux s e)
     else Ret' Error)
∧ endpoint_itree_aux (s,Receive p v e) =
    (Vis' (Receive p) (endpoint_itree_recv_aux s v e))
∧ endpoint_itree_aux (s,IntChoice b p e) =
    (Vis' (Choose p b) (endpoint_itree_send_aux s e))
∧ endpoint_itree_aux (s,ExtChoice p l r) =
    (Vis' (Select p) (endpoint_itree_select_aux s l r))
End

Definition endpoint_itree_aux_def:
  endpoint_itree s e = itree_unfold endpoint_itree_aux (s,e)
End

Definition endpoint_itree_send_def[simp]:
  endpoint_itree_send s e Ok = endpoint_itree s e
∧ endpoint_itree_send _ _ _  = Ret Error
End

Definition endpoint_itree_recv_def[simp]:
  endpoint_itree_recv s v e (Msg x) = endpoint_itree (s |+ (v,x)) e
∧ endpoint_itree_recv s _ _ _       = Ret Error
End

Definition endpoint_itree_select_def[simp]:
  endpoint_itree_select s l r (Branch b) =
    (if b
     then endpoint_itree s l
     else endpoint_itree s r)
∧ endpoint_itree_select s _ _ _ = Ret Error
End

Theorem endpoint_itree_def:
∀vl v s r p l f' f e b.
  endpoint_itree s Nil = Ret Done
∧ endpoint_itree s (Call f') = Ret Error
∧ endpoint_itree s (Let v f vl e) =
    (if EVERY IS_SOME (MAP (FLOOKUP s) vl)
     then
       Tau (endpoint_itree (s |+ (v,f (MAP (THE ∘ FLOOKUP s) vl))) e)
     else Ret Error)
∧ endpoint_itree s (Fix f' e) = Tau (endpoint_itree s (dsubst e f' (Fix f' e)))
∧ endpoint_itree s (IfThen v l r) =
    (if IS_SOME (FLOOKUP s v)
     then if FLOOKUP s v = SOME [1w]
          then Tau (endpoint_itree s l)
          else Tau (endpoint_itree s r)
     else Ret Error)
∧ endpoint_itree s (Send p v e) =
    (if IS_SOME (FLOOKUP s v)
     then Vis (Send p (THE (FLOOKUP s v))) (endpoint_itree_send s e)
     else Ret Error)
∧ endpoint_itree s (Receive p v e) =
    Vis (Receive p) (endpoint_itree_recv s v e)
∧ endpoint_itree s (IntChoice b p e) =
    Vis (Choose p b) (endpoint_itree_send s e)
∧ endpoint_itree s (ExtChoice p l r) =
    Vis (Select p) (endpoint_itree_select s l r)
Proof
  rw[endpoint_itree_aux_def]
  \\ simp[Once itree_unfold,endpoint_itree_aux1_def]
  \\ rw[FUN_EQ_THM]
  \\ Cases_on ‘x’ \\ simp[endpoint_itree_aux1_def,endpoint_itree_aux_def,EPERROR]
  \\ simp[Once itree_unfold,endpoint_itree_aux1_def]
  \\ Cases_on ‘b’ \\ simp[]
  \\ irule EQ_SYM
  \\ simp[Once itree_unfold,endpoint_itree_aux1_def]
QED

val _ = export_theory ()

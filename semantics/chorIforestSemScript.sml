open preamble chorLangTheory
     itreesTheory iforestTheory itreeCommonTheory
     chorItreeSemTheory

val _ = new_theory "chorIforestSem";

Definition message_add_def[simp]:
  message_add s p q d = s |+ ((p,q), the [] (FLOOKUP s (p,q)) ++ [d])
End

Definition message_fetch_def[simp]:
  message_fetch s p q =
    case FLOOKUP s (p,q) of
      NONE => NONE
    | SOME [] => NONE
    | SOME (x::xs) => SOME x
End

Definition message_drop_def[simp]:
  message_drop s p q =
    case FLOOKUP s (p,q) of
      NONE => s
    | SOME [] => s \\ (p,q)
    | SOME (x::xs) => s |+ ((p,q),xs)
End

Definition chor_iforest_act_def[simp]:
  chor_iforest_act s p (Send q d)   = SOME Ok
∧ chor_iforest_act s p (Choose q b) = SOME Ok
∧ chor_iforest_act s p (Receive q)  = OPTION_MAP Msg (message_fetch s p q)
∧ chor_iforest_act s p (Select q)   = OPTION_MAP (Branch o $= [1w]) (message_fetch s p q)
End

Definition chor_iforest_upd_def[simp]:
  chor_iforest_upd s p (Send q d)   = message_add s p q d
∧ chor_iforest_upd s p (Choose q b) = message_add s p q (if b then [1w] else [0w])
∧ chor_iforest_upd s p (Receive q)  = message_drop s p q
∧ chor_iforest_upd s p (Select q)   = message_drop s p q
End

Definition procs_s_def:
  procs_s p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
End

Definition chor_forest_def:
  chor_forest c []         = FEMPTY
∧ chor_forest c (p::procs) = (chor_forest c procs) |+ (p,chor_itree p FEMPTY c)
End

Definition chor_iforest_def:
  chor_iforest c = <| forest := chor_forest c (procsOf c);
                      st     := FEMPTY;
                      upd    := chor_iforest_upd;
                      act    := chor_iforest_act;
                   |>
End

val _ = export_theory ()

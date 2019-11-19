open preamble payloadLangTheory;

val _ = new_theory "payloadSemantics";

(* QUEUE MANAGEMENT FUNCTIONS *)
Definition fget_def:
  fget fm dv k =
    case FLOOKUP fm k of
      SOME kv => kv
    | NONE    => dv
End

Definition qlk_def:
  qlk qs p = fget qs [] p
End

Definition qpush_def:
  qpush qs sp d =
    qs |+ (sp,SNOC d (qlk qs sp))
End

(* MESSAGE PROTOCOL IMPLEMENTATION *)
Definition pad_def:
  pad conf d =
  if LENGTH d = conf.payload_size then       
    7w::d
  else if LENGTH d < conf.payload_size then
    6w::REPLICATE ((conf.payload_size - LENGTH d) - 1) (0w:word8) ++ [1w] ++ d
  else
    2w::TAKE conf.payload_size d
End

Definition unpad_def:
  (unpad (w::d) =
    if w = 7w ∨ w = 2w then d     
    else if w = 6w then
      case SPLITP ($= 1w) d of
        (_,_::d) => d
      | _ => []
    else []
  )
  ∧ (unpad _ = [])
End

Definition final_def:
    final (w::d) = (w = 7w:word8 ∨ w = 6w:word8)
  ∧ final _ = F
End

Definition intermediate_def:
  intermediate (w::d) = (w = 2w:word8)
  ∧ intermediate _ = F
End


(* PAYLOAD SEMANTICS *)
Datatype:
 label = LSend proc datum proc
       | LReceive proc datum proc
       | LTau
End

Inductive trans:
  (* Send-last-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n <= conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e))
                 (LSend p1 (pad conf (DROP n d)) p2)
                 (NEndpoint p1 s e)) ∧ 

  (* Send-intermediate-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n > conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e))
                  (LSend p1 (pad conf (DROP n d)) p2)
                  (NEndpoint p1 s (Send p2 v (n + conf.payload_size) e))) ∧ 

  (* Enqueue *)
  (∀conf s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queues := qpush s.queues p1 d) e)) ∧ 

  (* Com-L *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LSend p1 d p2) n1'
    ∧ trans conf n2 (LReceive p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2')) ∧ 

  (* Com-R *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LReceive p1 d p2) n1'
    ∧ trans conf n2 (LSend p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2')) ∧ 

  (* Dequeue-last-payload *)
  (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ qlk s.queues p1 = d::tl
    ∧ final d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2
                        (s with <|queues :=
                                    s.queues   |+ (p1,tl);
                                  bindings :=
                                    s.bindings |+ (v,FLAT(SNOC (unpad d) ds))
                                  |>)
                        e)) ∧ 

  (* Dequeue-intermediate-payload *)
  (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ qlk s.queues p1 = d::tl
    ∧ intermediate d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with queues :=
                                    s.queues |+ (p1,tl))
                           (Receive p1 v (SNOC (unpad d) ds) e))) ∧ 

  (* If-L *)
  (∀conf s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1)) ∧ 

  (* If-R *)
  (∀conf s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2)) ∧ 

  (* Let *)
  (∀conf s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans conf (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p
                        (s with bindings :=
                          s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
                        e)) ∧ 

  (* Par-L *)
  (∀conf n1 n1' n2 α.
    trans conf n1 α n1'
    ⇒ trans conf (NPar n1 n2)
             α
             (NPar n1' n2)) ∧ 

  (* Par-R *)
  (∀conf n1 n2 n2' α.
    trans conf n2 α n2'
    ⇒ trans conf (NPar n1 n2)
             α
             (NPar n1 n2'))
End

val _ = export_theory ()

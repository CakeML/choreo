open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open chorLibProgTheory;
open fromSexpTheory;
open astToSexprLib;
open compilationProofTheory;

open projectionLib;

val _ = new_theory "filter";

val _ = translation_extends "chorLibProg";

val n2w8 = “n2w:num -> word8”;
val w2n = “w2n:word8 -> num”;

val msg1 = “MAP (^n2w8 o ORD) "This message should be filtered."” |> EVAL |> concl |> rhs;
val msg2 = “MAP (^n2w8 o ORD) "A message such as this should be forwarded. It is absurdly long, so hopefully it will be split into distinct messages that will all be forwarded. Indeed, that would be great, wouldn't it? Hopefully, that will be exactly the behaviour you observe when you run this example."” |> EVAL |> concl |> rhs;
val msg3 = “MAP (^n2w8 o ORD) "Drop this message."” |> EVAL |> concl |> rhs;
val msg4 = “MAP (^n2w8 o ORD) "A message such as this should be forwarded."” |> EVAL |> concl |> rhs;
val msg5 = “MAP (^n2w8 o ORD) "Another message that should be forwarded."” |> EVAL |> concl |> rhs;

Definition test_def :
  test args =
       (if EVERY (λa. case a of []  => F | (f::r) => f = (65w:word8)) args then
          [1w:word8]
        else
          [0w])
End
    
Definition next_msg_def :
  next_msg args =
       case args of
       | (f::r)::r' => [f+1w]
       | _ => [0w:word8]
End

Definition msg_def :
  msg args =
    case args of
       | (f::r)::r' =>
           (if f = 0w:word8 then
             ^msg1
           else if f=1w then ^msg2
           else if f=2w then ^msg3
           else if f=3w then ^msg4
           else if f=4w then ^msg5
           else
             MAP (λx. ^n2w8(ORD x)) (explode (mlint$toString(&(^w2n f)))))
       | _ => []
End

val _ = ml_prog_update (open_module "filter");

val _ = next_ml_names := ["K0","K1","test","next_msg","msg"];

Theorem K0_v_thm = translate endpoint_to_choiceTheory.K0_def;
Theorem K1_v_thm = translate endpoint_to_choiceTheory.K1_def;

Theorem test_v_thm = translate test_def;

Theorem next_msg_v_thm = translate next_msg_def;

Theorem msg_v_thm = translate msg_def;

val _ = ml_prog_update (close_module NONE);

Definition filter_def:
  (filter:chor) =
  Let "count" "producer" K0 []
    (Fix "X"
       (Let "msg" "producer" msg ["count"]
          (Let "count" "producer" next_msg ["count"]
            (Com "producer" "msg" "filter" "msg"
              (Let "test" "filter" test ["msg"]
                (IfThen "test" "filter"
                   (Sel "filter" T "consumer"
                      (Com "filter" "msg" "consumer" "msg"
                        (Call "X")))
                   (Sel "filter" F "consumer"
                        (Call "X"))
                )
              )
            )
          )
       )
    )
End

val thm = project_to_camkes "filter_camkes" "filter" “filter”;

val _ = export_theory();

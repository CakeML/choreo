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

val msg1 = “MAP (^n2w8 o ORD) "This message should be filtered."” |> EVAL |> concl |> rhs;
val msg2 = “MAP (^n2w8 o ORD) "A message such as this should be forwarded. It is absurdly long, so hopefully it will be split into distinct messages that will all be forwarded. Indeed, that would be great, wouldn't it? Hopefully, that will be exactly the behaviour you observe when you run this example."” |> EVAL |> concl |> rhs;
val msg3 = “MAP (^n2w8 o ORD) "Drop this message."” |> EVAL |> concl |> rhs;

Definition test_def :
  test args =
       (if EVERY (λa. case a of []  => F | (f::r) => f = (65w:word8)) args then
          [1w:word8]
        else
          [0w])
End

Definition Kmsg1_def :
  Kmsg1 args = ^msg1
End

Definition Kmsg2_def :
  Kmsg2 args = ^msg2
End

Definition Kmsg3_def :
  Kmsg3 args = ^msg3
End

val _ = ml_prog_update (open_module "filter");

val _ = next_ml_names := ["K0","K1","test","Kmsg1","Kmsg2","Kmsg3"];

Theorem test_v_thm = translate test_def;

Theorem K0_v_thm = translate endpoint_to_choiceTheory.K0_def;
Theorem K1_v_thm = translate endpoint_to_choiceTheory.K1_def;
Theorem Kmsg1_v_thm = translate Kmsg1_def;
Theorem Kmsg2_v_thm = translate Kmsg2_def;
Theorem Kmsg3_v_thm = translate Kmsg3_def;

val _ = ml_prog_update (close_module NONE);

Definition filter_def:
  filter test =
  FOLDR (λe c.
         Let "v" "producer" e []
         (Com "producer" "v" "filter" "v"
          (Let "test" "filter" test ["v"]
           (IfThen "test" "filter"
            (Sel "filter" T "consumer"
             (Com "filter" "v" "consumer" "v" c)
            )
            (Sel "filter" F "consumer" c)
           )
          )
         )
        )
        chorLang$Nil
End

val thm = project_to_camkes "filter_camkes" "filter" “filter test [Kmsg1;Kmsg2;Kmsg3]”;

val _ = export_theory();

open preamble chorLangTheory chorSemTheory projectionTheory basisProgTheory;

val _ = new_theory "pingpong";

val _ = translation_extends "basisProg";

val n2w8 = “n2w:num -> word8”;
    
val ping = “MAP (^n2w8 o ORD) "ping"” |> EVAL |> concl |> rhs;
val pong = “MAP (^n2w8 o ORD) "pong"” |> EVAL |> concl |> rhs;

Definition pingpong_def:
  pingpong =
  Let "v" ^ping (K []) []
   (Com ^ping "v" ^pong "v"
     (Com ^pong "v" ^ping "v"
       Nil
     )
   )
End

Definition pingpong_conf:
  pingpong_conf = 
  <| payload_size := 1
   |>
End

Theorem compile_to_payload_thm =
  “projection pingpong_conf FEMPTY pingpong [^ping; ^pong]”
  |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY];

val _ = export_theory();

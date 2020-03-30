open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open fromSexpTheory;
open astToSexprLib;

val _ = new_theory "pingpong";

val _ = translation_extends "basisProg";

fun get_fun_name trm =
  lookup_v_thm trm |> concl |> rator |> rand |> rand

fun get_con_name s =
  get_cons_names() |>
  filter (fn (_,(tm,_)) => s = stringSyntax.fromHOLstring tm) |>
  map fst |> hd

val _ = ml_prog_update (open_module "ChorLib");

val _ = append_decs
  “[Dlet unknown_loc (Pvar "toList")
     (Fun "arr"
       (App Opapp
         [App Opapp
           [Var(Long "List" (Short "tabulate"));
            App Aw8length [Var(Short "arr")]];
          Fun "index"
            (App Aw8sub [Var(Short "arr"); Var(Short "index")])
         ]
       ));
    Dlet unknown_loc (Pvar "fromList")
     (Fun "l"
       (Let (SOME "arr")
          (App Aw8alloc
             [App Opapp [Var(Long "List" (Short "length")); Var(Short "l")];
              Lit(Word8 0w)])
          (Let NONE
             (App Opapp
                [App Opapp
                  [Var(Long "List" (Short "mapi"));
                   Fun "index"
                     (Fun "elem"
                       (App Aw8update [Var (Short "arr"); Var(Short "index"); Var(Short "elem")]
                       )
                     )
                  ];
                 Var(Short "l")
                ])
             (Var (Short "arr"))
          )
       )
     );
    Dlet unknown_loc (Pvar "append")
      (Fun "l1" (Fun "l2" (App ListAppend [Var(Short "l1");Var(Short "l2")])))
   ]”

val _ = ml_prog_update (close_module NONE);

val n2w8 = “n2w:num -> word8”;

val ping = “MAP (^n2w8 o ORD) "ping"” |> EVAL |> concl |> rhs;
val pong = “MAP (^n2w8 o ORD) "pong"” |> EVAL |> concl |> rhs;

Definition KNil_def :
  KNil = K []
End

val _ = ml_prog_update (open_module "pingpong");


val _ = next_ml_names := ["KNil"];
Theorem KNil_v_thm = translate KNil_def;

val _ = ml_prog_update (close_module NONE);

Definition pingpong_def:
  pingpong =
  Let "v" ^ping (KNil) []
   (Com ^ping "v" ^pong "v"
     (Com ^pong "v" ^ping "v"
       Nil
     )
   )
End

Definition pingpong_conf:
  pingpong_conf =
  <| payload_size := 1;
     length := ^(get_fun_name ``LENGTH``);
     null := ^(get_fun_name ``null``);
     take := ^(get_fun_name ``mllist$take``);
     drop := ^(get_fun_name ``mllist$drop``);
     toList := Long "ChorLib" (Short "toList");
     fromList := Long "ChorLib" (Short "fromList");
     concat := ^(get_fun_name ``FLAT``);
     append := Long "ChorLib" (Short "append");
     cons := Short "::";
     nil := Short "[]";
     letModule := "pingpong";
   |>
End

Theorem compile_to_payload_thm =
  “projection pingpong_conf FEMPTY pingpong [^ping; ^pong]”
  |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY];

val [(ping_state,ping_code), (pong_state,pong_code)] =
  “endpoints ^(compile_to_payload_thm |> concl |> rhs)” |> EVAL |> concl |> rhs |>
  listSyntax.dest_list |> fst |> map pairSyntax.dest_pair |>
  map snd |> map pairSyntax.dest_pair

Theorem ping_to_cake_thm = “compile_endpoint pingpong_conf ["KNil"] ^ping_code” |> EVAL

val ping_to_cake_wholeprog =
  “SNOC (Dlet unknown_loc Pany ^(ping_to_cake_thm |> concl |> rhs))
        ^(ml_progLib.get_prog (get_ml_prog_state()))” |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "ping.sexp" ping_to_cake_wholeprog;



val _ = export_theory();

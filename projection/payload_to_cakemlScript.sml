open preamble payloadLangTheory astTheory

val _ = new_theory "payload_to_cakeml";

val letfuns_def = Define `
   (letfuns payloadLang$Nil = [])
∧ (letfuns (Send p v n e) = letfuns e)
∧ (letfuns (Receive p v l e) = letfuns e)
∧ (letfuns (IfThen v e1 e2) = letfuns e1 ++ letfuns e2)
∧ (letfuns (Let v f vl e) = f::letfuns e)`

val buffer_size_def = Define
  `buffer_size conf = Lit(IntLit(&(conf.payload_size + 1)))`

val payload_size_def = Define
  `payload_size conf = Lit(IntLit(&conf.payload_size))`

(* TODO: let length x *)
val padv_def = Define
  `padv conf =
   Fun "x"
   (Let (SOME "y")
    (App Aw8alloc [buffer_size conf;Lit(Word8 0w)])
    (If (App Equality [App Opapp [Var conf.length;Var(Short "x")];payload_size conf])
     (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 7w)])      
       (Let
         (SOME "z")
         (App Opapp [Var conf.fromList;App Opapp [Var conf.take; Var(Short"x"); payload_size conf]])
         (Let NONE
           (App CopyAw8Aw8 [Var(Short "z"); Lit(IntLit 0); payload_size conf;
                            Var(Short "y"); Lit(IntLit 1)])
           (Var(Short "y"))
         )
       )
     )
     (If (App (Opb Lt) [App Opapp [Var conf.length;Var(Short "x")];payload_size conf])
      (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 6w)])
        (Let (SOME "z") (App Opapp [Var conf.fromList;Var(Short"x")])
          (Let NONE
            (App Aw8update
                 [Var(Short "y");
                  App (Opn Minus)
                      [payload_size conf;
                       App Aw8length [Var(Short "z")]];
                  Lit(Word8 1w)
                 ]
            )
            (Let NONE
              (App CopyAw8Aw8
                   [Var (Short "z");
                    Lit(IntLit 0);
                    App Aw8length [Var(Short "z")];
                    Var(Short "y");
                    App (Opn Minus)
                        [payload_size conf;
                         App (Opn Plus) [App Aw8length [Var(Short "z")];Lit(IntLit 1)]
                        ]
                   ]
              )
              (Var (Short "y"))
            )
          )
        )
      )
      (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 2w)])
       (Let
         (SOME "z")
         (App Opapp [Var conf.fromList;App Opapp [Var conf.take; Var(Short"x"); payload_size conf]])
         (Let NONE
           (App CopyAw8Aw8 [Var(Short "z"); Lit(IntLit 0); payload_size conf;
                            Var(Short "y"); Lit(IntLit 1)])
           (Var (Short "y"))
         )
       )
      )
     )
    )
   )
`

val unpadv_def = Define
  `unpadv conf = (ARB:exp)
`

val sendloop_def =
  Define `sendloop conf =
   Letrec
   [("sendloop","x",
     If (App Opapp [Var conf.null;Var(Short "x")])
        (Con NONE [])
        (Let (SOME "y")
          (App Opapp [Var conf.take;Var (Short "x");payload_size conf])
          ARB
        )
    )]
  `

val compile_endpoint_def = Define `
   (compile_endpoint conf vs payloadLang$Nil = Con NONE [])
∧  (compile_endpoint conf vs (Send p v n e) = ARB)
∧ (compile_endpoint conf vs (Receive p v l  e) = ARB)
∧ (compile_endpoint conf vs (IfThen v e1 e2) =
   let vn = LENGTH(letfuns e1) in
     If (Var(Short v))
        (compile_endpoint conf (TAKE vn vs) e1)
        (compile_endpoint conf (DROP vn vs) e2))
∧ (compile_endpoint (hv::vs) conf (payloadLang$Let v f vl e) =
   ast$Let (SOME v)
       (App Opapp (hv::MAP (Var o Short) vl))
       (compile_endpoint conf vs e))`

val _ = export_theory ();

open preamble payloadLangTheory astTheory;
     

val _ = new_theory "payload_to_cakeml";

(* List of all functions used to compute let-expressions by an
   endpoint, in order of occurence
 *)
val letfuns_def = Define ‘
   (letfuns payloadLang$Nil = [])
∧ (letfuns (Send p v n e) = letfuns e)
∧ (letfuns (Receive p v l e) = letfuns e)
∧ (letfuns (IfThen v e1 e2) = letfuns e1 ++ letfuns e2)
∧ (letfuns (Let v f vl e) = f::letfuns e)’;

val getLetID_def = Define ‘
  getLetID conf letStr = Long conf.letModule (Short letStr)’;

val buffer_size_def = Define
  ‘buffer_size conf = Lit(IntLit(&(conf.payload_size + 1)))’;

val payload_size_def = Define
  ‘payload_size conf = Lit(IntLit(&conf.payload_size))’;

(* Simple helper functions to convert HOL datums and list of datum to CakeML AST *)
val convDatum_def = Define
  ‘
  (convDatum conf []    = Con (SOME conf.nil) []) ∧
  (convDatum conf (x::xs) = Con (SOME conf.cons) [Lit (Word8 x); convDatum conf xs]) 
  ’;

val convDatumList_def = Define
  ‘
  (convDatumList conf []    = Con (SOME conf.nil) []) ∧
  (convDatumList conf (x::xs) = Con (SOME conf.cons) [convDatum conf x; convDatumList conf xs]) 
  ’;

(* Simple helper function to convert HOL list of CakeML expressions into CakeML list of
CakeML expressions *)
val convList_def = Define
  ‘
  (convList conf []    = Con (SOME conf.nil) []) ∧
  (convList conf (x::xs) = Con (SOME conf.cons) [x; convList conf xs]) 
  ’;

(* CakeML deep embedding of message padding function *)
val padv_def = Define
  ‘padv conf =
   Fun "x"
   (Let (SOME "y")
    (App Aw8alloc [buffer_size conf;Lit(Word8 0w)])
    (If (App Equality [App Opapp [Var conf.length;Var(Short "x")];payload_size conf])
     (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 7w)])      
       (Let
         (SOME "z")
         (App Opapp [Var conf.fromList;App Opapp [App Opapp [Var conf.take; Var(Short"x")]; payload_size conf]])
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
                    App (Opn Plus)
                        [Lit(IntLit 1);
                         App (Opn Minus)
                             [payload_size conf;App Aw8length [Var(Short "z")]]
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
         (App Opapp [Var conf.fromList;App Opapp [App Opapp [Var conf.take; Var(Short"x")]; payload_size conf]])
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
’;

(* This loop encodes the payloadLang Send prefix,
   with a one-to-one correspondence between #(send)
   FFI calls and LSend labels. *)
val sendloop_def = Define ‘sendloop conf dest = 
   [("sendloop","x",
     Let (SOME "y")
       (App Opapp [padv conf;Var(Short "x")])
       (Let NONE
         (App (FFI "send") [Lit(StrLit dest); Var (Short "y")])
         (If
           (App (Opb Leq) [App Opapp [Var conf.length; Var(Short "x")];
                           payload_size conf]
           )
           (Con NONE [])
           (Let (SOME "x") (App Opapp [App Opapp [Var conf.drop; Var (Short "x")];
                                       payload_size conf])
                (App Opapp [Var(Short "sendloop"); Var(Short "x")])
           )
         )
       )
    )]’;

(* Find the first occurence of 1 in a W8array x, which
   is assumed to be in scope. *)
val find_one_def = Define
  ‘find_one =
   [("find_one","n",
     If (App (Opb Leq) [App Aw8length [Var (Short "x")]; Var(Short "n")])
      (App Aw8length [Var (Short "x")])
      (If (App Equality [Lit (Word8 1w); App Aw8sub [Var(Short "x"); Var(Short "n")]])
        (Var (Short "n"))
        (App Opapp [Var(Short "find_one"); App (Opn Plus) [Var(Short "n"); Lit(IntLit 1)]])
      )
   )]’;

(* True iff x is a W8array containing a message tagged as final. *)
val finalv_def = Define
  ‘finalv x =
   Log Or
       (App Equality [Lit (Word8 7w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])
       (App Equality [Lit (Word8 2w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])’;

(* True iff x is a W8array containing a message tagged correctly. *)
val validv_def = Define
  ‘validv x =
   Log Or
       (App Equality [Lit (Word8 6w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])
       (finalv x)’;

(* CakeML deep embedding of the unpad function. *)
val unpadv_def = Define
        ‘unpadv conf = 
         Fun "x"
         (If (validv "x")
         (Let (SOME "n")
           (If (finalv "x")
              (Lit(IntLit 1))
              (App (Opn Plus) [Lit (IntLit 1);
              Letrec find_one (App Opapp [Var(Short "find_one"); Lit(IntLit 1)])])
           )
           (If (App Equality [Var (Short "n");
                              App (Opn Plus) [Lit (IntLit 1);
                                              App Aw8length [Var (Short "x")]
                                              ]
                              ])
            (Con (SOME conf.nil) [])
            (Let (SOME "y")
                (App Aw8alloc
                     [App (Opn Minus)
                          [App Aw8length [Var (Short "x")];
                           Var(Short "n")];
                      Lit(Word8 0w)
                     ]
                )
                (Let NONE
                     (App CopyAw8Aw8
                          [Var(Short "x");
                           Var(Short "n");
                           App Aw8length [Var (Short "y")];
                           Var(Short "y");
                           Lit(IntLit 0)
                          ]
                     )
                     (App Opapp [Var conf.toList; Var(Short "y")]
                     )
                )
            )
           )
           )
         (Con (SOME conf.nil) []))
  ’;

(* This loop encodes the payloadLang Receive prefix,
   with a one-to-one correspondence between #(receive)
   FFI calls and LReceive labels. A buffer named buff
   of length conf.payload_size is assumed to be in scope *)
val receiveloop_def = Define ‘receiveloop conf src =
  [("receiveloop","u",
    (Let NONE (App (FFI "receive") [Lit(StrLit src); Var(Short "buff")])
       (If (finalv "buff")
          (Con (SOME conf.cons)
               [App Opapp [unpadv conf;Var(Short "buff")];
                Con(SOME conf.nil) []])
          (Con(SOME conf.cons)
               [App Opapp [unpadv conf;Var(Short "buff")];
                App Opapp [Var(Short "receiveloop");Var(Short "u")]
               ]
          )
       )
    )
  )]’;

(* compile_endpoint conf vs e

   (Static parts of) the compilation of endoint e to CakeML.

   In particular, does not compile the functions used in let expressions.
   Instead, assumes that the i:th element of vs is a CakeML expression
   whose value refines the i:th element of letfuns(e).
   It is expected that these will be obtained by translating the letfuns.
         
   The compilation depends on some functions from the CakeML basis library,
   mostly for routine list operations. In order to avoid this directory
   having to depend on basis, we assume that, eg., conf.append is the name
   of a function that refines APPEND.
 *)

val ps2cs_def = Define
  ‘
  ps2cs ps = #"P"::ps
  ’;

val w1ckV_def = Define
  ‘
  w1ckV conf = Con (SOME conf.cons) [Lit (Word8 1w);Con (SOME conf.nil) []]
  ’;

val compile_endpoint_def = Define ‘
   (compile_endpoint conf vs payloadLang$Nil = Con NONE [])
∧ (compile_endpoint conf vs (Send p v n e) =
    let vv = Var(Short (ps2cs v)) in
      If (App (Opb Leq) [App Opapp [Var conf.length; vv]; Lit(IntLit(&n))])
         (compile_endpoint conf vs e)
         (Let NONE
           (Letrec
              (sendloop conf (MAP (CHR o w2n) p))
              (App Opapp [Var(Short "sendloop");
                          App Opapp [App Opapp [Var conf.drop; vv]; Lit(IntLit(&n))]
              ])
           )
           (compile_endpoint conf vs e)
         )
  )
∧ (compile_endpoint conf vs (Receive p v l e) =
    Let (SOME v)
        (Let (SOME "buff") (App Aw8alloc [buffer_size conf;Lit(Word8 0w)])
             (Letrec
                (receiveloop conf (MAP (CHR o w2n) p))
                (App Opapp
                     [
                      App Opapp
                        [
                          Var conf.concat;
                          App Opapp [
                                      Var(Short "receiveloop");
                                      Con NONE []
                                    ]
                        ];
                      convDatumList conf l
                      ]
                )
             )
        )
        (compile_endpoint conf vs e)
   )
∧ (compile_endpoint conf vs (IfThen v e1 e2) =
   let vn = LENGTH(letfuns e1) in
     If (App Equality [Var(Short (ps2cs v)); w1ckV conf])
        (compile_endpoint conf (TAKE vn vs) e1)
        (compile_endpoint conf (DROP vn vs) e2))
∧ (compile_endpoint conf (hv::vs) (payloadLang$Let v f vl e) =
   ast$Let (SOME (ps2cs v))
       (App Opapp [((ast$Var o (getLetID conf)) hv);convList conf (MAP (Var o Short o ps2cs) vl)])
       (compile_endpoint conf vs e))’;

val _ = export_theory ();

structure projectionLib :> projectionLib =
struct
  (* TODO: open local parse context like a good boy *)
  open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
  open chorLibProgTheory;
  open fromSexpTheory;
  open astToSexprLib;

  val n2w8 = “n2w:num -> word8”;

  fun pnames chor =
      “MAP (MAP (CHR o w2n)) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map stringSyntax.fromHOLstring

  fun letfunstbl chor =
     “MAP (λp. (MAP (CHR o w2n) p, letfunsOf p ^chor)) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map pairSyntax.dest_pair
     |> map (fn (n,l) => (stringSyntax.fromHOLstring n,fst(listSyntax.dest_list l)))

  fun rectbl chor =
     “MAP (λp. (MAP (CHR o w2n) p, MAP (MAP (CHR o w2n)) (receiversOf p ^chor))) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map pairSyntax.dest_pair
     |> map (fn (n,l) => (stringSyntax.fromHOLstring n,
                          map stringSyntax.fromHOLstring(fst(listSyntax.dest_list l))))

  fun mk_camkes_assembly chor =
      let
        val rectbl = rectbl chor
        val pns = map fst rectbl
        fun mk_import name =
            String.concat ["import \"components/",name,"/",name,"/",name,".camkes\";\n"]
        fun mk_component_decl name =
            String.concat ["        component ",name," ",name,";\n"]
        fun mk_connections (p,qs) =
            map
              (fn q =>
                  String.concat [
                    "        connection seL4RPCCall ",
                    p,"_to_",q,
                    "(from ",p,".",q,"_send, to ",q,".",p,"_recv);\n"
                  ])
              qs |> String.concat
        val imports = map mk_import pns
        val decls = map mk_component_decl pns
        val connections = map mk_connections rectbl
      in
        String.concat [
          "import <std_connector.camkes>;\n",
          "\n",
          "import \"interfaces/TransferString.idl4\";\n",
          String.concat imports,
          "\n",
          "assembly {\n",
          "    composition {\n",
          "        component Producer producer;\n",
          String.concat decls,
          "\n",
          String.concat connections,
          "    }\n",
          "}\n"
        ]
      end

  fun reverse_table tbl =
      map
        (fn (p,_) =>
            (p,filter (exists (curry op = p) o snd) tbl |> map fst)
        ) tbl

  fun mk_component_declarations chor =
      let
        val rectbl = rectbl chor
        val rrectbl = reverse_table rectbl
        val bidirtbl = ListPair.map (fn ((p,qs),(_,rs)) => (p,qs,rs)) (rectbl,rrectbl)
        fun mk_provides p qs =
            map (fn q => String.concat ["    provides TransferString ",q,"__recv;\n"]) qs
        fun mk_uses p qs =
            map (fn q => String.concat ["    uses TransferString ",q,"__send;\n"]) qs
      in
        map
          (fn (p,qs,rs) =>
              (p,
               String.concat
                 ["component ",p," {\n",
                  "    control;\n",
                  String.concat(mk_provides p rs),
                  String.concat(mk_uses p rs),
                  "    has binary_semaphore binsem;\n",
                  "}\n"
                 ]
              )
          )
          bidirtbl
      end

  (* TODO: what should permissions be? *)
  (* TODO: check directory existence *)
  fun mkdir dname =
      Posix.FileSys.mkdir(dname,Posix.FileSys.S.irwxu)
      handle SysErr(_, SOME EEXISTS) =>
             print("Warning: directory "^dname^" already exists! Contents may be overwritten.\n")

  fun print_to_file fname contents =
      let
        val st = TextIO.openOut fname
      in
        TextIO.output(st,contents);
        TextIO.closeOut st
      end

  fun mk_camkes_boilerplate builddir chorname chor =
      let
        val _ = mkdir builddir
        val _ = mkdir(builddir^"/components")
        val _ = mkdir(builddir^"/interfaces")
        val _ = print_to_file (builddir^"/"^chorname^".camkes") (mk_camkes_assembly chor)
        fun print_component_declaration (p,contents) =
            let
              val _ = mkdir(builddir^"/components/"^p)
            in
              print_to_file (builddir^"/components/"^p^"/"^p^".camkes") contents
            end
        val _ = mk_component_declarations chor |> List.app print_component_declaration
      in
        ()
      end

  fun project_to_cake_with_letfuns chor p payload_size letmodule letfuns =
    let
      val ptm = “MAP (^n2w8 o ORD) ^(stringSyntax.fromMLstring p)” |> EVAL |> concl |> rhs
      val conf =
          “base_conf with <|payload_size := ^(numSyntax.term_of_int payload_size);
                            letModule := ^(stringSyntax.fromMLstring letmodule)|>”
      val compile_to_payload_thm =
          “projection ^conf FEMPTY ^chor (procsOf ^chor)”
           |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY]
      val (p_state,p_code) =
          “THE(ALOOKUP (endpoints ^(compile_to_payload_thm |> concl |> rhs)) ^ptm)”
          |> EVAL |> concl |> rhs |> pairSyntax.dest_pair

      val letfuns_tm =
          listSyntax.mk_list(map stringSyntax.fromMLstring letfuns, “:string”)


      val to_cake_thm = “compile_endpoint ^conf ^letfuns_tm ^p_code” |> EVAL

      val to_cake_wholeprog =
          “SNOC (Dlet unknown_loc Pany ^(to_cake_thm |> concl |> rhs))
           ^(ml_progLib.get_prog (get_ml_prog_state()))” |> EVAL |> concl |> rhs
    in
      (to_cake_thm,to_cake_wholeprog)
    end

  fun obtain_letfun tm =
      if can lookup_v_thm tm then
        let
          val vname = lookup_v_thm tm |> concl |> rator |> rand |> rand;
        in
          if term_eq (rator vname) “Short:(string -> (string,string) id)” then
            NONE
          else
            SOME(rand(rator vname),rand(rand vname))
        end
       else
        NONE

  fun project_to_cake chor p payload_size =
    let
      val ptm = “MAP (^n2w8 o ORD) ^(stringSyntax.fromMLstring p)” |> EVAL |> concl |> rhs

      val letfun_names = “letfunsOf ^ptm ^chor” |> EVAL |> concl |> rhs |> listSyntax.dest_list |> fst

      val letfuns = map obtain_letfun letfun_names

      val _ = if all isSome letfuns then
                ()
              else
                (print "Error: there are untranslated functions\n"; raise Domain);

      val letfuns = map valOf letfuns;

      val letmodule = if null letfuns then “ARB:string”
                      else if all (term_eq (fst(hd letfuns)) o fst) letfuns then
                        fst(hd letfuns)
                      else
                        (print "Error: all letfuns must inhabit the same module\n"; raise Domain);

      val conf =
          “base_conf with <|payload_size := ^(numSyntax.term_of_int payload_size);
                            letModule := ^letmodule|>”
      val compile_to_payload_thm =
          “projection ^conf FEMPTY ^chor (procsOf ^chor)”
           |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY]
      val (p_state,p_code) =
          “THE(ALOOKUP (endpoints ^(compile_to_payload_thm |> concl |> rhs)) ^ptm)”
          |> EVAL |> concl |> rhs |> pairSyntax.dest_pair

      val letfun_names = “letfuns ^p_code” |> EVAL |> concl |> rhs |> listSyntax.dest_list |> fst

      val letfuns = map obtain_letfun letfun_names

      val _ = if all isSome letfuns then
                ()
              else
                (print "Error: there are untranslated functions\n"; raise Domain);

      val letfuns_tm = listSyntax.mk_list(map (snd o valOf) letfuns, “:string”)

      val to_cake_thm = “compile_endpoint ^conf ^letfuns_tm ^p_code” |> EVAL

      val to_cake_wholeprog =
          “SNOC (Dlet unknown_loc Pany ^(to_cake_thm |> concl |> rhs))
           ^(ml_progLib.get_prog (get_ml_prog_state()))” |> EVAL |> concl |> rhs
    in
      (to_cake_thm,to_cake_wholeprog)
    end

end

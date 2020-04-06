structure projectionLib =
struct
  (* TODO: open local parse context like a good boy *)

  fun pnames chor =
      “MAP (MAP (CHR o w2n)) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map stringSyntax.fromHOLstring

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
end

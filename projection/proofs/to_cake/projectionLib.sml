structure projectionLib :> projectionLib =
struct
  (* TODO: open local parse context like a good boy *)
  open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
  open compilationProofTheory;
  open chorLibProgTheory;
  open fromSexpTheory;
  open astToSexprLib;

  val n2w8 = “n2w:num -> word8”;
  val camkes_payload_size = 256
  (* Buffer size must be at least payload_size + 1 and be 4096-aligned *)
  fun buf_size n =
      if (n + 1) mod 4096 = 0 then
        n + 1
      else
        (n + 1) + (4096 - ((n + 1) mod 4096))

  val queue_size = 1 (* TODO: factor out *)

  fun pnames chor =
      “procsOf ^chor”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map stringSyntax.fromHOLstring

  fun letfunstbl chor =
     “MAP (λp. (p, chorSem$letfunsOf p ^chor)) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map pairSyntax.dest_pair
     |> map (fn (n,l) => (stringSyntax.fromHOLstring n,fst(listSyntax.dest_list l)))

  fun rectbl chor =
     “MAP (λp. (p, receiversOf p ^chor)) (procsOf ^chor)”
     |> EVAL
     |> concl
     |> rhs
     |> listSyntax.dest_list
     |> fst
     |> map pairSyntax.dest_pair
     |> map (fn (n,l) => (stringSyntax.fromHOLstring n,
                          map stringSyntax.fromHOLstring(fst(listSyntax.dest_list l))))

  val transfer_string =
      String.concat [
        "procedure TransferString {\n",
        "    void transfer_string(in string s);\n",
        "};\n"]

  fun mk_camkes_assembly chor =
      let
        val rectbl = rectbl chor
        val pns = map fst rectbl
        fun mk_import name =
            String.concat ["import \"components/",name,"/",name,".camkes\";\n"]
        fun mk_component_decl name =
            String.concat ["        component ",name," ",name,";\n"]
        fun mk_connections (p,qs) =
            map
              (fn q =>
                  String.concat [
                    "        connection seL4RPCCall ",
                    p,"_to_",q,
                    "(from ",p,".",q,"_send, to ",q,".",p,"_recv);\n",
                    "        connection seL4SharedData ",
                    p,"_to_",q,"_data",
                    "(from ",p,".",q,"_out, to ",q,".",p,"_in);\n"
                  ])
              qs |> String.concat

        fun mk_configs (p,qs) =
            map
              (fn q =>
                  String.concat [
                    "        ",q,".",p,"_empty_value = 1;\n", (* todo: queue_size *)
                    "        ",q,".",p,"_usequeue_value = 1;\n",
                    "        ",q,".",p,"_full_value = 0;\n"
                  ])
              qs |> String.concat

        val imports = map mk_import pns
        val decls = map mk_component_decl pns
        val connections = map mk_connections rectbl
        val configs = map mk_configs rectbl
      in
        String.concat [
          "import <std_connector.camkes>;\n",
          "\n",
          "import \"interfaces/TransferString.idl4\";\n",
          String.concat imports,
          "\n",
          "assembly {\n",
          "    composition {\n",
          String.concat decls,
          "\n",
          String.concat connections,
          "    }\n\n",
          "    configuration {\n",
          String.concat configs,
          "    }\n",
          "}\n"
        ]
      end

  fun mk_camkes_cmakefile chorname chor =
      let
        val pnames = pnames chor
        val set_dirs =
            map (fn p => "set("^p^"_dir ${CMAKE_CURRENT_LIST_DIR}/components/"^p^"/)\n") pnames
        val custom_commands =
            map (fn p =>
                    String.concat [
                      "add_custom_command(\n",
                      "  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/"^p^".S\n",
                      String.concat [
                        "  COMMAND ${CAKEML_COMPILER} --exclude_prelude=true --sexp=true < ${",
                        p,"_dir}/",p,".sexp > ${CMAKE_CURRENT_BINARY_DIR}/",
                        p,".S\n"],
                      ")\n\n"
                    ])
                pnames
        val component_decls =
            map (fn p =>
                    String.concat [
                      "DeclareCAmkESComponent(",p,"\n",
                      "  SOURCES components/",p,"/",p,".c ",
                      "${CMAKE_CURRENT_BINARY_DIR}/",p,".S\n",
                      ")\n\n"
                    ])
                pnames
      in
        String.concat [
          "cmake_minimum_required(VERSION 3.8.2)\n",
          "\n",
          "project("^chorname^" C)\n",
          "\n",
          "add_definitions(-DCAMKES)\n",
          "\n",
          "find_program(CAKEML_COMPILER NAMES \"cake\")\n",
          "\n",
          String.concat set_dirs,
          "\n",
          String.concat custom_commands,
          "includeGlobalComponents()\n",
          "\n",
          String.concat component_decls,
          "DeclareCAmkESRootserver("^chorname^".camkes)\n"
        ]
      end

  fun reverse_table tbl =
      map
        (fn (p,_) =>
            (p,List.filter (exists (curry op = p) o snd) tbl |> map fst)
        ) tbl

  fun mk_component_declarations chor =
      let
        val rectbl = rectbl chor
        val rrectbl = reverse_table rectbl
        val bidirtbl = ListPair.map (fn ((p,qs),(_,rs)) => (p,qs,rs)) (rectbl,rrectbl)
        fun mk_provides p qs =
            map (fn q =>
                    String.concat [
                      "    provides TransferString ",q,"_recv;\n",
                      "    dataport Buf(",Int.toString(buf_size camkes_payload_size),") ",q,"_in;\n"
                    ]
                )
                qs
        fun mk_uses p qs =
            map (fn q =>
                    String.concat [
                      "    uses TransferString ",q,"_send;\n",
                      "    dataport Buf(",Int.toString(buf_size camkes_payload_size),") ",q,"_out;\n"]) qs
        fun mk_semaphore name =
            String.concat ["    has binary_semaphore ",name,";\n"]
        fun mk_semaphores qs =
            map (fn q => String.concat [mk_semaphore(q^"_usequeue"),
                                        mk_semaphore(q^"_empty"),
                                        mk_semaphore(q^"_full")]) qs
      in
        map
          (fn (p,qs,rs) =>
              (p,
               String.concat
                 ["component ",p," {\n",
                  "    control;\n",
                  String.concat(mk_provides p rs),
                  String.concat(mk_uses p qs),
                  String.concat(mk_semaphores rs),
                  "}\n"
                 ]
              )
          )
          bidirtbl
      end

  fun mk_camkes_glue_code(p,rs,qs) =
      let
        fun ffisendline r =
            String.concat (
              [
                " if (strcmp(c,\"",r,"\")==0) {\n",
                "    my_strcpy(a,(char *)",r,"_out);\n",
                "    ",r,"_send_transfer_string(\"\");\n",
                "  }\n"
              ]
            )

        fun ffireceiveline q =
            String.concat [
              " if (strcmp(c,\"",q,"\")==0) {\n",
              "    assert(",q,"_full_wait() == 0);\n",
              "    assert(",q,"_usequeue_wait() == 0);\n",
              "    my_strcpy(",q,"_ins,a);\n",
              "    assert(",q,"_usequeue_post() == 0);\n",
              "    assert(",q,"_empty_post() == 0);\n",
              "  }\n"
            ]

        fun ffirecvmethod q =
            String.concat [
              "void ",q,"_recv_transfer_string(const char *s) {\n",
              "  assert(",q,"_empty_wait() == 0);\n",
              "  assert(",q,"_usequeue_wait() == 0);\n",
              "  my_strcpy((char *)",q,"_in,",q,"_ins);\n",
              "  assert(",q,"_usequeue_post() == 0);\n",
              "  assert(",q,"_full_post() == 0);\n",
              "}\n",
              "\n"
            ]

        val ffisend =
            if null rs then
              "ZF_LOGF(\"Unknown receiver: %s\\n\",c);\n"
            else
              String.concat
                ["  ZF_LOGE(\"",p," |-> %s: %s\\n\",c,a + unpad(a));\n",
                 " ",
                 String.concatWith "  else" (map ffisendline rs),
                 "  else {\n",
                 "    ZF_LOGF(\"Unknown receiver: %s\\n\",c);\n",
                 "  }\n"
                ]

        val ffireceive =
            if null qs then
              "ZF_LOGF(\"Unknown sender: %s\\n\",c);\n"
            else
              String.concat
                [" ",
                 String.concatWith "  else" (map ffireceiveline qs),
                 "  else {\n",
                 "    ZF_LOGF(\"Unknown sender: %s\\n\",c);\n",
                 "  }\n"
                ]

        val receivemethods = String.concat (map ffirecvmethod qs)
      in
        String.concat [
          "#include <stdio.h>\n",
          "#include <string.h>\n",
          "#include <stdlib.h>\n",
          "#include <unistd.h>\n",
          "#include <fcntl.h>\n",
          "#include <sys/stat.h>\n",
          "#include <sys/time.h>\n",
          "#include <assert.h>\n",
          "#include <camkes.h>\n",
          "\n",
          "static char cml_memory[1024*1024*2];\n", (* TODO: parameterise *)
          "unsigned int argc;\n",
          "char **argv;\n",
          "\n",
          "/* exported in cake.S */\n",
          "extern void cml_main(void);\n",
          "extern void *cml_heap;\n",
          "extern void *cml_stack;\n",
          "extern void *cml_stackend;\n",
          "\n",
          "/* run the control thread */\n",
          "int run(void) {\n",
          "    unsigned long sz = 1024*1024; // 1 MB unit\n",
          "    unsigned long cml_heap_sz = sz;    // Default: 1 MB heap\n", (* TODO: parameterise *)
          "    unsigned long cml_stack_sz = sz;   // Default: 1 MB stack\n", (* TODO: parameterise *)
          "\n",
          "    cml_heap = cml_memory;\n",
          "    cml_stack = cml_heap + cml_heap_sz;\n",
          "    cml_stackend = cml_stack + cml_stack_sz;\n",
          "    cml_main();\n",
          "    return 0;\n",
          "}\n",
          "\n",
          "/* This flag is on by default. It catches CakeML's out-of-memory exit codes\n",
          " * and prints a helpful message to stderr.\n",
          " * Note that this is not specified by the basis library.\n",
          " * */\n",
          "#define STDERR_MEM_EXHAUST\n",
          "\n",
          String.concat
            (map (fn q =>
                     String.concat ["volatile unsigned char ",q,"_ins[",
                                    Int.toString(camkes_payload_size + 2),
                                    "];\n"])
                 qs),
          "\n",
          "void my_strcpy(char *s, volatile unsigned char *t) {\n",
          String.concat ["  int len = ",
                         Int.toString(camkes_payload_size + 1),
                         ";\n"],
          "  for (int i = 0; i <= len; i++) {\n",
          "    t[i] = s[i];\n",
          "  }\n",
          "}\n",
          "\n",
          receivemethods,
          "\n",
          "void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          "  ZF_LOGF(\"ffi_write not supported\\n\");\n",
          "}\n",
          "\n",
          "/* Returns the index of the first non-padding character in arr.\n",
          " */\n",
          "int unpad(char* arr) {\n",
          "  if(arr[0] == 7 || arr[0] == 2) return 1;\n",
          "  assert(arr[0] == 6);\n",
          "  int i = 1;\n",
          "  while(arr[i] == 0) {\n",
          "    i++;\n",
          "  }\n",
          "  return(i+1);\n",
          "}\n",
          "\n",
          "void ffisend (unsigned char *c, long clen, unsigned char *a, long alen) {  \n",
          ffisend,
          "}\n",
          "\n",
          "void ffireceive (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          ffireceive,
          "}\n",
          "\n",
          "/* GC FFI */\n",
          "int inGC = 0;\n",
          "struct timeval t1,t2,lastT;\n",
          "long microsecs = 0;\n",
          "int numGC = 0;\n",
          "int hasT = 0;\n",
          "\n",
          "void cml_exit(int arg) {\n",
          "\n",
          "  #ifdef STDERR_MEM_EXHAUST\n",
          "  if(arg == 1) {\n",
          "    fprintf(stderr,\"CakeML heap space exhausted.\\n\");\n",
          "  }\n",
          "  else if(arg == 2) {\n",
          "    fprintf(stderr,\"CakeML stack space exhausted.\\n\");\n",
          "  }\n",
          "  #endif\n",
          "\n",
          "  #ifdef DEBUG_FFI\n",
          "  {\n",
          "    fprintf(stderr,\"GCNum: %d, GCTime(us): %ld\\n\",numGC,microsecs);\n",
          "  }\n",
          "  #endif\n",
          "\n",
          "  exit(arg);\n",
          "}\n",
          "\n",
          "void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          "  assert(alen == 1);\n",
          "  exit((int)a[0]);\n",
          "}\n",
          "\n",
          "\n",
          "/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */\n",
          "void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          "  #ifdef DEBUG_FFI\n",
          "  {\n",
          "    if (clen == 0)\n",
          "    {\n",
          "      if(inGC==1)\n",
          "      {\n",
          "        gettimeofday(&t2, NULL);\n",
          "        microsecs += (t2.tv_usec - t1.tv_usec) + (t2.tv_sec - t1.tv_sec)*1e6;\n",
          "        numGC++;\n",
          "        inGC = 0;\n",
          "      }\n",
          "      else\n",
          "      {\n",
          "        inGC = 1;\n",
          "        gettimeofday(&t1, NULL);\n",
          "      }\n",
          "    } else {\n",
          "      int indent = 30;\n",
          "      for (int i=0; i<clen; i++) {\n",
          "        putc(c[i],stderr);\n",
          "        indent--;\n",
          "      }\n",
          "      for (int i=0; i<indent; i++) {\n",
          "        putc(' ',stderr);\n",
          "      }\n",
          "      struct timeval nowT;\n",
          "      gettimeofday(&nowT, NULL);\n",
          "      if (hasT) {\n",
          "        long usecs = (nowT.tv_usec - lastT.tv_usec) +\n",
          "                     (nowT.tv_sec - lastT.tv_sec)*1e6;\n",
          "        fprintf(stderr,\" --- %ld milliseconds\\n\",usecs / (long)1000);\n",
          "      } else {\n",
          "        fprintf(stderr,\"\\n\");\n",
          "      }\n",
          "      gettimeofday(&lastT, NULL);\n",
          "      hasT = 1;\n",
          "    }\n",
          "  }\n",
          "  #endif\n",
          "}\n",
          "\n",
          "// FFI calls for floating-point parsing\n",
          "void ffidouble_fromString (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          "  ZF_LOGF(\"Floating point printing/parsing not supported\\n\");\n",
          "}\n",
          "\n",
          "void ffidouble_toString (unsigned char *c, long clen, unsigned char *a, long alen) {\n",
          "  ZF_LOGF(\"Floating point printing/parsing not supported\\n\");\n",
          "}\n"
        ]
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

  fun mk_camkes_glue_codes chor =
      let
        val rectbl = rectbl chor
        val rrectbl = reverse_table rectbl
        val bidirtbl = ListPair.map (fn ((p,qs),(_,rs)) => (p,qs,rs)) (rectbl,rrectbl)
      in
        map (fn tup => (#1 tup, mk_camkes_glue_code tup)) bidirtbl
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
        fun print_camkes_glue_code (p,contents) =
              print_to_file (builddir^"/components/"^p^"/"^p^".c") contents
        val _ = mk_component_declarations chor |> List.app print_component_declaration
        val _ = mk_camkes_glue_codes chor |> List.app print_camkes_glue_code
        val _ = print_to_file(builddir^"/CMakeLists.txt") (mk_camkes_cmakefile chorname chor)
        val _ = print_to_file(builddir^"/interfaces/TransferString.idl4") transfer_string
      in
        ()
      end

  fun project_to_cake_with_letfuns chor p payload_size letmodule letfuns =
    let
      val ptm = stringSyntax.fromMLstring p
      val conf =
          “base_conf with <|payload_size := ^(numSyntax.term_of_int payload_size);
                            letModule := ^(stringSyntax.fromMLstring letmodule)|>”
      val compile_to_payload_thm =
          “projection_top ^conf FEMPTY ^chor (procsOf ^chor)”
           |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY]
           |> CONV_RULE(RHS_CONV EVAL)
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
      val ptm = stringSyntax.fromMLstring p

      val letfun_names = “chorSem$letfunsOf ^ptm ^chor” |> EVAL |> concl |> rhs |> listSyntax.dest_list |> fst

      val letfuns = map obtain_letfun letfun_names

      val kfun = obtain_letfun “K0”

      val _ = if all isSome (kfun::letfuns) then
                ()
              else
                (print "Error: there are untranslated functions\n"; raise Domain);

      val letfuns = map valOf letfuns;

      val letmodule = if null letfuns then
                        if isSome kfun then
                          fst(valOf kfun)
                        else
                          (print "Error: K0 should be among the letfuns\n"; raise Domain)
                      else if all (term_eq (fst(hd letfuns)) o fst) letfuns then
                        fst(hd letfuns)
                      else
                        (print "Error: all letfuns must inhabit the same module\n"; raise Domain);

      val conf =
          “base_conf with <|payload_size := ^(numSyntax.term_of_int payload_size);
                            letModule := ^letmodule|>”
      val compile_to_payload_thm =
          “projection_top ^conf FEMPTY ^chor (procsOf ^chor)”
           |> EVAL |> PURE_REWRITE_RULE [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY]
           |> CONV_RULE(RHS_CONV EVAL)
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

  fun mk_projection_thm p chor pc =
    let
      val conf = pc |> concl |> lhs |> rator |> rator |> rand
      val pCd1 = pc |> concl |> lhs |> rand
      val vs = pc |> concl |> lhs |> rator |> rand
      val ptm = stringSyntax.fromMLstring p

      val oracle = “comms_ffi_oracle ^conf”
      val oracle_type = type_of oracle |> strip_fun |> fst |> C (curry List.nth) 1
      fun subst_the_var rex tm =
          subst [hd(free_vars tm) |-> rex] tm

      val cst = get_ml_prog_state() |> get_state |> inst [alpha |-> oracle_type] |>
                                 subst_the_var “initial_ffi_state ^oracle (^ptm,FEMPTY,net_filter ^ptm (projection_top ^conf FEMPTY ^chor (procsOf ^chor)))”
      val cenv = get_ml_prog_state() |> get_env

      val eval_assm = C MP TRUTH o CONV_RULE(LAND_CONV(EVAL))

      val env_asm =
          env_asm_extend
            |> PURE_ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
            |> C MATCH_MP chorLibProgTheory.env_asm_base_conf
            |> SPEC cenv
            |> eval_assm

      val cvs = env_asm |> concl |> rand

      val enc_ok_thm =
          auto_prove "enc_ok"
            (“enc_ok ^conf ^cenv (letfuns ^pCd1) ^vs”,
             PURE_REWRITE_TAC [enc_ok_alt,payload_to_cakemlTheory.letfuns_def,boolTheory.AND_CLAUSES,
                               payload_to_cakemlTheory.getLetID_def,payloadLangTheory.state_accfupds,
                               payloadLangTheory.config_accfupds,listTheory.APPEND] >>
             SIMP_TAC std_ss [] >>
             rpt conj_tac >>
             MAP_FIRST match_mp_tac
                       (“(letfuns ^pCd1)” |> EVAL |> concl |> rhs |>
                        listSyntax.dest_list |> fst
                        |> map lookup_v_thm |> map DISCH_ALL) >>
             CONV_TAC(LHS_CONV EVAL) >>
             MATCH_ACCEPT_TAC EQ_REFL)
    in
      compilation_preservation
        |> Q.SPEC ‘FEMPTY’
        |> SPEC chor
        |> SPEC(mk_var("s2",“:string # string |-> word8 list”))
        |> SPEC(mk_var("c2",“:chorLang$chor”))
        |> SPEC conf
        |> SPEC ptm
        |> Q.SPEC ‘<|bindings := FEMPTY; funs := []; queues := FEMPTY|>’
        |> SPEC pCd1
        |> Q.SPEC ‘projection_top ^conf FEMPTY ^chor (procsOf ^chor)’
        |> SPEC cst
        |> SPEC vs
        |> SPEC cenv
        |> SPEC cvs
        |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]
        |> UNDISCH
        |> eval_assm
        |> eval_assm
        |> eval_assm
        |> eval_assm
        |> CONV_RULE(LAND_CONV(SIMP_CONV pure_ss [EQ_REFL]))
        |> C MP TRUTH
        |> CONV_RULE(LAND_CONV EVAL)
        |> CONV_RULE(LAND_CONV (PURE_REWRITE_CONV [DRESTRICT_FEMPTY,MAP_KEYS_FEMPTY,FDOM_FEMPTY,NOT_IN_EMPTY,NOT_CLAUSES,bool_case_thm]))
        |> eval_assm
        |> eval_assm
        |> eval_assm
        |> CONV_RULE(LAND_CONV EVAL)
        |> CONV_RULE(LAND_CONV(SIMP_CONV std_ss []))
        |> C MP TRUTH
        |> CONV_RULE(LAND_CONV (PURE_REWRITE_CONV[payload_to_cakemlProofTheory.sem_env_cor_def,env_asm_simps]))
        |> PURE_ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        |> C MP env_asm
(*        |> CONV_RULE(LAND_CONV(SIMP_CONV
                                 (std_ss ++ pred_setLib.PRED_SET_ss)
                                 [payload_to_cakemlProofTheory.pSt_pCd_corr_def,
                                  payload_to_cakemlProofTheory.pFv_def,
                                  payloadLangTheory.state_accfupds,
                                  finite_mapTheory.FLOOKUP_EMPTY,
                                  listTheory.MEM]))
        |> C MP TRUTH*)
        |> C MP enc_ok_thm
        |> DISCH_ALL
    end

  fun project_to_camkes builddir chorname chor =
    let
      val pns = pnames chor
      val to_cakes = map(fn p => project_to_cake chor p camkes_payload_size) pns
      val thms = ListPair.map (fn (p,(pc,_)) => mk_projection_thm p chor pc) (pns,to_cakes)
      val _ = mk_camkes_boilerplate builddir chorname chor
      val _ = ListPair.map
                (fn (p,(_,p_wholeprog)) =>
                    astToSexprLib.write_ast_to_file
                      (String.concat [builddir,"/components/",p,"/",p,".sexp"])
                      p_wholeprog)
                (pns,to_cakes)
    in
      thms
    end

end

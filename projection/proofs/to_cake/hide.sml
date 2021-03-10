structure hide :> hide =
struct

open HolKernel boolLib
open hideTheory

val hidec = prim_mk_const{Thy = "hide", Name = "hide"}
val sv = mk_var("s", stringSyntax.string_ty)
val tv = mk_var("t", bool)

fun hide_pp (tyg,tmg) backend printer ppfns gravs depth t =
    let
      open term_pp_types term_pp_utils smpp
      val (f,xs) = strip_comb t
      val _ = same_const f hidec andalso length xs = 2 orelse
              raise UserPP_Failed
      val {add_string, ublock, add_break, ...} = ppfns:ppstream_funs
      fun syspr t =
          printer { gravs = gravs, depth = decdepth depth, binderp = false } t
    in
      ublock PP.CONSISTENT 2 (
        add_string "HIDDEN:" >> add_break(1, 0) >>
        syspr (hd xs)
      )
    end

fun install_hidepp() =
    temp_add_user_printer ("hide-printer", list_mk_comb(hidec, [sv,tv]),
                           hide_pp)

val _ = BasicProvers.logged_addfrags {thyname = "hide"}
          [simpLib.SSFRAG {ac = [], congs = [hideCONG],
                           convs = [], dprocs = [], filter = NONE,
                           name = SOME "hide", rewrs = []}]

fun mk_hide s t = list_mk_comb(hidec, [stringSyntax.fromMLstring s, t])
fun MK_HIDE s th =
    EQ_MP (SYM (SPECL [stringSyntax.fromMLstring s, concl th] hide_def)) th
val UNHIDE = CONV_RULE (REWR_CONV hide_def)

fun hide s th (asl,w) =
    ([(asl @ [mk_hide s (concl th)], w)],
     fn ths => PROVE_HYP (MK_HIDE s th) (hd ths))

fun dest_hide t =
    let val (f,xs) = strip_comb t
        val _ = same_const f hidec andalso length xs = 2 orelse
                raise mk_HOL_ERR "hide" "dest_hide" "Not a hide term"
        val s = stringSyntax.fromHOLstring (hd xs)
                handle HOL_ERR _ => raise mk_HOL_ERR "hide"
                                          "dest_hide"
                                          "First argument not a string literal"
    in
      (s,hd (tl xs))
    end

val is_hide = can dest_hide

fun unhide s =
    let fun do1 th =
            case total dest_hide (concl th) of
                NONE => th
              | SOME (s',_) => if s' = s then CONV_RULE (REWR_CONV hide_def) th
                               else th
    in
      RULE_ASSUM_TAC do1
    end

fun hide_assum s ttac =
    first_x_assum (fn th => ttac th THEN hide s th)

fun unhide_assum0 extractor k s ttac =
    let
      fun find th0 =
          case total dest_hide (concl th0) of
              NONE => NO_TAC
            | SOME (s', _) => if s = s' then
                                let val th = UNHIDE th0
                                in
                                  ttac th THEN k th
                                end
                              else NO_TAC
    in
      extractor find
    end

val unhide_assum = unhide_assum0 first_x_assum assume_tac
val unhide_x_assum = unhide_assum0 first_x_assum (K all_tac)
val use_hidden_assum = unhide_assum0 first_assum (K all_tac)

end

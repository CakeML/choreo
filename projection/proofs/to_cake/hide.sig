signature hide =
sig

  include Abbrev
  val mk_hide : string -> term -> term
  val is_hide : term -> bool
  val dest_hide : term -> string * term
  val install_hidepp : unit -> unit

  val MK_HIDE : string -> thm -> thm
  val UNHIDE : thm -> thm
  val hide : string -> thm -> tactic
  val unhide : string -> tactic
  val hide_assum : string -> thm_tactic -> tactic
  val unhide_assum : string -> thm_tactic -> tactic
  val unhide_x_assum : string -> thm_tactic -> tactic
  val use_hidden_assum : string -> thm_tactic -> tactic

end

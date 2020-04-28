signature projectionLib =
sig
  include Abbrev
  val pnames: term -> string list
  val rectbl: term -> (string * string list) list
  
  val mk_camkes_assembly : term -> string
  val mk_camkes_boilerplate : string -> string -> term -> unit
  val mk_component_declarations: term -> (string * string) list

  val project_to_cake_with_letfuns: term -> string -> int -> string -> string list -> thm * term
  val project_to_cake: term -> string -> int -> thm * term

  val mk_projection_thm: string -> term -> thm -> thm

  val project_to_camkes : string -> string -> term -> thm list
end

structure state_tacticLib :> state_tacticLib =
	struct
	open HolKernel Tactical;
	(* Reduce right-assoc addition term to list of all free
	   variables in sequence until non-variable or bound variable
	   found *)
	fun get_add_terms (bvs,t) =
		case Lib.total numSyntax.dest_plus t of
			NONE       => []
		|   SOME (l,r) =>
				if Term.is_var l andalso not (boolLib.tmem l bvs) then
					l::get_add_terms (bvs,r)
				else
					[]

	(* Fail if any given variable is free in assumptions or goal *)
	fun fail_if_free vars (G as (asl,w)) =
		let
			val all_free = flatten ((Term.free_vars w)::(map Term.free_vars asl))
		in
			(if null(Lib.op_intersect Term.aconv vars all_free) then
				ALL_TAC
			else
				NO_TAC) G
		end 

	(* Take an abbreviated left-assoc addition and return a theorem tactic
	   to rewrite the right-assoc version of the abbreviated addition *)
	fun genpmc th =
	let
		val mc          = Term.genvar “:num”
	in
		Rewrite.REWRITE_RULE [markerTheory.Abbrev_def] th |> Thm.SYM |>
							  Thm.AP_TERM numSyntax.plus_tm |> Lib.C Thm.AP_THM mc
							  |> Rewrite.REWRITE_RULE [Conv.GSYM arithmeticTheory.ADD_ASSOC]
							  |> Thm.GEN mc |> (fn th => Rewrite.PURE_REWRITE_TAC[th])
	end


	fun unite_nums nm (G as (asl,w)) =
	let
		(* tripaddP behaviour:
			- Try and match given term to right-assoc addition
				1. If NONE then return NONE
				2. If SOME match then:
					a. Retrieve x, y, and z variables
					b. Check x and y are free variables
						-> If False then return NONE
					c. Run get_add_terms to retrieve all added
					   free variables in z
					d. Create left-assoc addition of free variable
					   sequence
					e. Return SOME tactic to abbreviate left-assoc addition of found
					   free variables and the list of variables used in abbreviation *)
		val x = Term.genvar “:num”
		val y = Term.genvar “:num”
		val z = Term.genvar “:num”
		fun tripaddP (bvs,t) =
			case Lib.total (Term.match_term ``^x + (^y + ^z)``) t of
				SOME (theta,_) =>
				let
					val x_v   = valOf (Lib.subst_assoc (Term.aconv x) theta)
					val y_v   = valOf (Lib.subst_assoc (Term.aconv y) theta)
					val xy_vs = [x_v,y_v]
					val z_v   = valOf (Lib.subst_assoc (Term.aconv z) theta)
				in
					if (List.all Term.is_var xy_vs) andalso
					   null(Lib.op_intersect Term.aconv bvs xy_vs) then
					   let
					   	val z_vars   = get_add_terms (bvs,z_v)
					   	val xyz_vars = x_v::y_v::z_vars
					   	val arhs     = numSyntax.list_mk_plus xyz_vars
					   	val atac     = Q.ABBREV_TAC [QUOTE ("UNITE_NUMS_TEMP = "),ANTIQUOTE arhs]
					   in
					   	SOME (atac,xyz_vars)
					   end
					else
						NONE
				end
			|	NONE 		   => NONE
	in
		(* Behaviour:
		   - Try and find a subterm that tripaddP can produce tactic from.
		 		1. If NONE then fail.
		 		2. If SOME then:
		 			a. Apply abbreviation tactic to combined added numbers
		 			b. Use genpmc to handle right associated addition of
		 			   same numbers
		 			c. Check when addition of vars destroyed no free
		 			   versions elsewhere of some remain
		 			d. Rename UNITE_NUMS_TEMP to given nm with Abbrev
		 			e. Remove remaining Abbrev to just leave behind the
		 			   rename *)
		case gen_find_term tripaddP w of
			NONE    => NO_TAC
		| 	SOME (atac,vars) => atac >> first_x_assum genpmc >> (fail_if_free vars) >>
		                        Q.ABBREV_TAC [QUOTE (nm ^ " = "),QUOTE "UNITE_NUMS_TEMP"] >>
		                        first_x_assum (K ALL_TAC)
	end G

	end;

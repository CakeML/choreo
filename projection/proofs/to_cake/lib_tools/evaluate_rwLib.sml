structure evaluate_rwLib :> evaluate_rwLib =
	struct

	open preamble
     evaluateTheory terminationTheory ml_translatorTheory ml_progTheory
     evaluatePropsTheory namespaceTheory semanticPrimitivesTheory ffiTheory
     terminationTheory;

    structure Parse =
    struct
    	open Parse;
    	val (Type,Term) = parse_from_grammars evaluatePropsTheory.evaluateProps_grammars
    end

    (* Rewrite list for exploding HOL to CakeML translator
       correspondence functions *)
	val trans_sl =
	[UNIT_TYPE_def,
	INT_def,
	NUM_def,
	BOOL_def,
	WORD_def,
	CHAR_def,
	STRING_TYPE_def,
	EqualityType_def,
	LIST_TYPE_def];

	(* Basic CakeML evaluation semantics rewrite list. For
	   crunching CakeML semantics as much as possible *)
	val eval_sl =
	[evaluate_def,
	do_con_check_def,
	build_conv_def,
	do_log_def,
	And_def,
	Eq_def,
	do_if_def,
	Boolv_def,
	build_rec_env_def,
	do_app_def,
	do_opapp_def,
	do_eq_def,
	nsLookup_def,
	nsOptBind_def,
	nsBind_def,
	nsLookup_nsBind_compute,
	v_to_list_def,
	list_to_v_def,
	opn_lookup_def,
	opb_lookup_def,
	opw8_lookup_def,
	opw64_lookup_def,
	shift8_lookup_def,
	shift64_lookup_def,
	store_assign_def,
	store_v_same_type_def,
	store_alloc_def,
	store_lookup_def,
	copy_array_def,
	call_FFI_def,
	do_eq_def,
	lit_same_type_def,
	ctor_same_type_def];

	(* CakeML evaluation semantics rewrite list without FFI. For
	   crunching CakeML semantics whilst leaving FFI for manual handling. *)
	val eval_sl_nffi =
	[evaluate_def,
	do_con_check_def,
	build_conv_def,
	do_log_def,
	And_def,
	Eq_def,
	do_if_def,
	Boolv_def,
	build_rec_env_def,
	do_app_def,
	do_opapp_def,
	do_eq_def,
	nsLookup_def,
	nsOptBind_def,
	nsBind_def,
	nsLookup_nsBind_compute,
	v_to_list_def,
	list_to_v_def,
	opn_lookup_def,
	opb_lookup_def,
	opw8_lookup_def,
	opw64_lookup_def,
	shift8_lookup_def,
	shift64_lookup_def,
	store_assign_def,
	store_v_same_type_def,
	store_alloc_def,
	store_lookup_def,
	copy_array_def,
	do_eq_def,
	lit_same_type_def,
	ctor_same_type_def];

	(* evalaute semantics definition with App Opapp
	   definition excluded, used below *)
	val evaluate_nofunapp_simp =
        let
          val evaluate_op = Q.prove(‘∀st op es env.
		    op ≠ Opapp ⇒
		      (evaluate st env [App op es] =
		      (case evaluate st env (REVERSE es) of
		        (st',Rval vs) =>
		            (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
		               NONE => (st',Rerr (Rabort Rtype_error))
		             | SOME ((refs,ffi),r) =>
		               (st' with <|refs := refs; ffi := ffi|>,list_result r))
		      | (st',Rerr v9) => (st',Rerr v9)))’,
                      simp[evaluate_def]);
        in
          evaluate_def |> CONJUNCTS
                       |> filter (not o free_in ``Opapp`` o concl)
                       |> foldr (uncurry CONJ) evaluate_op
        end

	(* CakeML evaluation semantics rewrite list without function application. For
	   crunching CakeML semantics whilst leaving functions for manual handling.
	   Useful if functions can be handled with translation machinery at
	   App Opapp level instead of reducing them. *)
	val eval_sl_nf =
	[evaluate_nofunapp_simp,
	do_con_check_def,
	build_conv_def,
	do_log_def,
	And_def,
	Eq_def,
	do_if_def,
	Boolv_def,
	build_rec_env_def,
	do_app_def,
	do_eq_def,
	nsLookup_def,
	nsOptBind_def,
	nsBind_def,
	nsLookup_nsBind_compute,
	v_to_list_def,
	list_to_v_def,
	opn_lookup_def,
	opb_lookup_def,
	opw8_lookup_def,
	opw64_lookup_def,
	shift8_lookup_def,
	shift64_lookup_def,
	store_assign_def,
	store_v_same_type_def,
	store_alloc_def,
	store_lookup_def,
	copy_array_def,
	call_FFI_def,
	do_eq_def,
	lit_same_type_def,
	ctor_same_type_def];


	end;

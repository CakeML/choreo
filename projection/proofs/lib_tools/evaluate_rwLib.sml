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

	val evaluate_nofunapp_simp =
	prove(
		“
		(∀st env. evaluate st env [] = (st,Rval [])) ∧
		(∀st es env e2 e1.
		    evaluate st env (e1::e2::es) =
		    case evaluate st env [e1] of
		      (st',Rval v1) =>
		        (case evaluate st' env (e2::es) of
		           (st'',Rval vs) => (st'',Rval (HD v1::vs))
		         | (st'',Rerr v8) => (st'',Rerr v8))
		    | (st',Rerr v10) => (st',Rerr v10)) ∧
		(∀st l env. evaluate st env [Lit l] = (st,Rval [Litv l])) ∧
		(∀st env e.
		    evaluate st env [Raise e] =
		    case evaluate st env [e] of
		      (st',Rval v) => (st',Rerr (Rraise (HD v)))
		    | (st',Rerr v8) => (st',Rerr v8)) ∧
		(∀st pes env e.
		    evaluate st env [Handle e pes] =
		    case evaluate st env [e] of
		      (st',Rval v7) => (st',Rval v7)
		    | (st',Rerr (Rraise v)) => evaluate_match st' env v pes v
		    | (st',Rerr (Rabort v12)) => (st',Rerr (Rabort v12))) ∧
		(∀st es env cn.
		    evaluate st env [Con cn es] =
		    if do_con_check env.c cn (LENGTH es) then
		      case evaluate st env (REVERSE es) of
		        (st',Rval vs) =>
		          (case build_conv env.c cn (REVERSE vs) of
		             NONE => (st',Rerr (Rabort Rtype_error))
		           | SOME v => (st',Rval [v]))
		      | (st',Rerr v8) => (st',Rerr v8)
		    else (st,Rerr (Rabort Rtype_error))) ∧
		(∀st n env.
		    evaluate st env [Var n] =
		    case nsLookup env.v n of
		      NONE => (st,Rerr (Rabort Rtype_error))
		    | SOME v => (st,Rval [v])) ∧
		(∀st op es env.
		    op ≠ Opapp ⇒
		      (evaluate st env [App op es] =
		      (case evaluate st env (REVERSE es) of
		        (st',Rval vs) =>
		            (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
		               NONE => (st',Rerr (Rabort Rtype_error))
		             | SOME ((refs,ffi),r) =>
		               (st' with <|refs := refs; ffi := ffi|>,list_result r))
		      | (st',Rerr v9) => (st',Rerr v9)))
		) ∧
		(∀x st env e. evaluate st env [Fun x e] = (st,Rval [Closure env x e])) ∧
		(∀st lop env e2 e1.
		    evaluate st env [Log lop e1 e2] =
		    case evaluate st env [e1] of
		      (st',Rval v1) =>
		        (case do_log lop (HD v1) e2 of
		           NONE => (st',Rerr (Rabort Rtype_error))
		         | SOME (Exp e) => evaluate st' env [e]
		         | SOME (Val v) => (st',Rval [v]))
		    | (st',Rerr v9) => (st',Rerr v9)) ∧
		(∀st env e3 e2 e1.
		    evaluate st env [If e1 e2 e3] =
		    case evaluate st env [e1] of
		      (st',Rval v) =>
		        (case do_if (HD v) e2 e3 of
		           NONE => (st',Rerr (Rabort Rtype_error))
		         | SOME e => evaluate st' env [e])
		    | (st',Rerr v8) => (st',Rerr v8)) ∧
		(∀st pes env e.
		    evaluate st env [Mat e pes] =
		    case evaluate st env [e] of
		      (st',Rval v) => evaluate_match st' env (HD v) pes bind_exn_v
		    | (st',Rerr v8) => (st',Rerr v8)) ∧
		(∀xo st env e2 e1.
		    evaluate st env [Let xo e1 e2] =
		    case evaluate st env [e1] of
		      (st',Rval v) =>
		        evaluate st' (env with v := nsOptBind xo (HD v) env.v) [e2]
		    | (st',Rerr v8) => (st',Rerr v8)) ∧
		(∀st funs env e.
		    evaluate st env [Letrec funs e] =
		    if ALL_DISTINCT (MAP (λ(x,y,z). x) funs) then
		      evaluate st (env with v := build_rec_env funs env env.v) [e]
		    else (st,Rerr (Rabort Rtype_error))) ∧
		(∀t st env e. evaluate st env [Tannot e t] = evaluate st env [e]) ∧
		(∀st l env e. evaluate st env [Lannot e l] = evaluate st env [e])
		”, simp[evaluate_def]);


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

	end;

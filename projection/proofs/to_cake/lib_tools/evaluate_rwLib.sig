signature evaluate_rwLib = 
sig
	include Abbrev
	val trans_sl:thm list
	val eval_sl_nf:thm list
	val eval_sl:thm list
	val eval_sl_nffi:thm list
end
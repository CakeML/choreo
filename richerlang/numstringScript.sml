open HolKernel Parse boolLib bossLib stringTheory listTheory numposrepTheory arithmeticTheory;

val _ = new_theory "numstring";

val _ = hide "STRING";

(* only positive integers *)        
Definition int_to_stringHelper_def:
  int_to_stringHelper n = if n < 10 then [(CHR (n+48))]
                          else
                            let r = n MOD 10 in
                              let d = n DIV 10 in
                                (CHR (r+48)) :: (int_to_stringHelper d)
End           

Definition int_to_string_def:
  int_to_string n =  (REVERSE (int_to_stringHelper n))
End        

(* handle invalid strings *)              
Definition string_to_intHelper2_def:
  string_to_intHelper2 "" = SOME 0 ∧
  string_to_intHelper2 (c::s) = if (((ORD c) < 48) ∨ ((ORD c) > 57))
                                then
                                  NONE
                                else
                                  case (string_to_intHelper2 s) of
                                    NONE => NONE
                                  | SOME n => SOME ((ORD c - 48) + n*10)
End

Definition string_to_int2_def:
  string_to_int2 s = if s = "" then NONE
                     else
                       string_to_intHelper2 (REVERSE s)
End


Theorem i2sHelper_EQ_NIL[simp]:
  ∀n. int_to_stringHelper n ≠ ""
Proof
  rw [Once int_to_stringHelper_def]
QED
                                                   
Theorem s2i_inverse:
  !n. string_to_int2(int_to_string(n)) = SOME n
Proof
  simp[int_to_string_def, string_to_int2_def]>>
  completeInduct_on ‘n’ >>
  rw [Once int_to_stringHelper_def]
  >- (rw [string_to_intHelper2_def])>>
  rw [string_to_intHelper2_def]
  >- (‘n MOD 10 + 48 < 256’ suffices_by simp [stringTheory.ORD_CHR_RWT]>>
      ‘n MOD 10 < 10’ suffices_by DECIDE_TAC>>simp[]   )
  >- (‘n MOD 10 < 10’ by simp[] >> ‘n MOD 10 + 48 < 256’ by simp[]>>
      simp [stringTheory.ORD_CHR_RWT])
  >> ‘n MOD 10 < 10’ by simp[] >> ‘n MOD 10 + 48 < 256’ by simp[]>>
      simp [stringTheory.ORD_CHR_RWT]>>
  metis_tac [DIVISION, MULT_COMM, DECIDE “0<10”]
QED 


Definition hnlz_def[simp]:
  hnlz s ⇔ (s = "" ∨ HD s ≠ #"0")
End

Theorem hnlz_reverse:
  ∀s. s≠"" ∧ hnlz s ⇒ LAST (REVERSE s) ≠ #"0"
Proof
  simp[hnlz_def, LAST_REVERSE]>>
  simp [Once IMP_DISJ_THM]
QED

Theorem s2iHelper_empty:
  ∀n. string_to_intHelper2 "" = SOME n ⇒ n = 0
Proof
  rw[string_to_intHelper2_def]
QED
  
Theorem s2iHelper_nonzero:
  ∀s n. s≠"" ∧ LAST s ≠ #"0" ∧ string_to_intHelper2 s = SOME n ⇒
        n > 0
Proof
  simp[string_to_intHelper2_def, AllCaseEqs()]>>
  rpt strip_tac>>
  Induct_on ‘s’
  >- simp[]
  >> simp[string_to_intHelper2_def, AllCaseEqs()]>>
  rw[]>>
  Cases_on ‘s’             
  >- (‘n'=0’ by rw[s2iHelper_empty]>>
      simp[]>>‘ORD h ≠ 48’ suffices_by simp[]>> gvs[]>>
      metis_tac [ORD_CHR_RWT, ORD_11, DECIDE “48<256”])
  >> gvs[]
QED     
 
Theorem i2sHelper_inverse:
  ∀s x. LAST s ≠ #"0" ∧ s ≠ "" ∧ string_to_intHelper2 s = SOME x ⇒
        int_to_stringHelper x = s
Proof
  Induct
  >- simp[]      
  >> simp [string_to_intHelper2_def, AllCaseEqs()]>>
  rpt strip_tac>>      
  simp [Once int_to_stringHelper_def]>>
  simp[s2iHelper_nonzero]>>
  Cases_on ‘s=""’
  >- (rw[] >> rw [s2iHelper_empty] >>
      ‘n=0’ by rw[s2iHelper_empty]>>simp[])
  >> ‘LAST s ≠ #"0"’ by metis_tac [LAST_DEF]>>
  ‘n>0’ by metis_tac [s2iHelper_nonzero]>>gvs[]>>rw[]          
  >- (‘(10 * n + ORD h − 48) MOD 10 + 48 = ORD h’ suffices_by simp[char_BIJ]>>
      ‘(10 * n + ORD h − 48) MOD 10 = ORD h - 48’ suffices_by DECIDE_TAC>>
      ‘((10 * n) MOD 10 + (ORD h - 48) MOD 10) MOD 10 = ORD h - 48’ suffices_by simp[MOD_PLUS]>>
      ‘((ORD h - 48) MOD 10) MOD 10 = ORD h - 48’ suffices_by simp[]>>
      ‘(ORD h - 48) MOD 10 = ORD h - 48’ suffices_by simp[MOD_MOD] >> simp[])
  >> ‘(10 * n + ORD h − 48) DIV 10 = n’ suffices_by simp[]>>
  ‘∃r. (10 * n + ORD h − 48) = n*10 + r ∧ r < 10’ suffices_by simp[DIV_UNIQUE]>>
  qexists_tac ‘ORD h - 48’>> simp[]
QED

Theorem reverse_zero:
  ∀s. s≠"" ∧ HD s≠#"0" ⇒ LAST(REVERSE s)≠#"0"
Proof
  rw[]>> ‘LAST (REVERSE s) = HD s’ by simp[LAST_REVERSE]
  >> gvs[]
QED

Theorem i2s_inverse:
  ∀s. hnlz s ∨ s="0" ⇒ (∃n. string_to_int2 s = SOME n ∧ int_to_string n = s) ∨
                       string_to_int2 s = NONE
Proof
  rw [string_to_int2_def]>>
  Cases_on ‘s=""’
  >- gvs[]
  >> Cases_on ‘string_to_intHelper2 (REVERSE s)’
  >- gvs[]
  >> gvs[]>>
  simp [int_to_string_def]>>
  Cases_on ‘HD s = #"0"’
  >- (rw[]>> ‘s="0"’by simp[]>>
      gvs[]>> ‘x = 0’ suffices_by simp[Once int_to_stringHelper_def]>>
      gvs[string_to_intHelper2_def])
  >> gvs[]>>‘LAST (REVERSE s) ≠ #"0"’ by simp[reverse_zero]>>
  ‘REVERSE s ≠ ""’ by simp[]>>
  ‘int_to_stringHelper x = REVERSE s’ by simp[i2sHelper_inverse]>>
  simp[]
QED
        

val _ = export_theory();

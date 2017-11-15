open preamble basis

open astBakeryTheory

val _ = new_theory "baseSemBakery"

val freeprocs_def = Define`
  freeprocs (LTau p)           = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
`;

val sender_def = Define`
  sender (LTau p)           = NONE
∧ sender (LCom p1 v1 p2 v2) = SOME p1
∧ sender (LSel p1 b p2)     = SOME p1
`;

val receiver_def = Define`
  receiver (LTau p)           = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
`;

val _ = export_theory ()

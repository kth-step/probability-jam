open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps;

val _ = new_theory "testReal";

Theorem real_stuff:
 (3.45:real) <= (5.6788:real)
Proof
 EVAL_TAC
QED

Theorem more_real_stuff:
 !(a : real) b c. b - a + (c-b)=c-a
Proof
 REAL_ARITH_TAC
QED

Theorem my_extreal_fact:
 !(r1 : extreal) (r2 : extreal). r1 <= r2 \/ r2 <= r1
Proof
 Cases_on `r1` >> Cases_on `r2` >> rw [extreal_le_def] >>
 REAL_ARITH_TAC
QED

EVAL ``extreal_sup {(1:extreal)}``;

Definition my_extreal_map:
 my_extreal_map (n:num) : extreal = 5
End

Theorem my_extreal_sigma[local]:
 SIGMA my_extreal_map {0;1} = 10
Proof
 (*METIS_TAC [EXTREAL_SUM_IMAGE_THM]*)
 cheat
QED

val _ = export_theory ();

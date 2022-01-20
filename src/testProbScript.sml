open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps lebesgueTheory probabilityTheory;

(* compare real_probabilityTheory, the old theory *)

val _ = new_theory "testProb";

(* 5.1: probability spaces/measures *)

val def_5_1 = prob_space_def;

val def_5_2 = indep_def;

val def_5_3 = random_variable_def;

Definition general_extreal_random_variable:
 general_extreal_random_variable (X:'a -> extreal) p s = random_variable X p s
End

val proper_real_random_variable = real_random_variable_def;

val def_5_4 = indep_rv_def;

val def_5_5 = distribution_def;

val def_5_6 = distribution_function;

val def_5_7 = joint_distribution_def;

(* 5.2: expectation *)

val def_5_8 = expectation_def;

(* E [ X + Y ] = E [ X ] + E [ Y ] *)
Theorem expectation_add:
 !p X Y. 
   prob_space p ==>
   real_random_variable X p ==>
   real_random_variable Y p ==>
   integrable p X ==>
   integrable p Y ==>
   expectation p (\x. X x + Y x) = expectation p X + expectation p Y
Proof
 rw [expectation_def,real_random_variable_def,prob_space_def,integral_add]
QED

(* E [ aX ] = a * E [ X] *)
Theorem expectation_mult:
 !p X a.
  prob_space p ==>
  real_random_variable X p ==>
  integrable p (\x. a * X x) ==>
  expectation p (\x. a * X x) = a * expectation p X
Proof
 rw [expectation_def,real_random_variable_def,prob_space_def] >>
 rw [integrable_from_square] >>
 cheat
QED

val varx2 = variance_eq;

(* 5.4 conditional probabilities *)

val def_5_14 = cond_prob_def;

val _ = export_theory ();


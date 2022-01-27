open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps lebesgueTheory borelTheory probabilityTheory;

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

(* E [ aX ] = a * E [ X ] *)
Theorem expectation_mult:
 !p X a.
  prob_space p ==>
  real_random_variable X p ==>
  integrable p X ==>
  expectation p (\x. Normal a * X x) = Normal a * expectation p X
Proof
 rw [expectation_def,real_random_variable_def,prob_space_def,integral_cmul]
QED

(* VAR [ X ] = E [ X^2 ] - E [ X ]^2  *)
Theorem var_expectation_x2:
 !p X.
  prob_space p ==>
  real_random_variable X p ==> 
  integrable p (\x. X x pow 2) ==>
  variance p X = expectation p (\x. X x pow 2) - expectation p X pow 2
Proof
 rw [variance_eq]
QED

(* 5.4 conditional probabilities *)

val def_5_14 = cond_prob_def;

(* Bernoulli random variables *)

Definition mu:
 mu g pr = (\a. if (a = {x | g x = 1}) then pr else (1 - pr))
End

Definition bernoulli_prob_space:
 bernoulli_prob_space pr g = ({0;1},POW {0;1},mu g pr)
End

Definition bernoulli_random_variable:
 bernoulli_random_variable X pb =
  random_variable X (bernoulli_prob_space pb X) Borel
End

Theorem bernoulli_prob:
 !i X pr.
  bernoulli_random_variable (X i) pr ==>
  prob (bernoulli_prob_space pr (X i)) { x | X i x = 1 } = pr
Proof
 rw [bernoulli_random_variable,bernoulli_prob_space,random_variable_def,prob_def,mu]
QED

Theorem bernoulli_expectation[local]:
 !s i' X pr.
 bernoulli_random_variable (X i') pr ==>
 (!i. i IN s ==> 
  (X i IN measurable (m_space (bernoulli_prob_space pr (X i')),
    measurable_sets (bernoulli_prob_space pr (X i'))) Borel)) ==>
 expectation (bernoulli_prob_space pr (X i')) (\x. SIGMA (\i. X i x) s) = pr * &(CARD s)
Proof
 cheat
QED

val _ = export_theory ();


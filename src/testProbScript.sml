open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps measureTheory lebesgueTheory borelTheory real_borelTheory probabilityTheory;

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
 rw [expectation_def,real_random_variable_def,prob_space_def] >>
 rw [integral_add]
QED

(* E [ c * X ] = c * E [ X ] *)
Theorem expectation_mult:
 !p X c.
  prob_space p ==>
  real_random_variable X p ==>
  integrable p X ==>
  expectation p (\x. Normal c * X x) = Normal c * expectation p X
Proof
 rw [expectation_def,real_random_variable_def,prob_space_def] >>
 rw [integral_cmul]
QED

(* VAR [ X ] = E [ X^2 ] - E [ X ]^2  *)
Theorem var_expectation_x2:
 !p X.
  prob_space p ==>
  real_random_variable X p ==>
  integrable p (\x. X x pow 2) ==>
  variance p X = expectation p (\x. (X x) pow 2) - (expectation p X) pow 2
Proof
 rw [variance_eq]
QED

(* 5.4 conditional probabilities *)

val def_5_14 = cond_prob_def;

(* Bernoulli random variables *)

(* the expectation parameter p is called "pr" *)

Definition bernoulli_mu:
 bernoulli_mu (g : 'a -> extreal) (pr : extreal) : 'a measure =
  (\a. if (a = {x | g x = 1}) then pr else (1 - pr))
End

Definition bernoulli_prob_space:
 bernoulli_prob_space pr g = ({0;1},POW {0;1},bernoulli_mu g pr)
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
 rw [bernoulli_random_variable,bernoulli_prob_space,random_variable_def,prob_def,bernoulli_mu]
QED

Theorem bernoulli_sigma_algebra:
 sigma_algebra ({0; 1},POW {0; 1})
Proof
 rw [sigma_algebra_def,POW_DEF] >-
  (rw [algebra_def,subset_class_def,SUBSET_DEF] >>
   Cases_on `0 IN s` >> fs [] >>
   Cases_on `1 IN s` >> fs []) >>
 fs [SUBSET_DEF] >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_SUM':
 !a f g (s : 'a -> bool). FINITE s /\ sigma_algebra a /\
  (!i. i IN s ==> (f i) IN measurable a Borel) /\
  (!i x. i IN s /\ x IN space a ==> f i x <> NegInf) /\
  (!x. x IN space a ==> (g x = SIGMA (\i. (f i) x) s)) ==>
  g IN measurable a Borel
Proof
 METIS_TAC [IN_MEASURABLE_BOREL_SUM]
QED

Theorem zero_le_neq_NegInf:
 !r. 0 <= r ==> r <> NegInf
Proof
 Cases_on `r` >> Cases_on `0` >> fs [extreal_le_def]
QED

Theorem bernoulli_sigma_borel_measurable:
 !X i' pr s.
  FINITE s ==>
  (!i x. 0 <= X i x) ==>
  (!i. i IN s ==>
   (X i IN measurable (m_space (bernoulli_prob_space pr (X i')),
    measurable_sets (bernoulli_prob_space pr (X i'))) Borel)) ==>
  (\x. SIGMA (\i. X i x) s) IN
    (measurable (m_space (bernoulli_prob_space pr (X i')),
    measurable_sets (bernoulli_prob_space pr (X i'))) Borel)
Proof
 rw [] >>
 MATCH_MP_TAC IN_MEASURABLE_BOREL_SUM' >>
 Q.EXISTS_TAC `X` >>
 Q.EXISTS_TAC `s` >>
 rw [m_space_def,bernoulli_prob_space,bernoulli_sigma_algebra] >>
 METIS_TAC [zero_le_neq_NegInf]
QED

Theorem bernoulli_prob_space_measure_space[local]:
 !g pr.
  pr <> PosInf ==>
  prob_space (bernoulli_prob_space pr g)
Proof
 rw [prob_space_def,measure_space_def,bernoulli_prob_space] >-
 rw [bernoulli_sigma_algebra] >| [
  cheat,
  cheat,
  rw [bernoulli_mu] >>
  cheat
 ]
QED

Theorem bernoulli_integrable[local]:
 !X i' pr s. 
 FINITE s ==>
 (!i x. 0 <= X i x) ==>
 (!i. i IN s ==>
  (X i IN measurable (m_space (bernoulli_prob_space pr (X i')),
    measurable_sets (bernoulli_prob_space pr (X i'))) Borel)) ==>
  integrable (bernoulli_prob_space pr (X i')) (\x. SIGMA (\i. X i x) s)
Proof
 rw [integrable_def] >| [
  rw [bernoulli_sigma_borel_measurable],
  rw [pos_fn_integral_sum] >> cheat,
  cheat
 ]
QED

Theorem bernoulli_expectation[local]:
 !s i' X pr.
 bernoulli_random_variable (X i') pr ==>
 (!i. i IN s ==>
  (X i IN measurable (m_space (bernoulli_prob_space pr (X i')),
    measurable_sets (bernoulli_prob_space pr (X i'))) Borel)) ==>
 expectation (bernoulli_prob_space pr (X i')) (\x. SIGMA (\i. X i x) s) = pr * &CARD s
Proof
 rw [bernoulli_random_variable,m_space_def,expectation_def,bernoulli_prob_space,bernoulli_mu,random_variable_def,p_space_def,events_def] >>
 rw [measure_space_def] >>
 rw [sigma_algebra_def] >>
 rw [integral_def,pos_fn_integral_def] >>
 cheat
QED

val _ = export_theory ();


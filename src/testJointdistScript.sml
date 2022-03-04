open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps measureTheory lebesgueTheory borelTheory probabilityTheory;

val _ = new_theory "testJointdist";

(* first property after Def 5.7 *)

(* ⊢ p_XY (a × b) = p_YX (b × a) *)
Theorem joint_distribution_comm:
  !p X Y a b.
    joint_distribution p X Y (λ(x,y). a x /\ b y)
    = joint_distribution p Y X (λ(y,x). b y /\ a x)
Proof
  PairCases >> rpt strip_tac
  >> fs[joint_distribution_def,PREIMAGE_ALT,combinTheory.o_DEF,AC CONJ_ASSOC CONJ_COMM]
QED

Theorem prob_space_increasing:
  !p. prob_space p ==> increasing p
Proof
  fs[INCREASING_PROB,PROB_INCREASING]
QED

(* second property after Def 5.7 *)
(* ⊢ p_XY (a x b ) \leq p_X a *)
Theorem joint_distribution_leq:
  !p X Y a b. prob_space p
  /\ real_random_variable X p
  /\ real_random_variable Y p
  /\ (a o X) IN events p (* FIXME Reasonable assumptions? *)
  /\ (b o Y) IN events p
  ==>
    joint_distribution p X Y (λ(x,y). a x /\ b y) <= prob p (a o X)
Proof
  rpt strip_tac
  >> fs[joint_distribution_def]
  >> irule PROB_INCREASING
  >> fs[SUBSET_DEF,pairTheory.ELIM_UNCURRY,AC CONJ_ASSOC CONJ_COMM,combinTheory.o_DEF,PREIMAGE_ALT,INTER_DEF]
  >> drule_then (dxrule_all_then assume_tac) EVENTS_INTER
  >> drule_then assume_tac EVENTS_SPACE
  >> dxrule_all EVENTS_INTER
  >> fs[INTER_DEF,AC CONJ_ASSOC CONJ_COMM]
QED

(* third property after Def 5.7 *)
(* ⊢ p_XY (a x b ) \leq p_Y b *)
Theorem joint_distribution_leq:
  !p X Y a b. prob_space p
  /\ real_random_variable X p
  /\ real_random_variable Y p
  /\ (a o X) IN events p (* FIXME Reasonable assumptions? *)
  /\ (b o Y) IN events p
  ==>
    joint_distribution p X Y (λ(x,y). a x /\ b y) <= prob p (b o Y)
Proof
  fs[joint_distribution_leq,Once joint_distribution_comm]
QED

val _ = export_theory ();

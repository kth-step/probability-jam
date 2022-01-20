open HolKernel boolLib Parse bossLib pred_setTheory arithmeticTheory realTheory extrealTheory sigma_algebraTheory RealArith realSimps;

val _ = new_theory "testSigma";

(* the intersection algebra is an algebra *)

Theorem algebra_inter:
  !Ω A B. algebra (Ω,A)
  /\ algebra (Ω,B)
  ==> algebra (Ω, {M| M SUBSET Ω /\ M IN A /\ M IN B })
Proof
  REWRITE_TAC[algebra_def]
  >> rpt strip_tac
  >- fs[subset_class_def]
  >> fs[]
QED

Theorem sigma_algebra_inter:
  !Ω A B. sigma_algebra (Ω,A)
  /\ sigma_algebra (Ω,B)
  ==> sigma_algebra (Ω, {M| M SUBSET Ω /\ M IN A /\ M IN B })
Proof
  rw[sigma_algebra_def,algebra_inter]
  >- (
    rw[BIGUNION,SUBSET_DEF]
    >> drule_then drule $ iffLR SUBSET_DEF
    >> simp[SUBSET_DEF]
  )
  >> first_x_assum irule
  >> fs[SUBSET_DEF]
QED

val _ = export_theory ();

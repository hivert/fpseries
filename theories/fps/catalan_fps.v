(** Combi.catalan_fps : Catalan numbers (classical version) *)
(******************************************************************************)
(*    Copyright (C) 2019-2026 Florent Hivert <florent.hivert@lisn.fr>         *)
(*                                                                            *)
(*    This program is free software; you can redistribute it and/or           *)
(*    modify it under the terms of the GNU Lesser General Public              *)
(*    License as published by the Free Software Foundation; either            *)
(*    version 3 of the License, or (at your option) any later version.        *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*    The full text of the LGPL is available at:                              *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
(** #
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
 # *)
(** * Catalan number via generating functions (classical power series version)

We prove using three different techniques that the Catalan number are equal to
[\frac{\binom{2n, n}}{n+1}] that is in math comp ['C(i.*2, i) %/ i.+1].
Precisely, we suppose that [C : nat -> nat] verify [C 0 = 1] and
[C (n+1) = \sum_{i=0}^n (C i) * (C (n-i))], and prove that [C i] is equal to
the formula above. The only definition here is

- [FC] : {fps rat} == the generating series of the [C i].
*******************************************************************************)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype div bigop ssralg binomial rat ssrnum.
From mathcomp Require Import zify ring lra.

Require Import auxresults fps.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** The generating series of Catalan numbers *)
Section Catalan.

Variable (Cat : nat -> nat).

Hypothesis Cat0 : Cat 0 = 1%N.
Hypothesis CatS :
  forall n : nat, Cat n.+1 = \sum_(i < n.+1) Cat i * Cat (n - i).

Local Definition Catsimpl := (Cat0, CatS, big_ord0, big_ord_recl).
Example Cat1 : Cat 1 = 1.  Proof. by rewrite !Catsimpl. Qed.
Example Cat2 : Cat 2 = 2.  Proof. by rewrite !Catsimpl. Qed.
Example Cat3 : Cat 3 = 5.  Proof. by rewrite !Catsimpl. Qed.
Example Cat4 : Cat 4 = 14. Proof. by rewrite !Catsimpl. Qed.
Example Cat5 : Cat 5 = 42. Proof. by rewrite !Catsimpl. Qed.

Import GRing.Theory.

Local Definition pchar_rat := Num.Theory.pchar_num rat.
Local Definition nat_unit := tfps.TFPSField.nat_unit_field pchar_rat.
Local Definition fact_unit := tfps.TFPSField.fact_unit pchar_rat.
Hint Resolve pchar_rat nat_unit : core.

Section GenSeries.

Local Open Scope ring_scope.
Local Open Scope fps_scope.

Definition FC : {fps rat} := \fps (Cat i)%:R .X^i.

Lemma FC_in_coef0_eq1 : FC \in coefs0_eq1.
Proof. by rewrite coefs0_eq1E coefs_FPSeries Cat0. Qed.

Proposition FC_algebraic_eq : FC = 1 + ''X * FC ^+ 2.
Proof.
rewrite /FC; apply/fpsP => i.
rewrite !(coefs_FPSeries, coefs_simpl).
case: i => [|i]; first by rewrite Cat0 addr0.
rewrite add0r CatS /= expr2 coefsM natr_sum.
apply eq_bigr => [[j /= _]] _.
by rewrite !coefs_FPSeries natrM.
Qed.

End GenSeries.


(** ** Extraction of the coefficient using square root and Newton's formula *)
Section AlgebraicSolution.

Local Open Scope ring_scope.
Local Open Scope fps_scope.

Lemma mulr_nat i (f : {fps rat}) : i%:R *: f = i%:R * f.
Proof. by rewrite scaler_nat -[f *+ i]mulr_natr mulrC. Qed.

Theorem FC_algebraic_solution :
  ''X * FC = 2%:R^-1 *: (1 - \sqrt (1 - 4%:R *: ''X)).
Proof.
have co1 : 1 - 4%:R *: ''X \in @coefs0_eq1 rat.
  by rewrite mulr_nat coefs0_eq1E !coefs_simpl subr0.
have: (2%:R *: ''X * FC - 1) ^+ 2 = 1 - 4%:R *: ''X.
  by rewrite !mulr_nat sqrrB1 {2}FC_algebraic_eq; ring.
move/(sqrtE nat_unit) => /(_ co1) [HeqP | HeqN].
  exfalso; move: HeqP => /(congr1 (fun x => x``_0)).
  rewrite mulr_nat; repeat rewrite ?coefs_simpl -?mulrA ?eqxx /=.
  rewrite (eqP (coefs0_eq1_expr _ _)) => /eqP.
  rewrite sub0r -subr_eq0 -opprD oppr_eq0.
  by rewrite (Num.Theory.pnatr_eq0 _ 2%N).
apply: (scalerI (a := 2)); first by rewrite Num.Theory.pnatr_eq0.
by rewrite scalerA divff // scale1r -HeqN !mulr_nat; ring.
Qed.

Theorem coefFC i : FC``_i = i.*2`!%:R / i`!%:R /i.+1`!%:R.
Proof.
have:= congr1 (fun x => x``_i.+1) FC_algebraic_solution.
rewrite coef_fpsXM ![X in (X = _)]/= => ->.
rewrite !coefs_simpl sub0r -scaleNr coef_expr1cX ?{}Hi //.
rewrite mulrN mulrA -mulNr; congr (_ / (i.+1)`!%:R).
rewrite -[4%N]/(2 * 2)%N mulrnA -mulNrn -[(1 *- 2 *+ 2)]mulr_natl.
rewrite exprMn -mulrA.
have -> : (1 *- 2)^+ i.+1 = \prod_(i0 < i.+1) (1 *- 2) :> rat.
  by rewrite prodr_const /= card_ord.
rewrite -big_split /= big_ord_recl /=.
rewrite subr0 mulNr divrr // mulN1r 2!mulrN [LHS]opprK.
rewrite exprS !mulrA [2%:R^-1 * 2%:R]mulVf // mul1r.
rewrite (eq_bigr (fun j : 'I_i => (2 * j + 1)%:R)) /=; last first.
  by move=> j _; rewrite /bump /=; field.
elim: i => [|i IHi]; first by rewrite expr0 big_ord0 double0 fact0 mulr1.
rewrite big_ord_recr /= exprS -mulrA mulrC mulrA {}IHi.
have factn0 : i`!%:R != 0 :> rat.
  by rewrite !Num.Theory.pnatr_eq0 -lt0n fact_gt0.
have i1n0 : 1 + i%:R != 0 :> rat.
  by rewrite nat1r !Num.Theory.pnatr_eq0 -lt0n.
by rewrite doubleS !factS; rewrite -mul2n; field.
Qed.

Theorem Cat_rat i : (Cat i)%:R = i.*2`!%:R / i`!%:R /i.+1`!%:R :> rat.
Proof. by rewrite -coefFC coefs_FPSeries. Qed.

Local Close Scope ring_scope.

Theorem CatM i : Cat i * i`! * i.+1`! = i.*2`!.
Proof.
have:= Cat_rat i.
move/(congr1 (fun x => x * (i.+1)`!%:R * i`!%:R)%R).
rewrite (divrK (fact_unit i.+1)) (divrK (fact_unit i)) // -!natrM => /eqP.
by rewrite Num.Theory.eqr_nat => /eqP <-; nia.
Qed.

Theorem CatV i : Cat i = i.*2`! %/ (i`! * i.+1`!).
Proof.
have:= CatM i; rewrite -mulnA => /(congr1 (fun j => j %/ (i`! * (i.+1)`!))).
by rewrite mulnK // muln_gt0 !fact_gt0.
Qed.

Theorem CatE i : Cat i = 'C(i.*2, i) %/ i.+1.
Proof.
case: (ltnP 0 i)=> [Hi|]; last first.
  by rewrite leqn0 => /eqP ->; rewrite Cat0 bin0 divn1.
rewrite (CatV i) factS [i.+1 * _]mulnC mulnA.
by rewrite bin_factd ?double_gt0 // -{3}addnn addnK divnMA.
Qed.

End AlgebraicSolution.


(** ** Extraction of the coefficient using Lagrange inversion formula *)
Section LagrangeSolution.

Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Lemma one_plusX_2_unit : ((1 + ''X) ^+ 2 : {fps rat}) \is a GRing.unit.
Proof.
rewrite unit_fpsE coefs0M coefsD coefs1.
by rewrite coef_fpsX addr0 mulr1.
Qed.

Proposition FC_fixpoint_eq : FC - 1 = lagrfix ((1 + ''X) ^+ 2).
Proof.
apply: (lagrfix_uniq one_plusX_2_unit).
rewrite {1}FC_algebraic_eq -addrA addrC subrK.
rewrite rmorphXn rmorphD /= comp_fps1 comp_fpsX //; first by ring.
rewrite coefs0_eq0E coefsB coefs1.
  by rewrite coefs_FPSeries /= Cat0 subrr.
Qed.

Theorem CatM_Lagrange i : (i.+1 * (Cat i))%N = 'C(i.*2, i).
Proof.
case: i => [|i]; first by rewrite Cat0 mul1n bin0.
apply/eqP; rewrite -(Num.Theory.eqr_nat rat); rewrite natrM.
have:= (congr1 (fun s => s``_i.+1) FC_fixpoint_eq).
rewrite !coefs_simpl coefs_FPSeries subr0 /= => ->.
rewrite coefs_lagrfix ?one_plusX_2_unit //.
rewrite -exprM mul2n addrC exprD1n coefs_sum.
have Hord : (i < (i.+1).*2.+1)%N by nia.
rewrite (bigD1 (Ordinal Hord)) //= -!/(_`_i.+1).
rewrite coefsMn coef_fpsXn // eqxx /=.
rewrite big1 ?addr0 => [|[j /= Hj]]; first last.
  rewrite -val_eqE /= => {Hj} /negbTE Hj.
  by rewrite !coefs_simpl eq_sym Hj mul0rn.
rewrite ltnS in Hord.
rewrite -bin_sub // -{2}addnn -addSnnS addnK.
by rewrite mulrA -natrM mul_bin_left -addnn addnK natrM mulrC mulKr.
Qed.

Local Close Scope ring_scope.

Theorem Cat_Lagrange i : Cat i = 'C(i.*2, i) %/ i.+1.
Proof.
by have:= congr1 (fun m => m %/ i.+1) (CatM_Lagrange i); rewrite mulnC mulnK.
Qed.

End LagrangeSolution.


(** ** Extraction of the coefficient using Holonomic differential equation *)
Section HolonomicSolution.

Local Open Scope ring_scope.
Local Open Scope fps_scope.

Proposition FC_differential_eq :
  (1 - ''X *+ 2) * FC + (1 - ''X *+ 4) * ''X * FC^`()%fps = 1.
Proof.
have X2Fu : (1 - ''X *+ 2 * FC) \is a GRing.unit.
  rewrite unit_fpsE coefsB coefs1.
  by rewrite mulrnAl coefsMn coef_fpsXM.
rewrite -mulrA.
have FalgN : ''X * FC ^+ 2 = FC - 1.
  by apply/eqP; rewrite eq_sym subr_eq addrC -FC_algebraic_eq.
have -> : ''X * FC^`()%fps = (FC - 1)/(1 - ''X *+ 2 * FC).
  rewrite -[LHS]divr1; apply/eqP.
  rewrite (eq_divr (''X * _)) ?unitr1 // ?X2Fu // mulr1; apply/eqP.
  have /= := congr1 ((fun s => ''X * s) \o (@deriv_fps _)) FC_algebraic_eq.
  rewrite derivD_fps deriv_fps1 add0r.
  rewrite derivM_fps /= deriv_fpsX mul1r derivX_fps /= expr1.
  rewrite mulrDr FalgN => /eqP; rewrite -(subr_eq _ _ (''X * _)) => /eqP <-.
  by apply/eqP => /=; ring.
rewrite mulrA -[X in X + _](mulrK X2Fu) -mulrDl -[RHS]divr1.
apply/eqP; rewrite eq_divr ?unitr1 //; apply/eqP.
by rewrite !mulr2n; ring: FalgN.
Qed.

Local Close Scope ring_scope.
Local Close Scope tfps_scope.

Proposition Catalan_rec n : n.+2 * Cat (n.+1) = (4 * n + 2) * Cat n.
Proof.
have := congr1 (fun x => (x``_n.+1)%R) FC_differential_eq.
rewrite coefs1 coefsD !mulrDl !mul1r !coefsD.
rewrite -!mulNrn !(mulrnAl, coefsMn, mulNr, coefsN).
rewrite -mulrA !coef_fpsXM /= !coef_deriv_fps !coefs_FPSeries.
case: n => [|n] /=; first by rewrite !Catsimpl.
move: {n} n.+1 => n; move: (Cat n.+1) (Cat n) => Cn1 Cn.
rewrite !mulNrn addrA [X in (X - _)%R]addrC addrA -mulrSr -!mulrnA.
move/eqP; rewrite subr_eq add0r subr_eq -natrD Num.Theory.eqr_nat.
by nia.
Qed.

Theorem CatM_from_rec n : n.+1 * Cat n = 'C(n.*2, n).
Proof.
elim: n => [| n IHn] /=; first by rewrite Cat0 bin0.
rewrite Catalan_rec doubleS !binS.
have leq_n2 : n <= n.*2 by rewrite -addnn leq_addr.
rewrite -[X in _ + _ + X]bin_sub; last exact: (leq_trans leq_n2 (leqnSn _)).
rewrite subSn // -{4}addnn addnK binS addnn.
rewrite addn2 -[4]/(2 * 2) -mulnA !mul2n -doubleS -doubleMl; congr _.*2.
rewrite -IHn -{1}addnn -addnS mulnDl; congr (_ + _).
have:= mul_bin_down n.*2 n.
rewrite mul_bin_diag -{2}addnn addnK -{}IHn mulnA [n * n.+1]mulnC.
rewrite -mulnA ![n.+1 * _]mulnC => /(congr1 (fun m => m %/ n.+1)).
by rewrite !mulnK.
Qed.

Theorem Cat_from_rec i : Cat i = 'C(i.*2, i) %/ i.+1.
Proof.
by have:= congr1 (divn^~ i.+1) (CatM_from_rec i); rewrite mulnC mulnK.
Qed.

End HolonomicSolution.

End Catalan.

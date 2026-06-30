(** Direct limits *)
(******************************************************************************)
(*       Copyright (C) 2021 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
(** * Direct limits in a constructive setting

In the following we use the following notation:

-   I : dirType d == a directed type
- Obj : I -> Type == a map associating to each i of type I an object of
                       some category
-   bonding le_ij == a morphism Obj i -> Obj j where (le_ij : i <= j)

We define the following notion and notations:

is_dirsys bonding == a type for proofs that the bonding morphisms define
                     a proper direct system.
     cocone Sys C == C : forall i, Obj i -> T is a co-cone to T for the
                     system Sys
      'inj[dlT]_i == the morphim from Obj i -> dlT where dlT is a
                     direct limit
'inj[dlT], 'inj_i, 'inj == idem inferring dlT or/and i from the context
      'ind[dlT] C == the morphism dlT -> T induced by the universal
                     property where C : cocone Sys C is a cocone to T
           'ind C == idem where dlT is inferred from the context
dsysequal Sys u v == u and v maps to the same element in the limit.
                     u and v are dependant pairs of type {i & Obj i}.
                     This is an intensional predicate (in Prop).

This file defines the following algebraic structures:

         dirLimType Sys == direct limits of sets (Type)
                           The HB class is called DirLim
     nmodDirLimType Sys == direct limits of N-modules
                           The HB class is called NmoduleDirLim
     zmodDirLimType Sys == direct limits of Z-modules
                           The HB class is called ZmoduleDirLim
pzSemiRingDirLimType Sys == direct limits of semi rings
                           The HB class is called PzSemiRingDirLim
nzSemiRingDirLimType Sys == direct limits of non trivial semi rings
                           The HB class is called NzSemiRingDirLim
   pzRingDirLimType Sys == direct limits of rings
                           The HB class is called PzRingDirLim
   nzRingDirLimType Sys == direct limits of non trivial rings
                           The HB class is called NzRingDirLim
comPzSemiRingDirLimType Sys == direct limits of commutative semi rings
                           The HB class is called ComPzSemiRingDirLim
comNzSemiRingDirLimType Sys == direct limits of commutative, non trivial
                           semi rings
                           The HB class is called ComNzSemiRingDirLim
comPzRingDirLimType Sys == direct limits of commutative rings
                           The HB class is called ComPzRingDirLim
comNzRingDirLimType Sys == direct limits of commutative, non trivial rings
                           The HB class is called ComNzRingDirLim
 unitRingDirLimType Sys == direct limits of rings with computable units
                           The HB class is called UnitRingDirLim
comUnitRingDirLimType Sys == direct limits of commutative rings with
                           computable units
                           The HB class is called ComUnitRingDirLim
  idomainDirLimType Sys == direct limits of integral, commutative ring
                           The HB class is called IDomainDirLim
    fieldDirLimType Sys == direct limits of fields
                           The HB class is called FieldDirLim
 lSemiModDirLimType Sys == direct limits of left semimodules. The base
                           ring is inferred from the system Sys.
                           The HB class is called LSemiModuleDirLim
     lmodDirLimType Sys == direct limits of left modules
                           The HB class is called LmoduleDirLim
 lSemiAlgDirLimType Sys == direct limits of left semi-algebras
                           The HB class is called LSemiAlgebraDirLim
     lalgDirLimType Sys == direct limits of left algebras
                           The HB class is called LalgebraDirLim
  semiAlgDirLimType Sys == direct limits of semi-algebras
                           The HB class is called SemiAlgebraDirLim
      algDirLimType Sys == direct limits of algebras
                           The HB class is called AlgebraDirLim
comSemiAlgDirLimType Sys == direct limits of commutative semi-algebras
                           The HB class is called ComSemiAlgebraDirLim
   comAlgDirLimType Sys == direct limits of commutative algebras
                           The HB class is called ComAlgebraDirLim
  unitAlgDirLimType Sys == direct limits of algebras with computable units
                           The HB class is called UnitAlgebraDirLim
comUnitAlgDirLimType Sys == direct limits of commutative algebras with
                           computable units
                           The HB class is called ComUnitAlgebraDirLim
*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot order ssralg.

Require Import natbar directed.


Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'dirlim' S }" (at level 0, format "{ 'dirlim'  S }").
Reserved Notation "''inj_' i" (at level 0, i at level 2, format "''inj_' i").
Reserved Notation "''inj[' T ']'" (at level 0).
Reserved Notation "''inj[' T ']_' i" (at level 0, i at level 2).
Reserved Notation "''ind[' T ']'" (at level 0).



(***************************************************************************)
(** Direct systems and direct limits                                       *)
(*                                                                         *)
(***************************************************************************)
Section DirectSystem.

Variables (disp : _) (I : dirType disp).

(** Objects and bonding morphisms of the direct system at left outside     *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Record is_dirsys : Prop := IsDirSys {
      _ : I;
      dirsys_id i (Hii : i <= i) : (bonding Hii) =1 id;
      dirsys_comp i j k  (Hij : i <= j) (Hjk : j <= k) :
          (bonding Hjk) \o (bonding Hij) =1 (bonding (le_trans Hij Hjk));
  }.

Lemma dirsys_inh : is_dirsys -> I.
Proof.
move=> Sys; have ex : exists i : I, true by case: Sys.
exact: (xchoose ex).
Qed.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {dirlim S} and to get the inhabitant of I.                    *)
Definition cocone of is_dirsys :=
  fun T (mors : forall i, Obj i -> T) =>
    forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

Lemma bondingE (Sys : is_dirsys) i j (Hij1 Hij2 : i <= j) :
  bonding Hij1 =1 bonding Hij2.
Proof. by rewrite (bool_irrelevance Hij1 Hij2). Qed.

Lemma bonding_transE (Sys : is_dirsys) i j k (Hij : i <= j) (Hjk : j <= k) u :
  (bonding Hjk) (bonding Hij u) = bonding (le_trans Hij Hjk) u.
Proof. by move/dirsys_comp : Sys; apply. Qed.

Lemma coconeE Sys T (mors : forall i, Obj i -> T) :
  cocone Sys mors ->
    forall i j (Hij : i <= j) u, mors j (bonding Hij u) = mors i u.
Proof. by rewrite /cocone => H i j le_ij u; rewrite -(H i j le_ij). Qed.


Implicit Types (i j k : I) (u v : {i : I & Obj i}).

Inductive dsysequal (Sys : is_dirsys) u v : Prop :=
  | Dsysequal : forall k (le_ik : projT1 u <= k) (le_jk : projT1 v <= k),
    (bonding le_ik (projT2 u) = bonding le_jk (projT2 v)) -> dsysequal Sys u v.

Local Arguments Dsysequal {Sys u v k} (le_ik le_jk).

Variable Sys : is_dirsys.

Lemma dsysequal_bonding i j (le_ij : i <= j) (u : Obj i) :
  dsysequal Sys (existT Obj i u) (existT Obj j (bonding le_ij u)).
Proof.
apply: (Dsysequal (k := j)) => /=.
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dsysequal_refl u : dsysequal Sys u u.
Proof. exact: (Dsysequal (k := projT1 u)). Qed.
Lemma dsysequal_sym_impl u v : dsysequal Sys u v -> dsysequal Sys v u.
Proof.
move=> [k le_ik le_jk Hbond].
by apply: (Dsysequal le_jk le_ik); rewrite Hbond.
Qed.
Lemma dsysequal_sym u v : dsysequal Sys u v <-> dsysequal Sys v u.
Proof. by split; apply: dsysequal_sym_impl. Qed.
Lemma dsysequal_trans v u w :
  dsysequal Sys u v -> dsysequal Sys v w -> dsysequal Sys u w.
Proof.
move=> [l le_il le_jl Huv].
move=> [m le_jm le_km Hvw].
have [n le_ln le_mn] := directedP l m.
apply: (Dsysequal (le_trans le_il le_ln) (le_trans le_km le_mn)).
rewrite -!bonding_transE // {}Huv -{}Hvw !bonding_transE //.
exact: bondingE.
Qed.

Section Compatibility.

Variables (T : Type) (f : forall i, Obj i -> T).
Hypothesis Hcone : cocone Sys f.

Lemma dsysequalE i j (u : Obj i) (v : Obj j) :
  dsysequal Sys (existT Obj i u) (existT Obj j v) -> f u = f v.
Proof.
move=> [k le_ik le_jk Hbond].
by rewrite -(coconeE Hcone le_ik) Hbond (coconeE Hcone).
Qed.

End Compatibility.

End DirectSystem.


(***************************************************************************)
(** Interface for direct limits                                            *)
(*                                                                         *)
(***************************************************************************)
Open Scope ring_scope.


#[key="dlT"]
HB.mixin Record isDirLim
    disp (I : dirType disp)
    (Obj : I -> Type) (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  dlT of Choice dlT := {
    dirlim_inj i : Obj i -> dlT;
    dirlim_ind T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) : dlT -> T;
    dirlim_eq i (u : Obj i) j (v : Obj j) :
      dirlim_inj i u = dirlim_inj j v ->
      exists k (leik : i <= k) (lejk : j <= k),
        bonding i k leik u = bonding j k lejk v;
    dirlim_surj (x : dlT) : exists i (u : Obj i), dirlim_inj i u = x;
    dlinjP : cocone Sys dirlim_inj;
    dlind_commute T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) :
      forall i, dirlim_ind T f Hcone \o dirlim_inj i =1 f i;
    dlind_uniq T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) :
      forall (ind : dlT -> T),
        (forall i, ind \o dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind T f Hcone
  }.

#[short(type="dirLimType")]
HB.structure Definition DirLim
    disp (I : dirType disp)
    (Obj : I -> Type) (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  := {
    dlT of isDirLim disp I Obj bonding Sys dlT
    & Choice dlT
  }.



Section InternalTheory.

Variables (disp : _) (I : dirType disp).
Variables Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.

Local Notation "''inj'" := (dirlim_inj (s := dlT)).
Local Notation "''inj_' i" := (dirlim_inj (s := dlT) i).
Local Notation "''ind'" := (dirlim_ind (s := dlT) _ _).

Lemma dlinjE :
  forall i j, forall (Hij : i <= j) u, 'inj_j (bonding Hij u) = 'inj_i u.
Proof. by move=> i j Hij u; rewrite [LHS]dlinjP. Qed.

Lemma injindE  T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) i u :
  'ind Hcone ('inj_ i u) = f i u.
Proof. exact: dlind_commute. Qed.

End InternalTheory.

Arguments dlinjP {disp I Obj bonding} [Sys].

Notation "''inj[' dlT ']_' i" := (dirlim_inj (s := dlT) i) (only parsing).
Notation "''inj[' dlT ']'" := ('inj[dlT]_ _)  (only parsing).
Notation "''inj_' i" := ('inj[ _ ]_ i).
Notation "''inj'" := ('inj[ _ ]_ _).
Notation "''ind[' T ']'" := (dirlim_ind (s := T) _ _)  (only parsing).
Notation "''ind'" := ('ind[ _ ]).


Section DirLimDirected.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Inductive dirlim_spec x : Prop :=
  | DirLimSpec : forall k (u : Obj k), 'inj u = x -> dirlim_spec x.

Inductive dirlim2_spec x y : Prop :=
  | DirLim2Spec :
    forall k (u v : Obj k), 'inj u = x -> 'inj v = y
                            -> dirlim2_spec x y.
Inductive dirlim3_spec x y z : Prop :=
  | DirLim3Spec :
    forall k (u v w : Obj k), 'inj u = x -> 'inj v = y -> 'inj w = z
                              -> dirlim3_spec x y z.
Lemma dirlimSP x : { p : {i & Obj i} | 'inj (projT2 p) = x }.
Proof.
suff : { p : {i & Obj i} | 'inj (projT2 p) == x }.
  by move=> [p /eqP Heq]; exists p.
apply: sigW => /=; have [i[u] <-{x}]:= dirlim_surj x.
by exists (existT Obj i u).
Qed.
Lemma dirlimS2P x y :
  { p : {i & (Obj i * Obj i)%type} |
    'inj (projT2 p).1 = x /\ 'inj (projT2 p).2 = y }.
Proof.
have [[iu u /= <-{x}]] := dirlimSP x.
have [[iv v /= <-{y}]] := dirlimSP y.
have [n le_ian le_ibn] := directedP iu iv.
by exists (existT _ n (bonding le_ian u, bonding le_ibn v)); rewrite !dlinjE.
Qed.

Lemma dirlimP x : dirlim_spec x.
Proof. by have [[i u] /= <-{x}] := dirlimSP x; exists i u. Qed.
Lemma dirlim2P x y : dirlim2_spec x y.
Proof. by have [[i [u v]/= [<-{x} <-{y}]]] := dirlimS2P x y; exists i u v. Qed.
Lemma dirlim3P x y z : dirlim3_spec x y z.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
have [j w <-{z}] := dirlimP z.
have [n le_in le_jn] := directedP i j.
by exists n (bonding le_in u) (bonding le_in v) (bonding le_jn w);
  rewrite dlinjE.
Qed.

End DirLimDirected.


Section Is_DirsysCongr.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Lemma dirlimE i j (u : Obj i) (v : Obj j) : reflect
    (dsysequal Sys (existT Obj i u) (existT Obj j v))
    ('inj[dlT] u == 'inj[dlT] v).
Proof.
apply (iffP eqP).
  by move/(dirlim_eq i u j v) => [k] [ik] [jk] Heq; exists k ik jk.
move=> [k le_ik le_jk /= Heq].
by rewrite -(coconeE (dlinjP dlT) le_ik) -(coconeE (dlinjP dlT) le_jk) Heq.
Qed.

Lemma dirlim_is_inj :
  (forall i, injective 'inj[dlT]_i)
  <->
  (forall i j (le_ij : i <= j), injective (bonding le_ij)).
Proof.
split => Hinj.
- move=> i j le_ij u v /(congr1 'inj[dlT]).
  by rewrite !dlinjE; apply: Hinj.
- move=> i u v /eqP/dirlimE [k /= le_ik le_ik1].
  by rewrite (bondingE Sys) /=; apply Hinj.
Qed.

End Is_DirsysCongr.
Arguments Dsysequal {disp I Obj bonding Sys u v k} (le_ik le_jk).
Arguments dsysequal {disp I Obj bonding} (Sys) (u v).


(****************************************************************************)
(**  Interface for direct limits in various algebraic categories            *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

#[key="dlT"]
HB.mixin Record isNmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (dlT : Type) of DirLim disp Sys dlT & GRing.Nmodule dlT := {
  dlinj_is_nmod_morphism :
    forall i, nmod_morphism ('inj[dlT]_i)
  }.
#[short(type="nmodDirLimType")]
HB.structure Definition NmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of DirLim disp Sys dlT
    & isNmoduleDirLim disp I Obj bonding Sys dlT
    & GRing.Nmodule dlT
  }.

Section NmoduleDirLimTheory.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> nmodType.
Variable bonding : forall i j, i <= j -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : nmodDirLimType Sys.
Implicit Type x y : dlT.

HB.instance Definition _ i :=
  GRing.isNmodMorphism.Build (Obj i) dlT _ (dlinj_is_nmod_morphism i).

(** The universal induced map is a N-module morphism *)
Section UniversalProperty.

Variable (T : nmodType) (f : forall i, {additive Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_nmod_morphism : nmod_morphism ('ind[dlT] Hcone).
Proof.
split => [| /= x y].
  have <- : 'inj[dlT]_(dirsys_inh Sys) 0 = 0 by rewrite raddf0.
  by rewrite injindE raddf0.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -raddfD /= !injindE raddfD.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build dlT T _ dlind_is_nmod_morphism.

End UniversalProperty.

Lemma dl0E i : 'inj[dlT]_i 0 = 0.
Proof. by rewrite !raddf0. Qed.

Lemma dlinj_eq0 i (u : Obj i) :
  'inj[dlT]_i u = 0 -> exists j (leij : i <= j), bonding leij u = 0.
Proof.
rewrite -(dl0E i) => /eqP/dirlimE [k lejk leik Heq].
by exists k; exists lejk; rewrite Heq raddf0.
Qed.

End NmoduleDirLimTheory.


#[short(type="zmodDirLimType")]
HB.structure Definition ZmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmoduleDirLim disp Sys dlT
    & GRing.Zmodule dlT
  }.

Section ZmoduleDirLimTheory.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : zmodDirLimType Sys.
Implicit Type x y : dlT.


(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_zmod_morphism : zmod_morphism ('ind[dlT] Hcone).
Proof.
move=> /= x y; have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -raddfB /=.
Qed.

End UniversalProperty.

End ZmoduleDirLimTheory.


#[key="dlT"]
HB.mixin Record isPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (dlT : Type) of DirLim disp Sys dlT & GRing.PzSemiRing dlT := {
  dlinj_is_monoid_morphism :
    forall i, monoid_morphism ('inj[dlT]_i)
  }.
#[short(type="pzSemiRingDirLimType")]
HB.structure Definition PzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmoduleDirLim disp Sys dlT
    & isPzSemiRingDirLim disp I Obj bonding Sys dlT
    & GRing.PzSemiRing dlT
  }.

Section PzSemiRingDirLimTheory.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> pzSemiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : pzSemiRingDirLimType Sys.
Implicit Type x y : dlT.

HB.instance Definition _ i :=
  GRing.isMonoidMorphism.Build (Obj i) dlT _ (dlinj_is_monoid_morphism i).

(** The universal induced map is a semi-ring morphism *)
Section UniversalProperty.

Variable (T : pzSemiRingType) (f : forall i, {rmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_monoid_morphism : monoid_morphism ('ind[dlT] Hcone).
Proof.
split=> /= [|x y].
- have <- : 'inj[dlT]_(dirsys_inh Sys) 1 = 1 by exact: rmorph1.
  by rewrite injindE rmorph1.
- have [i u v <-{x} <-{y}] := dirlim2P x y.
  by rewrite -rmorphM /= !injindE rmorphM.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build dlT T _ dlind_is_monoid_morphism.

End UniversalProperty.

Lemma dl1E i : 'inj[dlT]_i 1 = 1.
Proof. by rewrite !rmorph1. Qed.

Lemma dlinj_eq1 i (u : Obj i) :
  'inj[dlT]_i u = 1 -> exists j (leij : i <= j), bonding leij u = 1.
Proof.
rewrite -(dl1E i) => /eqP/dirlimE [k lejk leik Heq].
by exists k; exists lejk; rewrite Heq rmorph1.
Qed.

End PzSemiRingDirLimTheory.


#[short(type="nzSemiRingDirLimType")]
HB.structure Definition NzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmoduleDirLim disp Sys dlT
    & isPzSemiRingDirLim disp I Obj bonding Sys dlT
    & GRing.NzSemiRing dlT
  }.


#[short(type="pzRingDirLimType")]
HB.structure Definition PzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of PzSemiRingDirLim disp Sys dlT
    & GRing.PzRing dlT
  }.


#[short(type="nzRingDirLimType")]
HB.structure Definition NzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NzSemiRingDirLim disp Sys dlT
    & GRing.NzRing dlT
  }.


#[short(type="comPzSemiRingDirLimType")]
HB.structure Definition ComPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComPzSemiRing dlT
    & PzSemiRingDirLim disp Sys dlT
  }.


#[short(type="comNzSemiRingDirLimType")]
HB.structure Definition ComNzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComNzSemiRing dlT
    & NzSemiRingDirLim disp Sys dlT
  }.


#[short(type="comPzRingDirLimType")]
HB.structure Definition ComPzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComPzRing dlT
    & PzRingDirLim disp Sys dlT
  }.


#[short(type="comNzRingDirLimType")]
HB.structure Definition ComNzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComNzRing dlT
    & NzRingDirLim disp Sys dlT
  }.


#[short(type="unitRingDirLimType")]
HB.structure Definition UnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.UnitRing dlT
    & NzRingDirLim disp Sys dlT
  }.

Section DirLimUnitRingTheory.

Variables
    (disp : _) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding).
Variable dlT : unitRingDirLimType Sys.
Implicit Type (x y z : dlT).

(** Cocone limit morphism send units to units *)
Lemma dlunitP (x : dlT) :
  reflect
    (exists i (u : Obj i), 'inj u = x /\ u \is a GRing.unit)
    (x \is a GRing.unit).
Proof.
apply (iffP idP) => [/unitrP [xinv][] | [i][u [<-{x} uunit]]]; first last.
  exact: (rmorph_unit _ uunit).
have [i u v <-{xinv} <-{x}] := dirlim2P x xinv; rewrite -!rmorphM /=.
move=> /dlinj_eq1 [j][leij]; rewrite rmorphM => vu1.
move=> /dlinj_eq1 [k][leik]; rewrite rmorphM => uv1.
have [n lejn lekn] := directedP j k.
exists n; exists (bonding (le_trans leij lejn) u).
split; first by rewrite dlinjE.
apply/unitrP; exists (bonding (le_trans leij lejn) v).
rewrite -!(bonding_transE Sys leij lejn).
split; first by rewrite -rmorphM {}vu1 rmorph1.
rewrite !(bonding_transE Sys leij lejn).
rewrite !(bondingE Sys _ (le_trans leik lekn)).
rewrite -!(bonding_transE Sys leik lekn).
by rewrite -rmorphM {}uv1 rmorph1.
Qed.

End  DirLimUnitRingTheory.


#[short(type="comUnitRingDirLimType")]
HB.structure Definition ComUnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComUnitRing dlT
    & NzRingDirLim disp Sys dlT
  }.


#[short(type="idomainDirLimType")]
HB.structure Definition IDomainDirLim
    disp (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NzSemiRingDirLim disp Sys dlT
    & GRing.IntegralDomain dlT
  }.


#[short(type="fieldDirLimType")]
HB.structure Definition FieldDirLim
    disp (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NzSemiRingDirLim disp Sys dlT
    & GRing.Field dlT
  }.


#[key="dlT"]
HB.mixin Record isLSemiModuleDirLim
    (R : pzSemiRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiModType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (dlT : Type) of DirLim disp Sys dlT & GRing.LSemiModule R dlT := {
  dlinj_is_semilinear :
    forall i, semilinear ('inj[dlT]_i)
  }.
#[short(type="lSemiModDirLimType")]
HB.structure Definition LSemiModuleDirLim
    (R : pzSemiRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiModType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmoduleDirLim _ Sys dlT
    & isLSemiModuleDirLim R disp I Obj bonding Sys dlT
    & GRing.LSemiModule R dlT
  }.

Section LSemiModuleDirLimTheory.

Variable (R : pzRingType).
Variables (disp : _) (I : dirType disp).
Variable Obj : I -> lSemiModType R.
Variable bonding : forall i j, i <= j -> {linear Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : lSemiModDirLimType Sys.

HB.instance Definition _ i :=
  GRing.isSemilinear.Build R (Obj i) dlT _ _ (dlinj_is_semilinear i).

(** The universal induced map is a L-semi-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_semilinear : semilinear ('ind Hcone : dlT -> T).
Proof.
split => [t x | x y].
  have [/= i u <-{x}] := dirlimP x.
  by rewrite -linearZ /= !injindE linearZ.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -linearD /= !injindE linearD.
Qed.
HB.instance Definition _ :=
  GRing.isSemilinear.Build R dlT T _ _ (dlind_is_semilinear).

End UniversalProperty.
End LSemiModuleDirLimTheory.


#[short(type="lmodDirLimType")]
HB.structure Definition LmoduleDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of ZmoduleDirLim _ Sys dlT
    & isLSemiModuleDirLim R disp I Obj bonding Sys dlT
    & GRing.Lmodule R dlT
  }.


#[short(type="lSemiAlgDirLimType")]
HB.structure Definition LSemiAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.LSemiAlgebra R dlT
    & NzSemiRingDirLim _ Sys dlT
    & LSemiModuleDirLim _ Sys dlT
  }.

Section LSemiAlgebraDirLimTheory.

Variable (R : pzRingType).
Variables (disp : _) (I : dirType disp).
Variable Obj : I -> lSemiAlgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : lSemiAlgDirLimType Sys.

(* Rebuilt the various instances on a lalgtype. *)
HB.instance Definition _ i := GRing.Linear.on 'inj[dlT]_i.
(* Check fun i => 'inj[dlT]_i : {lrmorphism Obj i -> dlT}. *)

(** The universal induced map is a L-semi-algebra morphism *)
Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

(* Rebuild the various instances on a lalgtype. *)
HB.instance Definition _ i := GRing.Linear.on ('ind[dlT] Hcone).
(* Check 'ind[dlT] Hcone : {lrmorphism T -> dlT}. *)

End UniversalProperty.
End LSemiAlgebraDirLimTheory.


#[short(type="lalgDirLimType")]
HB.structure Definition LalgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.Lalgebra R dlT
    & PzRingDirLim _ Sys dlT
    & LmoduleDirLim _ Sys dlT
  }.


#[short(type="semiAlgDirLimType")]
HB.structure Definition SemiAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> semiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.SemiAlgebra R dlT
    & PzSemiRingDirLim _ Sys dlT
    & LSemiModuleDirLim _ Sys dlT
  }.


#[short(type="algDirLimType")]
HB.structure Definition AlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.Algebra R dlT
    & PzRingDirLim _ Sys dlT
    & LmoduleDirLim _ Sys dlT
  }.


#[short(type="comSemiAlgDirLimType")]
HB.structure Definition ComSemiAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> comSemiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComSemiAlgebra R dlT
    & SemiAlgebraDirLim R Sys dlT
  }.


#[short(type="comAlgDirLimType")]
HB.structure Definition ComAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> comAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComAlgebra R dlT
    & AlgebraDirLim R Sys dlT
  }.


#[short(type="unitAlgDirLimType")]
HB.structure Definition UnitAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> unitAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.UnitAlgebra R dlT
    & AlgebraDirLim R Sys dlT
  }.


#[short(type="comUnitAlgDirLimType")]
HB.structure Definition ComUnitAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> comUnitAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of GRing.ComUnitAlgebra R dlT
    & ComAlgebraDirLim R Sys dlT
    & UnitAlgebraDirLim R Sys dlT
  }.


(****************************************************************************)
(** Canonical structures for direct limits in various algebraic categories  *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

HB.factory Record DirLim_isNmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isNmoduleDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Definition dlzero  : dlT := 'inj[dlT]_(dirsys_inh Sys) 0.
Definition dladd x y : dlT :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[dlT] (a + b).

Local Lemma dlzeroE i : dlzero = 'inj[dlT]_i 0.
Proof.
rewrite /dlzero; apply/eqP/dirlimE.
have [j le_j le_ij] := directedP (dirsys_inh Sys) i.
by exists j le_j le_ij; rewrite !raddf0.
Qed.
Lemma dladdE i (u v : Obj i) :
  dladd ('inj u) ('inj v) = 'inj (u + v).
Proof.
rewrite /dladd /=; case: dirlimS2P => [[j [x y]]] /= [].
move/eqP/dirlimE => [k /= le_jk le_ik Hux].
move/eqP/dirlimE => [l /= le_jl le_il Hvy].
apply/eqP/dirlimE; have [m le_km le_lm] := directedP k l.
exists m (le_trans le_jk le_km) (le_trans le_ik le_km).
rewrite !raddfD; congr (_ + _); first by rewrite -!(bonding_transE Sys) Hux.
rewrite (bondingE Sys _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvy (bonding_transE Sys).
exact: (bondingE Sys).
Qed.

Fact dladdA : associative dladd.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dladdE addrA.
Qed.
Fact dladdC : commutative dladd.
Proof.
move=> x y; have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite !dladdE addrC.
Qed.
Fact dladd0r : left_id dlzero dladd.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite (dlzeroE i) dladdE add0r.
Qed.
HB.instance Definition _ :=
    GRing.isNmodule.Build dlT dladdA dladdC dladd0r.

Fact dlinj_is_nmod_morphism i : nmod_morphism 'inj[dlT]_i.
Proof.
split; first by rewrite -dlzeroE.
by move=> u v; rewrite {2}/GRing.add /= dladdE.
Qed.
HB.instance Definition _ :=
  isNmoduleDirLim.Build _ _ _ _ _ dlT dlinj_is_nmod_morphism.
HB.end.


HB.factory Record NmoduleDirLim_isZmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim_isZmoduleDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Definition dlopp x : dlT :=
  let: existT i a := projT1 (dirlimSP x) in 'inj[dlT] (- a).
Lemma dloppE i (u : Obj i) : dlopp ('inj u) = 'inj (-u).
Proof.
rewrite /dlopp /=; case: dirlimSP => [[j v]] /= /eqP/dirlimE [k lejk leik].
move/(congr1 (fun u => 'inj[dlT](-u))).
by rewrite -!raddfN !dlinjE.
Qed.
Fact dladdNr : left_inverse 0 dlopp +%R.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite dloppE -raddfD /= addNr raddf0.
Qed.
HB.instance Definition _ :=
    GRing.Nmodule_isZmodule.Build dlT dladdNr.

Fact dlinj_is_zmod_morphism i : zmod_morphism 'inj[dlT]_i.
Proof.
by move=> u v; rewrite {2}/GRing.opp /= dloppE raddfD /=.
Qed.
HB.end.


HB.factory Record DirLim_isZmoduleDirLim
    disp (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isZmoduleDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isNmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isZmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record NmoduleDirLim_isPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim_isPzSemiRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Definition dlone : dlT := 'inj[dlT]_(dirsys_inh Sys) 1.
Definition dlmul x y : dlT :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[dlT] (a * b).

Lemma dloneE i : dlone = 'inj[dlT]_i 1.
Proof.
rewrite /dlone; apply/eqP/dirlimE.
have [j le_j le_ij] := directedP (dirsys_inh Sys) i.
by exists j le_j le_ij; rewrite /= !rmorph1.
Qed.
Lemma dlmulE i (u v : Obj i) :
  dlmul ('inj u) ('inj v) = 'inj (u * v).
Proof.
rewrite /dlmul /=; case: dirlimS2P => [[j [a b]]] /= [].
move/eqP/dirlimE => [k /= le_jk le_ik Hua].
move/eqP/dirlimE => [l /= le_jl le_il Hvb].
apply/eqP/dirlimE; have [m le_km le_lm] := directedP k l.
exists m (le_trans le_jk le_km) (le_trans le_ik le_km).
rewrite /= !rmorphM; congr (_ * _); first by rewrite -!(bonding_transE Sys) Hua.
rewrite (bondingE Sys _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvb (bonding_transE Sys).
exact: (bondingE Sys).
Qed.

Fact dlmulA : associative dlmul.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE mulrA.
Qed.
Fact dlmul1r : left_id dlone dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite (dloneE i) !dlmulE mul1r.
Qed.
Fact dlmulr1 : right_id dlone dlmul.
Proof.
move=> a; have [i x <-{a}] := dirlimP a.
by rewrite (dloneE i) !dlmulE mulr1.
Qed.
Fact dlmulDl : left_distributive dlmul +%R.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE -!raddfD /= -mulrDl dlmulE.
Qed.
Fact dlmulDr : right_distributive dlmul +%R.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE -!raddfD /= -mulrDr dlmulE.
Qed.
Fact dlmul0r : left_zero 0 dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite -(raddf0 'inj[dlT]_i) dlmulE mul0r.
Qed.
Fact dlmulr0 : right_zero 0 dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite -(raddf0 'inj[dlT]_i) dlmulE mulr0.
Qed.
HB.instance Definition _ :=
  GRing.Nmodule_isPzSemiRing.Build dlT
    dlmulA dlmul1r dlmulr1 dlmulDl dlmulDr dlmul0r dlmulr0.
Fact dlinj_is_monoid_morphism i : monoid_morphism 'inj[dlT]_i.
Proof.
split => [|u v].
- by rewrite {2}/GRing.one /= (dloneE i).
- by rewrite {2}/GRing.mul /= dlmulE.
Qed.
HB.instance Definition _ :=
  isPzSemiRingDirLim.Build _ _ _ _ _ dlT dlinj_is_monoid_morphism.
HB.end.


HB.factory Record PzSemiRingDirLim_isNzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> nzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim_isNzSemiRingDirLim _ _ _ _ Sys dlT.

Fact dl1_neq0 : 1 != 0 :> dlT.
Proof.
apply/negP => /eqP.
rewrite -(dl1E dlT (dirsys_inh Sys)).
move => /dlinj_eq0 [i] [le_j].
by rewrite [_ 1]rmorph1=> /eqP; rewrite oner_eq0.
Qed.
HB.instance Definition _ :=
  GRing.PzSemiRing_isNonZero.Build dlT dl1_neq0.
HB.end.


HB.factory Record DirLim_isPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> pzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isPzSemiRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isNmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isNzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> nzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isNzSemiRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isNmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isNzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record PzSemiRingDirLim_isPzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> pzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim_isPzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isZmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record NzSemiRingDirLim_isNzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzSemiRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> nzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzSemiRingDirLim_isNzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isZmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isPzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> pzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> pzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isPzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isPzRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isNzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> nzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> nzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isNzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isNzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NzSemiRingDirLim_isNzRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record PzSemiRingDirLim_isComPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comPzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzSemiRingDirLim_isComPzSemiRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Fact dlmulC x y : x * y = y * x.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -!rmorphM mulrC.
Qed.
HB.instance Definition _ :=
  GRing.PzSemiRing_hasCommutativeMul.Build dlT dlmulC.
HB.end.


HB.factory Record NzSemiRingDirLim_isComNzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzSemiRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comNzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzSemiRingDirLim_isComNzSemiRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isComPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isComPzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comPzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComPzSemiRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isComPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isComNzSemiRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comNzSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComNzSemiRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isComPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isNzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record PzRingDirLim_isComPzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comPzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of PzRingDirLim_isComPzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isComPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record NzRingDirLim_isComNzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comNzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzRingDirLim_isComNzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NzSemiRingDirLim_isComNzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isComPzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comPzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comPzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComPzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isPzRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzRingDirLim_isComPzRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isComNzRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comNzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comNzRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComNzRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isNzRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NzRingDirLim_isComNzRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record NzRingDirLim_isUnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzRingDirLim _ Sys dlT := {
    dlunit : dlT -> bool;
    dlunit_decP x : reflect
      (exists i (u : Obj i), 'inj[dlT] u = x /\ u \is a GRing.unit)
      (dlunit x)
  }.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NzRingDirLim_isUnitRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Lemma dlunitP x :
  dlunit x ->
  {p : {i & Obj i} | 'inj[dlT] (projT2 p) = x /\ projT2 p \is a GRing.unit}.
Proof.
move/dlunit_decP => H.
suff : {p : {i & Obj i} |
  ('inj[dlT] (projT2 p) == x) && (projT2 p \is a GRing.unit)}.
  by move=> [p] /andP[/eqP H1 H2]; exists p.
apply: sigW; move: H => /= [i][u][<-{x} Hunit]; exists (existT Obj i u).
by rewrite eq_refl Hunit.
Qed.

Definition dlinv x : dlT :=
  if (boolP (dlunit x)) is AltTrue pf then
    let: exist p _ := dlunitP pf in 'inj[dlT] ((projT2 p)^-1)
    else x.

Fact dlmulVr : {in dlunit, left_inverse 1 dlinv *%R}.
Proof.
move=> x; rewrite /dlinv unfold_in -/(dlunit x).
case (boolP (dlunit x)) => //; rewrite /dlunit => Hunit _ /=.
case: (dlunitP Hunit) => [][ix inv /= [eqinv unitinv]].
by rewrite -eqinv -rmorphM /= mulVr // rmorph1.
Qed.
Fact dlmulrV : {in dlunit, right_inverse 1 dlinv *%R}.
Proof.
move=> x; rewrite /dlinv unfold_in -/(dlunit x).
case (boolP (dlunit x)) => //; rewrite /dlunit => Hunit _ /=.
case: (dlunitP Hunit) => [][ix inv /= [eqinv unitinv]].
by rewrite -eqinv -rmorphM /= mulrV // rmorph1.
Qed.
Fact dlunit_impl x y : y * x = 1 /\ x * y = 1 -> dlunit x.
Proof.
have [i u v <-{x} <-{y} []] := dirlim2P x y.
rewrite -!rmorphM /= -(dl1E dlT i).
move/eqP/dirlimE => [j le_ij le_j Hl].
move/eqP/dirlimE => [k le_ik le_k Hr].
move: Hl Hr; rewrite !rmorphM !rmorph1 {le_j le_k}.
have [l le_jl le_kl] := directedP j k.
move/(congr1 (bonding _ _ le_jl)); rewrite !rmorphM rmorph1 => Hl.
move/(congr1 (bonding _ _ le_kl)); rewrite !rmorphM rmorph1 => Hr.
move: Hl Hr; rewrite !(bonding_transE Sys).
rewrite !(bondingE Sys _ (le_trans le_ij le_jl)).
set bu := bonding _ _ _ u; set bv := bonding _ _ _ v => Hvu Huv.
apply/dlunit_decP; exists l; exists bu.
split; first by rewrite /bu dlinjE.
by apply/unitrP; exists bv.
Qed.
Fact dlinv0id : {in [predC dlunit], dlinv =1 id}.
Proof.
move=> a; rewrite /dlinv; case (boolP (dlunit a)) => // H1 H2; exfalso.
by move: H2; rewrite !unfold_in /=; have -> : a \in dlunit by [].
Qed.
HB.instance Definition _ :=
  GRing.NzRing_hasMulInverse.Build dlT dlmulVr dlmulrV dlunit_impl dlinv0id.
HB.end.


HB.factory Record UnitRingDirLim_isComUnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of UnitRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of UnitRingDirLim_isComUnitRingDirLim _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NzRingDirLim_isComNzRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record ComUnitRingDirLim_isIntegralDirLim
    disp (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of ComUnitRingDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of ComUnitRingDirLim_isIntegralDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Fact dlmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> Heq; apply/orP; move: Heq.
have [i u v <-{x} <-{y}] := dirlim2P x y.
rewrite -!rmorphM /= => /dlinj_eq0 [j] [le_ij] /=.
rewrite rmorphM => /eqP.
by rewrite mulf_eq0 => /orP [] /eqP /(congr1 'inj[dlT]) H; [left|right];
   move: H; have /= -> := dlinjE dlT _ _ => ->; rewrite rmorph0.
Qed.
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build dlT dlmul_eq0.
HB.end.


HB.factory Record IDomainDirLim_isFieldDirLim
    disp (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of IDomainDirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of IDomainDirLim_isFieldDirLim _ _ _ _ Sys dlT.

Fact dirlim_field_axiom : GRing.field_axiom dlT.
Proof.
move=> x; have [i u <-{x} Hu] := dirlimP x.
have : u != 0 by move: Hu; apply contra => /eqP ->; rewrite raddf0.
rewrite -unitfE => uunit.
by apply/dlunitP; exists i; exists u.
Qed.
HB.instance Definition _ :=
    GRing.UnitRing_isField.Build dlT dirlim_field_axiom.
HB.end.


HB.factory Record NmoduleDirLim_isLSemiModuleDirLim
    (R : pzSemiRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiModType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzSemiRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiModType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of NmoduleDirLim_isLSemiModuleDirLim R _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Definition dlscale r x : dlT :=
  let: existT i u := projT1 (dirlimSP x) in 'inj (r *: u).

Lemma dlscaleE r i (u : Obj i) : dlscale r ('inj u) = 'inj (r *: u).
Proof.
rewrite /dlscale; case: dirlimSP => [[j v /=]] /eqP/dirlimE H.
apply/eqP/dirlimE; move: H => [k /= le_ik le_jk eq_uv].
by exists k le_ik le_jk; rewrite !linearZ /= eq_uv.
Qed.
Fact dlscaleA a b x : dlscale a (dlscale b x) = dlscale (a * b) x.
Proof.
have [i u <-{x}] := dirlimP x.
by rewrite [dlscale b _]dlscaleE !dlscaleE scalerA.
Qed.
Fact dlscale0 x : dlscale 0 x = 0.
Proof.
have [i u <-{x}] := dirlimP x.
by rewrite dlscaleE scale0r raddf0.
Qed.
Fact dlscale1 : left_id 1 dlscale.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite dlscaleE scale1r.
Qed.
Fact dlscaleDr : right_distributive dlscale +%R.
Proof.
move=> r x y; have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite !dlscaleE -!raddfD /= dlscaleE.
Qed.
Fact dlscaleDl x : {morph dlscale^~ x: a b / a + b}.
Proof.
move=> a b; have [i u <-{x}] := dirlimP x.
by rewrite !dlscaleE -raddfD /= -scalerDl.
Qed.
HB.instance Definition _ := GRing.Nmodule_isLSemiModule.Build R dlT
                              dlscaleA dlscale0 dlscale1 dlscaleDr dlscaleDl.

Fact dlinj_is_semilinear i : semilinear 'inj[dlT]_i.
Proof.
split => [r x | x y].
  by rewrite [in RHS]/GRing.scale /= dlscaleE.
by rewrite [in RHS]/GRing.scale /= -raddfD.
Qed.
HB.instance Definition _ :=
  isLSemiModuleDirLim.Build R _ _ _ _ _ dlT dlinj_is_semilinear.
HB.end.


HB.factory Record ZmoduleDirLim_isLmoduleDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of ZmoduleDirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of ZmoduleDirLim_isLmoduleDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isLSemiModuleDirLim.Build R _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isLmoduleDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isLmoduleDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isZmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  ZmoduleDirLim_isLmoduleDirLim.Build _ _ _ _ _ Sys dlT.
HB.end.


HB.factory Record LSemiModuleDirLim_isLSemiAlgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LSemiModuleDirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lSemiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LSemiModuleDirLim_isLSemiAlgebraDirLim R _ _ _ _ Sys dlT.

Implicit Type (x y : dlT) (r : R).

HB.instance Definition _ :=
  NmoduleDirLim_isPzSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  PzSemiRingDirLim_isNzSemiRingDirLim.Build _ _ _ _ Sys dlT.

Fact dlscaleAl r x y : r *: (x * y) = r *: x * y.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -[r *: _ u]linearZ /= -!rmorphM /= -linearZ /= -scalerAl.
Qed.
HB.instance Definition _ :=
  GRing.LSemiModule_isLSemiAlgebra.Build R dlT dlscaleAl.
HB.end.


HB.factory Record LmoduleDirLim_isLalgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LmoduleDirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LmoduleDirLim_isLalgebraDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  LSemiModuleDirLim_isLSemiAlgebraDirLim.Build R _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isLalgebraDirLim
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : pzRingType)
    disp (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isLalgebraDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isLmoduleDirLim.Build R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  LmoduleDirLim_isLalgebraDirLim.Build R _ _ _ _ Sys dlT.
HB.end.


HB.factory Record LSemiAlgebraDirLim_isSemiAlgebraDirLim
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> semiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LSemiAlgebraDirLim _ Sys dlT := {}.
HB.builders Context
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> semiAlgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LSemiAlgebraDirLim_isSemiAlgebraDirLim R _ _ _ _ Sys dlT.

Implicit Type (x y : dlT) (r : R).

Fact dlscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -[r *: _ v]linearZ /= -!rmorphM /= -linearZ /= -scalerAr.
Qed.
HB.instance Definition _ :=
  GRing.LSemiAlgebra_isSemiAlgebra.Build R dlT dlscaleAr.
HB.end.


HB.factory Record LalgebraDirLim_isAlgebraDirLim
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LalgebraDirLim _ Sys dlT := {}.
HB.builders Context
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of LalgebraDirLim_isAlgebraDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  LSemiAlgebraDirLim_isSemiAlgebraDirLim.Build R _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isAlgebraDirLim
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : comPzRingType)
    disp (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isAlgebraDirLim R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isLalgebraDirLim.Build R _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  LalgebraDirLim_isAlgebraDirLim.Build R _ _ _ _ Sys dlT.
HB.end.


Close Scope ring_scope.

Section CommHugeOp.

Variables (disp : _) (I : porderType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j : I, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.

Variable (C : choiceType).
Variables (idx : ilT) (op : Monoid.com_law idx).

Implicit Type F : C -> ilT.
Implicit Types (x y z t : ilT).

Definition invar i x := forall s, 'pi_i (op x s) = 'pi_i s.
Definition is_ilopable F :=
  `[< forall i, exists S : {fset C}, forall c, c \notin S -> invar i (F c)>].
Lemma ilopand_spec F :
  is_ilopable F ->
  forall i, { f : {fset C} | f =i predC (fun c => `[< invar i (F c)>]) }.
Proof.
move=> H i; move/asboolP/(_ i): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq c <- s | ~~ `[< invar i (F c)>]]) => c.
rewrite seq_fsetE !inE mem_filter.
by case: (boolP `[< _>]) => //=; apply contraR => /Hs/asboolT.
Qed.
Definition ilopand F (sm : is_ilopable F) c :=
  let: exist fs _ := ilopand_spec sm c in fs.

Lemma ilopandP F (sm : is_ilopable F) i c :
  reflect (invar i (F c)) (c \notin (ilopand sm i)).
Proof.
rewrite /ilopand; apply (iffP negP); case: ilopand_spec => f Hf.
- by rewrite Hf inE => /negP; rewrite negbK => /asboolW.
- by rewrite Hf inE => H; apply/negP; rewrite negbK; apply asboolT.
Qed.

Lemma ilopand_subset F (sm : is_ilopable F) i j :
  i <= j -> (ilopand sm i `<=` ilopand sm j)%fset.
Proof.
move=> ilej.
apply/fsubsetP => c; apply/contraLR => /ilopandP Hinv.
by apply/ilopandP => x; rewrite -!(ilprojE _ ilej) Hinv.
Qed.

Fact ilopand_istrhead F (sm : is_ilopable F) :
  isthread Sys (fun i => 'pi_i (\big[op/idx]_(c <- ilopand sm i) F c)).
Proof.
move=> i j Hij; rewrite ilprojE.
rewrite (bigID (fun c => `[< invar i (F c)>])) /=.
set X := (X in op _ X); set Y := (Y in _ = _ Y).
have {X} -> : X = Y.
  rewrite {}/X {}/Y; apply eq_fbigl_cond => c.
  rewrite !inE andbT; apply negb_inj; rewrite negb_and negbK.
  case: (boolP (c \in (ilopand sm j))) => /= Hc.
  - by apply/asboolP/idP=> /ilopandP //; apply.
  - suff -> : c \notin (ilopand sm i) by [].
    by apply/contra: Hc; apply: (fsubsetP (ilopand_subset sm Hij)).
elim: (X in \big[op/idx]_(i <- X | _) _) => [| s0 s IHs].
  by rewrite big_nil Monoid.mul1m.
rewrite big_cons /=; case: asboolP => [|]; last by rewrite IHs.
by rewrite -Monoid.mulmA {1}/invar => ->.
Qed.

Definition HugeOp F : ilT :=
  if pselect (is_ilopable F) is left sm
  then ilthr (ilopand_istrhead sm)
  else idx.

Local Notation "\Op_( c ) F" := (HugeOp (fun c => F)) (at level 0).

Lemma projHugeOp F i (S : {fset C}) :
  is_ilopable F ->
  subpred (predC (mem S)) (fun c => `[< invar i (F c)>]) ->
  'pi_i (\Op_(c) (F c)) = 'pi_i (\big[op/idx]_(c <- S) F c).
Proof.
rewrite /HugeOp=> Hop Hsub; case: pselect => [/= {}Hop |/(_ Hop) //].
transitivity ('pi_i (\big[op/idx]_(c <- S | c \in ilopand Hop i) F c));
    first last.
  rewrite [in RHS](bigID [pred c | `[< invar i (F c)>]]) /=.
  set Inv := (X in op X _); have {Inv} -> : invar i Inv.
    rewrite {}/Inv; elim: {1}(enum_fset S) => [| s0 s IHs].
      by rewrite  big_nil => s; rewrite Monoid.mul1m.
    rewrite big_cons.
    by case asboolP; rewrite {1}/invar => H s1 //; rewrite -Monoid.mulmA H IHs.
  congr 'pi_i; apply: eq_big => x //.
  by apply/negb_inj; rewrite negbK; apply/ilopandP/asboolP.
rewrite ilthrP; congr 'pi_i.
rewrite [in RHS]big_fset_condE; apply: eq_fbigl => c.
rewrite !inE andbC.
case: (boolP (c \in _)) => //= /ilopandP/asboolP Hc; apply/esym.
by have /contraR /= := Hsub c; rewrite -asbool_neg => /(_ Hc).
Qed.

End CommHugeOp.


Section Summable.

Variables (disp : _) (I : porderType disp).
Variable Obj : I -> nmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : nmodInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> ilT.
Implicit Types (s x y z t : ilT).

Let add_law : Monoid.com_law 0 := (+%R : ilT -> ilT -> ilT).

Definition is_summable F := is_ilopable add_law F.
Definition summand F (sm : is_summable F) := ilopand sm.
Definition HugeSum F : ilT := HugeOp add_law F.

Local Notation "\Sum_( c ) F" := (HugeSum (fun c => F)).

Lemma invar_addE F i c : invar add_law i (F c) <-> 'pi_i (F c) = 0.
Proof.
rewrite /invar /=; split => [/(_ 0)| H0 x]; first by rewrite addr0 raddf0.
by rewrite raddfD /= H0 add0r.
Qed.

Lemma is_summableP F :
  (is_summable F) <->
  (forall i, exists S : {fset C}, forall c, c \notin S -> 'pi_i (F c) = 0).
Proof.
split.
- rewrite /is_summable/is_ilopable => /asboolP H i.
  move: H => /(_ i) [S HS]; exists S => c /HS.
  by rewrite invar_addE.
- move=> H; apply/asboolP => i; move/(_ i): H => [S Hs].
  by exists S => c; rewrite invar_addE => /Hs.
Qed.

Lemma summandP F (sm : is_summable F) i c :
  reflect ('pi_i (F c) = 0) (c \notin (summand sm i)).
Proof. by apply (iffP (ilopandP _ _ _)); rewrite invar_addE. Qed.

Lemma summand_subset F (sm : is_summable F) i j :
  i <= j -> (summand sm i `<=` summand sm j)%fset.
Proof. exact: ilopand_subset. Qed.

Lemma projHugeSum F i (S : {fset C}) :
  is_summable F ->
  (forall c : C, c \notin S -> 'pi_i (F c) = 0) ->
  'pi_i (\Sum_(c) F c) = 'pi_i (\sum_(c <- S) F c).
Proof.
move=> /projHugeOp H Hpred; apply: H => c {}/Hpred /= H.
by apply/asboolP; rewrite invar_addE.
Qed.

End Summable.



Section Prodable.

Variables (disp : _) (I : porderType disp).
Variable Obj : I -> comPzSemiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : comPzSemiRingInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> ilT.
Implicit Types (s x y z t : ilT).

Let mul_law : Monoid.com_law 1 := ( *%R : ilT -> ilT -> ilT).

Definition is_prodable F := is_ilopable mul_law F.
Definition prodand F (sm : is_prodable F) := ilopand sm.
Definition HugeProd F : ilT := HugeOp mul_law F.

Local Notation "\Prod_( c ) F" := (HugeProd (fun c => F)) (at level 0).

Lemma invar_mulE F i c : invar mul_law i (F c) <-> 'pi_i (F c) = 1.
Proof.
rewrite /invar /=; split => [/(_ 1)| H0 x].
  by rewrite rmorphM /= rmorph1 mulr1.
by rewrite rmorphM /= H0 mul1r.
Qed.

Lemma is_prodableP F :
  (is_prodable F) <->
  (forall i, exists S : {fset C}, forall c, c \notin S -> 'pi_i (F c) = 1).
Proof.
split.
- rewrite /is_prodable/is_ilopable => /asboolP H i.
  move: H => /(_ i) [S HS]; exists S => c /HS.
  by rewrite invar_mulE.
- move=> H; apply/asboolP => i; move/(_ i): H => [S Hs].
  by exists S => c; rewrite invar_mulE => /Hs.
Qed.

Lemma prodandP F (sm : is_prodable F) i c :
  reflect ('pi_i (F c) = 1) (c \notin (prodand sm i)).
Proof. by apply (iffP (ilopandP _ _ _)); rewrite invar_mulE. Qed.

Lemma prodand_subset F (sm : is_prodable F) i j :
  i <= j -> (prodand sm i `<=` prodand sm j)%fset.
Proof. exact: ilopand_subset. Qed.

Lemma projHugeProd F i (S : {fset C}) :
  is_prodable F ->
  (forall c : C, c \notin S -> 'pi_i (F c) = 1) ->
  'pi_i (\Prod_( c ) (F c)) = 'pi_i (\prod_(c <- S) F c).
Proof.
move=> /projHugeOp H Hpred; apply: H => c {}/Hpred /= H.
by apply/asboolP; rewrite invar_mulE.
Qed.

End Prodable.

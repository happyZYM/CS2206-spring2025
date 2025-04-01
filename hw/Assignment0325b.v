Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_SimpleWhile.
Require Import PV.ExprIntDenotation.
Require Import PV.ExprBoolDenotation.
Require Import PV.RelsAsDenotations.
Require Import PV.HoareLogic.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       DntSem_SimpleWhile4_Properties
       HoareSimpleWhile.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.

(************)
(** 习题：  *)
(************)
Lemma hoare_seq_valid_inv: forall P R c1 c2,
  valid {{ P }} c1 ; c2 {{ R }} ->
  exists Q: assertion,
    valid {{ P }} c1 {{ Q }} /\
    valid {{ Q }} c2 {{ R }}.
Proof.
  unfold valid.
  unfold_sem.
  intros.
  simpl in H.
  Sets_unfold in H.
  exists (fun s => (exists s1: state, P s1 /\ (s1, s) ∈ ⟦ c1 ⟧)).
  split.
  + intros.
    exists s1.
    split; tauto.
  + intros.
    destruct H0.
    specialize (H x s2).
    destruct H0.
    specialize (H H0).
    assert (exists i : state, (x, i) ∈ ⟦ c1 ⟧ /\ (i, s2) ∈ ⟦ c2 ⟧).
    {
      exists s1.
      split; tauto.
    }
    specialize (H H3).
    tauto.
Qed.


(************)
(** 习题：  *)
(************)

Lemma hoare_skip_inv: forall P Q,
  provable {{ P }} skip {{ Q }} -> P |--  Q.
Proof.
  intros.
  remember ({{P}} skip {{Q}}) as ht eqn:EQ.
  revert P Q EQ; induction H; intros; try discriminate EQ.
  + injection EQ.
    intros.
    subst.
    assn_tauto.
  + injection EQ.
    intros.
    subst Q0.
    subst P0.
    subst c.
    clear EQ.
    specialize (IHprovable P' Q').
    assert (P' |-- Q').
    {
      apply IHprovable.
      reflexivity.
    }
    unfold derives in *.
    intros.
    apply H0 in H3.
    apply H2 in H3.
    apply H1 in H3.
    tauto.
Qed.

(************)
(** 习题：  *)
(************)

Lemma hoare_while_inv: forall P Q e c,
  provable {{ P }} while (e) do { c } {{ Q }} ->
  exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q.
Proof.
  intros.
  remember ({{ P }} while (e) do { c } {{ Q }}) as ht eqn:EQ.
  revert P Q EQ; induction H; intros; try discriminate EQ.
  + injection EQ.
    intros.
    subst P0 c0 e0.
    clear IHprovable.
    exists P.
    split.
    * assn_tauto.
    * split.
      - tauto.
      - rewrite <- H0.
        assn_tauto.
  + injection EQ.
    intros.
    subst P0 c0 Q0.
    specialize (IHprovable P' Q').
    assert (exists I : assertion, (P' |-- I) /\ provable {{I && [[e]]}} c {{I}} /\ Assn (I && [[! e]]) |-- Q').
    {
      apply IHprovable.
      reflexivity.
    }
    destruct H2.
    exists x.
    destruct H2.
    destruct H3.
    split; try split.
    * unfold derives in *.
      intros.
      apply H0 in H5.
      apply H2 in H5.
      tauto.
    * tauto.
    * unfold derives in *.
      intros.
      apply H4 in H5.
      apply H1 in H5.
      tauto.
Qed. 



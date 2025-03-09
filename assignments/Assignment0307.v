Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_SimpleWhile.
Require Import PV.ExprIntDenotation.
Require Import PV.ExprBoolDenotation.
Require Import PV.RelsAsDenotations.
Import DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       DntSem_SimpleWhile4_Properties.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.

(************)
(** 习题：  *)
(************)

(** 下面我们定义一项简单的程序变换：右结合变换。例如，将_[(c1;c2);c3]_变换为
    _[c1;(c2;c3)]_。

    首先，这里定义一个辅助函数，该函数假设_[c]_与_[c0]_已经是右结合的，计算
    _[c; c0]_转换后的结果*)

Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

(** 现在，可以在_[CSeq_right_assoc]_的基础上定义右结合变换_[right_assoc]_。*)

Fixpoint right_assoc (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      CSeq_right_assoc (right_assoc c1) (right_assoc c2)
  | CIf e c1 c2 =>
      CIf e (right_assoc c1) (right_assoc c2)
  | CWhile e c1 =>
      CWhile e (right_assoc c1)
  | _ =>
      c
  end.

(** 下面证明：经过右结合变换后，确实程序语句中不再有左结合的结构了。下面分为两步
    定义『无左结合结构』，即_[no_left_assoc]_。*)

Definition not_left_assoc (c: com): Prop :=
  match c with
  | CSeq (CSeq _ _) _ => False
  | _ => True
  end.

Fixpoint no_left_assoc (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_left_assoc c /\
      no_left_assoc c1 /\ no_left_assoc c2
  | CIf e c1 c2 =>
      no_left_assoc c1 /\ no_left_assoc c2
  | CWhile e c1 =>
      no_left_assoc c1
  | _ =>
      True
  end.

(** 证明也需要分两步进行。请先证明关于_[CSeq_right_assoc]_的引理。*)

Lemma CSeq_right_assoc_no_left_assoc: forall c c0,
  no_left_assoc c ->
  no_left_assoc c0 ->
  no_left_assoc (CSeq_right_assoc c c0).
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  induction c;
  induction c0;
  try simpl in *; try tauto.
Qed.

(** 下面是需要证明的最终结论。*)

Theorem right_assoc_no_left_assoc: forall c,
  no_left_assoc (right_assoc c).
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  induction c; simpl; try tauto.
  apply CSeq_right_assoc_no_left_assoc; try tauto.
Qed.



(************)
(** 习题：  *)
(************)

(** 请证明下面关于行为等价的性质。*)

Theorem if_seq:
  forall e c1 c2 c3,
    [[ if (e) then { c1 } else { c2 }; c3 ]] ~=~
    [[ if (e) then { c1; c3 } else { c2; c3 } ]].
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  unfold cequiv.
  unfold_sem.
  Sets_unfold.
  intros.
  split; intros.
  + destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    - left.
      exists x0.
      split.
      apply H.
      exists x.
      tauto.
    - destruct H.
      destruct H.
      right.
      exists x0.
      split.
      apply H.
      exists x.
      tauto.
  + destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    - exists x0.
      split.
      left.
      exists x.
      split.
      tauto.
      tauto.
      tauto.
    - destruct H.
      destruct H.
      destruct H0.
      destruct H0.
      exists x0.
      split.
      right.
      exists x.
      split.
      tauto.
      tauto.
      tauto.
Qed.


(************)
(** 习题：  *)
(************)

(** 下面请分两步证明：_[right_assoc]_变换前后的程序是语义等价的。*)

Lemma CSeq_right_assoc_sound: forall c c0,
  CSeq_right_assoc c c0 ~=~ [[ c; c0 ]].
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  induction c; destruct c0; try reflexivity;
  simpl; try rewrite IHc2;
  unfold cequiv; unfold_sem; simpl; Sets_unfold; intros; split; intros.
  + destruct H. destruct H. destruct H0. destruct H0.
    exists a0.
    split.
    exists x.
    split.
    apply H.
    rewrite <- H1.
    apply H0.
    reflexivity.
  + destruct H. destruct H. destruct H. destruct H.
    exists x0.
    split.
    apply H.
    exists a0.
    split.
    rewrite <- H0.
    apply H1.
    reflexivity.
  + destruct H. destruct H. destruct H0. destruct H0.
    exists x1.
    split.
    exists x0.
    split.
    apply H.
    apply H0.
    apply H1.
  + destruct H. destruct H. destruct H. destruct H.
    exists x1.
    split.
    apply H.
    exists x0.
    split.
    apply H1.
    apply H0.
  + destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1.
    exists x0.
    split.
    - exists x.
      split.
      apply H.
      apply H0.
    - exists x1.
      split.
      apply H1.
      apply H2.
  + destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0.
    exists x0.
    split.
    apply H.
    exists x.
    split.
    apply H1.
    exists x1.
    split.
    apply H0.
    apply H2.
  + destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H1.
    - exists x0.
      split.
      exists x.
      split.
      apply H.
      apply H0.
      left.
      exists x1.
      split.
      apply H1.
      apply H2.
    - destruct H1. destruct H1.
      exists x0.
      split.
      exists x.
      split.
      apply H.
      apply H0.
      right.
      exists x1.
      split.
      apply H1.
      apply H2.
  + destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0.
    - exists x0.
      split.
      apply H.
      exists x.
      split.
      apply H1.
      left.
      exists x1.
      split.
      apply H0.
      apply H2.
    - destruct H0. destruct H0.
      exists x0.
      split.
      apply H.
      exists x.
      split.
      apply H1.
      right.
      exists x1.
      split.
      apply H0.
      apply H2.
  + destruct H. destruct H. destruct H0. destruct H0. destruct H1.
    exists x0.
    split.
    - exists x.
      split.
      apply H.
      apply H0.
    - exists x1.
      apply H1.
  + destruct H. destruct H. destruct H. destruct H. destruct H0. 
    exists x0.
    split.
    apply H.
    exists x.
    split.
    apply H1.
    exists x1.
    apply H0.
Qed.
    


Theorem right_assoc_sound: forall c,
  right_assoc c ~=~ c.
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  induction c; try reflexivity; simpl.
  + pose proof CSeq_right_assoc_sound (right_assoc c1) (right_assoc c2).
    rewrite H.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.
  + rewrite IHc1.
    rewrite IHc2.
    reflexivity.
  + rewrite IHc.
    reflexivity.
Qed.
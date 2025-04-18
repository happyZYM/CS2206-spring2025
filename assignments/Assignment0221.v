Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.Intro.
Require Import PV.InductiveType.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  unfold opposite_sgn in H.
  nia.
Qed.

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  unfold opposite_sgn in H.
  unfold square in H.
  nia.
Qed.


(************)
(** 习题：  *)
(************)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  induction t.
  - simpl.
    lia.
  - simpl.
    lia.
Qed.

(************)
(** 习题：  *)
(************)

Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros t.
  induction t.
  + discriminate.
  + simpl.
    intros.
    injection H as H1 H2 H3.
    rewrite <- H1.
    rewrite <- H2.
    rewrite <- H3.
    rewrite (reverse_involutive t1).
    rewrite (reverse_involutive t2).
    reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
(* Admitted. 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros t.
  induction t.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHt2.
    intros.
    reflexivity.
Qed. 

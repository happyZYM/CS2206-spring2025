Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.ExprIntDenotation.
Local Open Scope string.
Local Open Scope Z.

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.

(** * 布尔表达式的语义 *)

(** 在Coq中可以如下定义：*)

Definition true_sem: state -> bool :=
  fun s => true.

Definition false_sem: state -> bool :=
  fun s => false.

Definition lt_sem (D1 D2: state -> Z):
  state -> bool :=
  fun s =>
    if Z_lt_dec (D1 s) (D2 s)
    then true
    else false.

Definition and_sem (D1 D2: state -> bool):
  state -> bool :=
  fun s => andb (D1 s) (D2 s).

Definition not_sem (D: state -> bool):
  state -> bool :=
  fun s => negb (D s).

Fixpoint eval_expr_bool (e: expr_bool): state -> bool :=
  match e with
  | ETrue =>
      true_sem
  | EFalse =>
      false_sem
  | ELt e1 e2 =>
      lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 =>
      and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 =>
      not_sem (eval_expr_bool e1)
  end.

Notation "⟦ e ⟧" := (eval_expr_bool e)
  (at level 0, only printing, e custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    end
  end.

Ltac unfold_expr_bool_sem :=
  cbv [true_sem false_sem lt_sem and_sem not_sem].

Ltac unfold_expr_bool_sem_in_hyp H :=
  cbv [true_sem false_sem lt_sem and_sem not_sem] in H.

Ltac ___unfold_sem ::=
  simpl eval_expr_bool; simpl eval_expr_int;
  unfold_expr_bool_sem; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H ::=
  simpl eval_expr_bool in H; simpl eval_expr_int in H;
  unfold_expr_bool_sem_in_hyp H; unfold_expr_int_sem_in_hyp H.

(** 基于这一定义，我们可以证明一些简单性质。*)

Lemma lt_spec:
  forall (e1 e2: expr_int) (s: state),
    ⟦ e1 < e2 ⟧ s = true <-> ⟦ e1 ⟧ s < ⟦ e2 ⟧ s.
Proof.
  intros.
  unfold_sem.
  (** 下面的_[destruct]_指令是对_[⟦ e1 ⟧ s < ⟦ e2 ⟧ s]_是否成立做分类讨论。*)
  destruct (Z_lt_dec (⟦ e1 ⟧ s) (⟦ e2 ⟧ s)).
  + tauto.
  + (** 下面的_[intuition]_指令在_[tauto]_的基础上一并考虑了一些基本类型的简单性质。*)
    intuition.
Qed.

(** 与整数类型表达式的行为等价定义一样，我们也可以用函数相等定义布尔表达式行为等价。*)

Definition bequiv (e1 e2: expr_bool): Prop :=
  (⟦ e1 ⟧ == ⟦ e2 ⟧)%func.

Notation "e1 '~=~' e2" := (bequiv e1 e2)
  (at level 69, no associativity, only printing).

Ltac any_equiv' x y ::=
  match type of x with
  | expr_int  => exact (iequiv x y)
  | expr_bool => exact (bequiv x y)
  | _         =>
      match type of y with
      | expr_int  => exact (iequiv x y)
      | expr_bool => exact (bequiv x y)
      end
  end.

(** 我们同样可以证明一些简单的布尔表达式行为等价的例子。*)

Example lt_plus_one_fact:
  [[ "x" < "x" + 1 ]] ~=~ ETrue.
Proof.
  unfold bequiv; intros s.
  unfold_sem.
  destruct (Z_lt_dec (s "x") (s "x" + 1)).
  + reflexivity.
  + lia.
Qed.

(** 下面先证明三个语义算子_[lt_sem]_、_[and_sem]_与_[not_sem]_能保持函数相等，再利用
    函数相等的性质证明布尔表达式行为等价的性质。*)

#[export] Instance lt_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          func_equiv _ _) lt_sem.
Proof.
  unfold Proper, respectful, lt_sem.
  unfold func_equiv, pointwise_relation.
  intros D11 D12 H1 D21 D22 H2 s.
  rewrite H1, H2.
  reflexivity.
Qed.

#[export] Instance and_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          func_equiv _ _) and_sem.
Proof.
  unfold Proper, respectful, and_sem.
  unfold func_equiv, pointwise_relation.
  intros D11 D12 H1 D21 D22 H2 s.
  rewrite H1, H2.
  reflexivity.
Qed.

#[export] Instance not_sem_congr:
  Proper (func_equiv _ _ ==> func_equiv _ _) not_sem.
Proof.
  unfold Proper, respectful, not_sem.
  unfold func_equiv, pointwise_relation.
  intros D1 D2 H s.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance bequiv_equiv: Equivalence bequiv.
Proof.
  unfold bequiv.
  apply equiv_in_domain.
  apply func_equiv_equiv.
Qed.

#[export] Instance ELt_congr:
  Proper (iequiv ==> iequiv ==> bequiv) ELt.
Proof.
  unfold Proper, respectful, bequiv, iequiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EAnd_congr:
  Proper (bequiv ==> bequiv ==> bequiv) EAnd.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance ENot_congr:
  Proper (bequiv ==> bequiv) ENot.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  rewrite H.
  reflexivity.
Qed.


End DntSem_SimpleWhile3.

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PV.Syntax.
Require Import PV.ExprIntDenotation.
Require Import PV.ExprBoolDenotation.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3.
Local Open Scope string.
Local Open Scope Z.

(** 请注意，使用高阶函数定义指称语义后，有时证明中需要展开的定义较多。讲义中提供了
    _[unfold_sem]_指令用于进行批量的定义化简。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于布尔表达式行为等价的命题。*)

Example true_and_fact:
  forall e: expr_bool,
    [[ ETrue && e ]] ~=~ e.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 请利用已有的结论_[lt_plus_one_fact]_证明下面命题。*)

Example lt_plus_one_and_fact:
  forall e: expr_bool,
    [[ "x" < "x" + 1 && e ]] ~=~ e.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



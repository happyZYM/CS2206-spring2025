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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

Lemma hoare_skip_inv: forall P Q,
  provable {{ P }} skip {{ Q }} -> P |--  Q.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Lemma hoare_while_inv: forall P Q e c,
  provable {{ P }} while (e) do { c } {{ Q }} ->
  exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



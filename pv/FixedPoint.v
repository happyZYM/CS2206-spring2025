Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.ExprIntDenotation.
Require Import PV.ExprBoolDenotation.
Require Import PV.RelsAsDenotations.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.



(** * Coq中证明并应用Kleene不动点定理 *)

Module KleeneFix.


(** 下面我们将在Coq中证明Kleene不动点定理。在Kleene不动点定理中，我们需要证明满足某些特
    定条件（例如偏序、完备偏序等）的二元关系的一些性质。在Coq中，我们当然可以通过
    _[R: A -> A -> Prop]_来探讨二元关系_[R]_的性质。然而Coq中并不能给这样的变量设定
    Notation符号，例如，我们希望用_[a <= b]_来表示_[R a b]_，因此我们选择使用Coq的
    _[Class]_来帮助我们完成定义。

    下面这一定义说的是：_[Order]_是一类数学对象，任给一个类型_[A]_，_[Order A]_
    也是一个类型，这个类型的每个元素都有一个域，这个域的名称是_[order_rel]_，它
    的类型是_[A -> A -> Prop]_，即_[A]_上的二元关系。*)

Class Order (A: Type): Type :=
  order_rel: A -> A -> Prop.

(** Coq中_[Class]_与_[Record]_有些像，但是有两点区别。第一：_[Class]_如果只有一
    个域，它的中可以不使用大括号将这个域的定义围起来；第二：在定义或证明中，Coq
    系统会试图自动搜索并填充类型为_[Class]_的参数，搜索范围为之前注册过可以使用
    的_[Instance]_以及当前环境中的参数。例如，我们先前在证明等价关系、congruence
    性质时就使用过_[Instance]_。例如，下面例子中，不需要指明_[order_rel]_是哪个
    _[Order A]_的_[order_rel]_域，Coq会自动默认这是指_[RA]_的_[order_rel]_域。*)

Check forall {A: Type} {RA: Order A} (x: A),
        exists (y: A), order_rel x y.

(** 这样，我们就可以为_[order_rel]_定义Notation符号。*)

Declare Scope order_scope.
Notation "a <= b" := (order_rel a b): order_scope.
Local Open Scope order_scope.

Check forall {A: Type} {RA: Order A} (x y: A),
        x <= y \/ y <= x.

(** 基于序关系，我们就可以定义上界与下界的概念。由于Kleene不动点定理中主
    要需要探讨无穷长元素序列的上界与上确界，下面既定义了元素集合的上下界也定义了
    元素序列的上下界。*)

Definition is_lb
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a <= a'.

Definition is_ub
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a' <= a.

Definition is_omega_lb
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, a <= l n.

Definition is_omega_ub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, l n <= a.

(** 下面定义序列的上确界，所谓上确界就是上界中最小的一个，因此它的定义包含两个子
    句。而在后续证明中，使用上确界性质的时候，有时需要用其第一条性质，有时需要用
    其第二条性质。为了后续证明的方便，这里在定义之外提供了使用这两条性质的方法：
    _[is_omega_lub_sound]_与_[is_omega_lub_tight]_。比起在证明中使用_[destruct]_
    指令拆解上确界的定义，使用这两条引理，可以使得Coq证明更自然地表达我们的证明
    思路。之后我们将在证明偏序集上上确界唯一性的时候会看到相关的用法。*)

Definition is_omega_lub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  is_omega_ub l a /\ is_lb (is_omega_ub l) a.

Lemma is_omega_lub_sound:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_omega_ub l a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Lemma is_omega_lub_tight:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_lb (is_omega_ub l) a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

(** 在编写Coq定义时，另有一个问题需要专门考虑，有些数学上的相等关系在Coq中只是一
    种等价关系。例如，我们之前在Coq中用过集合相等的定义。因此，我们描述
    Kleene不动点定理的前提条件时，也需要假设有一个与序关系相关的等价关
    系，我们用_[Equiv]_表示，并用_[==]_这个符号描述这个等价关系。*)

Class Equiv (A: Type): Type :=
  equiv: A -> A -> Prop.

Notation "a == b" := (equiv a b): order_scope.

(** 基于此，我们可以定义基于等价关系的自反性与反对称性。注意，传递性的定义与这个
    等价关系无关。这里我们也用_[Class]_定义，这与Coq标准库中的自反、对称、传递的
    定义是类似的，但是也有不同：(1) 我们的定义需要探讨一个二元关系与一个等价关系
    之间的联系，而Coq标准库中只考虑了这个等价关系是普通等号的情况；(2) Coq标准库
    中直接使用二元关系_[R: A -> A -> Prop]_作为参数，而我们的参数使用了_[Order]_
    与_[Equiv]_这两个_[Class]_。 

    自反性： *)
Class Reflexive_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  reflexivity_setoid:
    forall a b, a == b -> a <= b.

(** 反对称性： *)
Class AntiSymmetric_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  antisymmetricity_setoid:
    forall a b, a <= b -> b <= a -> a == b.

(** 现在，我们就可以如下定义偏序关系。*)

Class PartialOrder_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
{
  PO_Reflexive_Setoid:> Reflexive_Setoid A;
  PO_Transitive:> Transitive order_rel;
  PO_AntiSymmetric_Setoid:> AntiSymmetric_Setoid A
}.

(** 下面证明两条偏序集的基本性质。在Coq中，我们使用前引号_[`]_让Coq自动填充
    _[Class]_类型元素的参数。例如，_[`{POA: PartialOrder_Setoid A}]_会指引Coq
    额外填上_[RA: Order A]_和_[EA: Equiv A]_。

    序关系两侧做等价变换不改变序关系：*)

#[export] Instance PartialOrder_Setoid_Proper
           {A: Type} `{POA: PartialOrder_Setoid A} {EquivA: Equivalence equiv}:
  Proper (equiv ==> equiv ==> iff) order_rel.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply reflexivity_setoid; tauto].
    transitivity x; [apply reflexivity_setoid; symmetry; tauto |].
    tauto.
  + transitivity y0; [| apply reflexivity_setoid; symmetry; tauto].
    transitivity y; [apply reflexivity_setoid; tauto |].
    tauto.
Qed.

(** 如果两个序列的所有上界都相同，那么他们的上确界也相同（如果有的话）：*)

Lemma same_omega_ub_same_omega_lub:
  forall
    {A: Type}
    `{POA: PartialOrder_Setoid A}
    (l1 l2: nat -> A)
    (a1 a2: A),
  (forall a, is_omega_ub l1 a <-> is_omega_ub l2 a) ->
  is_omega_lub l1 a1 ->
  is_omega_lub l2 a2 ->
  a1 == a2.
Proof.
  intros A ? ? POA.
  intros.
  apply antisymmetricity_setoid.
  + apply (is_omega_lub_tight H0).
    apply H.
    apply (is_omega_lub_sound H1).
  + apply (is_omega_lub_tight H1).
    apply H.
    apply (is_omega_lub_sound H0).
Qed.

(** 证明Kleene不动点定理时还需要定义完备偏序集，由于在其证明中实际只用到
    了完备偏序集有最小元和任意单调不减的元素序列有上确界，我们在Coq定义时也只考
    虑符合这两个条件的偏序集，我们称为OmegaCPO，Omega表示可数无穷多项的意思。另
    外，尽管数学上仅仅要求完备偏序集上的所有链有上确界，但是为了Coq证明的方便，
    我们将_[omega_lub]_定义为所有元素序列的上确界计算函数，只不过我们仅仅要求该
    函数在其参数为单调不减序列时能确实计算出上确界，见_[oCPO_completeness]_。*)

Class OmegaLub (A: Type): Type :=
  omega_lub: (nat -> A) -> A.

Class Bot (A: Type): Type :=
  bot: A.

Definition increasing
             {A: Type} {RA: Order A} (l: nat -> A): Prop :=
  forall n, l n <= l (S n).

Definition is_least {A: Type} {RA: Order A} (a: A): Prop :=
  forall a', a <= a'.

Class OmegaCompletePartialOrder_Setoid
        (A: Type)
        {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
{
  oCPO_PartialOrder:> PartialOrder_Setoid A;
  oCPO_completeness: forall T,
    increasing T -> is_omega_lub T (omega_lub T);
  bot_is_least: is_least bot
}.

(** 利用这里定义中的_[omega_lub]_函数，可以重述先前证明过的性质：两个单调不减序
    列如果拥有完全相同的上界，那么他们也有同样的上确界。*)

Lemma same_omega_ub_same_omega_lub':
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (l1 l2: nat -> A),
  (forall a, is_omega_ub l1 a <-> is_omega_ub l2 a) ->
  increasing l1 ->
  increasing l2 ->
  omega_lub l1 == omega_lub l2.
Proof.
  intros.
  apply (same_omega_ub_same_omega_lub _ _ _ _ H).
  + apply oCPO_completeness.
    apply H0.
  + apply oCPO_completeness.
    apply H1.
Qed.

(** 下面定义单调连续函数。*)

Definition mono
             {A B: Type}
             `{POA: PartialOrder_Setoid A}
             `{POB: PartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall a1 a2, a1 <= a2 -> f a1 <= f a2.

Definition continuous
             {A B: Type}
             `{oCPOA: OmegaCompletePartialOrder_Setoid A}
             `{oCPOB: OmegaCompletePartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall l: nat -> A,
    increasing l ->
    f (omega_lub l) == omega_lub (fun n => f (l n)).

(** 下面我们可以证明：自反函数是单调连续的、复合函数能保持单调连续性。

    自反函数的单调性：*)
Lemma id_mono:
  forall {A: Type}
         `{POA: PartialOrder_Setoid A},
  mono (fun x => x).
Proof.
  unfold mono; intros.
  apply H.
Qed.

(** 复合函数保持单调性：*)
Lemma compose_mono:
  forall {A B C: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         `{POC: PartialOrder_Setoid C}
         (f: A -> B)
         (g: B -> C),
  mono f -> mono g -> mono (fun x => g (f x)).
Proof.
  unfold mono; intros.
  apply H0, H, H1.
Qed.

(** 自反函数的连续性：*)
Lemma id_continuous:
  forall {A: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         {EquivA: Equivalence equiv},
  continuous (fun x => x).
Proof.
  unfold continuous; intros.
  reflexivity.
Qed.

(** 这里，要证明单调连续函数的复合结果也是连续的要复杂一些。显然，这其中需要证明
    一个单调函数作用在一个单调不减序列的每一项后还会得到一个单调不减序列。下面的
    引理_[increasing_mono_increasing]_描述了这一性质。*)
Lemma increasing_mono_increasing:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         (f: A -> B)
         (l: nat -> A),
  increasing l -> mono f -> increasing (fun n => f (l n)).
Proof.
  unfold increasing.
  intros.
  apply H0.
  apply H.
Qed.

(** 除此之外，我们还需要证明单调函数能保持相等关系，即，如果_[f]_是一个单调函
    数，那么_[x == y]_能推出_[f x == f y]_。当然，如果这里的等价关系就是等号描述
    的相等关系，那么这个性质是显然的。但是，对于一般的等价关系，这就并不显然了。
    这一引理的正确性依赖于偏序关系中的自反性和反对称性。*)
Lemma mono_equiv_congr:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
          {EquivA: Equivalence (equiv: A -> A -> Prop)}
         (f: A -> B),
  mono f -> Proper (equiv ==> equiv) f.
Proof.
  unfold mono, Proper, respectful.
  intros.
  apply antisymmetricity_setoid; apply H.
  + apply reflexivity_setoid.
    apply H0.
  + apply reflexivity_setoid.
    rewrite H0.
    reflexivity.
Qed.

(** 现在，可以利用上面两条引理证明复合函数的连续性了。*)
Lemma compose_continuous:
  forall {A B C: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         `{oCPOB: OmegaCompletePartialOrder_Setoid B}
         `{oCPOC: OmegaCompletePartialOrder_Setoid C}
          {EquivB: Equivalence (equiv: B -> B -> Prop)}
          {EquivC: Equivalence (equiv: C -> C -> Prop)}
         (f: A -> B)
         (g: B -> C),
  mono f ->
  mono g ->
  continuous f ->
  continuous g ->
  continuous (fun x => g (f x)).
Proof.
  unfold continuous.
  intros.
  pose proof increasing_mono_increasing f l H3 H.
  specialize (H1 _ H3).
  specialize (H2 _ H4).
  simpl in H2.
  rewrite <- H2.
  apply mono_equiv_congr in H0.
  apply H0.
  apply H1.
Qed.

(** 到目前为止，我们已经定义了Omega完备偏序集与单调连续函数。在证明Kleene
    不动点定理之前还需要最后一项准备工作：定理描述本身的合法性。即，我们需要证明
    _[bot]_, _[f bot]_, _[f (f bot)]_...这个序列的单调性。我们利用Coq标准库中的
    _[Nat.iter]_来定义这个序列，_[Nat.iter n f bot]_表示将_[f]_连续_[n]_次作用在
    _[bot]_上。*)

Lemma iter_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => Nat.iter n f bot).
Proof.
  unfold increasing.
  intros.
  induction n; simpl.
  + apply bot_is_least.
  + apply H.
    apply IHn.
Qed.

(** 当然，_[f bot]_, _[f (f bot)]_, _[f (f (f bot))]_...这个序列也是单调不减的。*)
Lemma iter_S_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => f (Nat.iter n f bot)).
Proof.
  unfold increasing.
  intros.
  apply H.
  apply iter_bot_increasing.
  apply H.
Qed.

(** _[Kleene_LFix]_定义了Kleene最小不动点。*)
Definition Kleene_LFix
             {A: Type}
             `{CPOA: OmegaCompletePartialOrder_Setoid A}
             (f: A -> A): A :=
  omega_lub (fun n => Nat.iter n f bot).

(** 先证明，_[Kleene_LFix]_的计算结果确实是一个不动点。*)
Lemma Kleene_LFix_is_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    continuous f ->
    f (Kleene_LFix f) == Kleene_LFix f.
Proof.
  unfold Kleene_LFix; intros.
  rewrite H0 by (apply iter_bot_increasing; tauto).
  apply same_omega_ub_same_omega_lub'.
  + intros; unfold is_omega_ub.
    split; intros.
    - destruct n.
      * apply bot_is_least.
      * apply H1.
    - specialize (H1 (S n)).
      apply H1.
  + apply iter_S_bot_increasing.
    apply H.
  + apply iter_bot_increasing.
    apply H.
Qed.

(** 再证明，_[Kleene_LFix]_的计算结果是最小不动点。*)
Lemma Kleene_LFix_is_least_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    continuous f ->
    f a == a ->
    Kleene_LFix f <= a.
Proof.
  unfold Kleene_LFix; intros.
  pose proof iter_bot_increasing f H.
  pose proof oCPO_completeness (fun n => Nat.iter n f bot) H2.
  apply (is_omega_lub_tight H3).
  unfold is_omega_ub.
  induction n; simpl.
  + apply bot_is_least.
  + rewrite <- H1.
    apply H.
    apply IHn.
Qed.

Local Close Scope order_scope.

End KleeneFix.

Module StateRels_CPO.
Import KleeneFix.


(** 接下去我们将利用Kleene最小不动点定义While语句的程序语义中运行终止的情况。

    首先需要定义我们所需的OmegaCPO。在定义_[Class]_类型的值时，可以使用
    _[Intance]_关键字。如果_[Class]_中只有一个域并且_[Class]_的定义没有使用大括
    号包围所有域，那么这个域的定义就是整个_[Class]_类型的值的定义；否则_[Class]_
    类型的值应当像_[Record]_类型的值一样定义。*)
#[export] Instance R_while_fin {A B: Type}: Order (A -> B -> Prop) :=
  Sets.included.

#[export] Instance Equiv_while_fin {A B: Type}: Equiv (A -> B -> Prop) :=
  Sets.equiv.

(** 下面证明这是一个偏序关系。证明的时候需要展开上面两个二元关系（一个表示序关系
    另一个表示等价关系）。以序关系为例，此时需要将_[R_while_fin]_与_[order_rel]_
    全部展开，前者表示将上面的定义展开，后者表示将从_[Class Order]_取出
    _[order_rel]_域这一操作展开。其余的证明则只需用_[Sets_unfold]_证明集合相关的
    性质。*)
#[export] Instance PO_while_fin {A B: Type}: PartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    intros.
    rewrite H.
    reflexivity.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    intros.
    rewrite H, H0.
    reflexivity.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    intros.
    apply Sets_equiv_Sets_included; tauto.
Qed.

(** 下面再定义上确界计算函数与完备偏序集中的最小值。*)
#[export] Instance oLub_while_fin {A B: Type}: OmegaLub (A -> B -> Prop) :=
  Sets.indexed_union.

#[export] Instance Bot_while_fin {A B: Type}: Bot (A -> B -> Prop) :=
  ∅: A -> B -> Prop.

(** 下面证明这构成一个Omega完备偏序集。*)
#[export] Instance oCPO_while_fin {A B: Type}:
  OmegaCompletePartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + apply PO_while_fin.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_fin, oLub_while_fin; simpl.
    intros.
    split; intros.
    - apply Sets_included_indexed_union.
    - apply Sets_indexed_union_included.
      apply H0.
  + unfold is_least.
    unfold bot, order_rel, R_while_fin, Bot_while_fin; simpl.
    intros.
    apply Sets_empty_included.
Qed.

(** 额外需要补充一点：_[Equiv_while_fin]_确实是一个等价关系。先前Kleene不
    动点定理的证明中用到了这一前提。*)
#[export] Instance Equiv_equiv_while_fin {A B: Type}:
  Equivalence (@equiv (A -> B -> Prop) _).
Proof.
  apply Sets_equiv_equiv.
Qed.

(** 有时，Coq证明中需要展开上面这些定理，这可以使用下面的证明指令。*)

Ltac unfold_CPO_defs :=
  unfold order_rel, equiv, omega_lub, bot,
         R_while_fin, Equiv_while_fin, oLub_while_fin, Bot_while_fin. 

End StateRels_CPO.

(** 事实上，我们可以在Coq中证明所有的密集上的包含关系都是CPO。以下证明代码可以跳过。*)

Module Sets_CPO.
Import KleeneFix.


#[export] Instance R_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Order T :=
  Sets.included.

#[export] Instance Equiv_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Equiv T :=
  Sets.equiv.

#[export] Instance PO_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: PartialOrder_Setoid T.
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_sets, Equiv_sets; simpl.
    intros.
    rewrite H; reflexivity.
  + unfold Transitive.
    unfold equiv, order_rel, R_sets, Equiv_sets; simpl.
    intros.
    rewrite H, H0.
    reflexivity.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_sets, Equiv_sets; simpl.
    intros.
    apply Sets_equiv_Sets_included; tauto.
Qed.

#[export] Instance oLub_sets
           {T: Type}
           {_SETS: Sets.SETS T}: OmegaLub T :=
  Sets.indexed_union.

#[export] Instance Bot_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Bot T :=
  ∅: T.

#[export] Instance oCPO_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}:
  OmegaCompletePartialOrder_Setoid T.
Proof.
  split.
  + apply PO_sets.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_sets, oLub_sets; simpl.
    intros l _.
    split.
    - intros.
      apply Sets_included_indexed_union.
    - intros.
      apply Sets_indexed_union_included.
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_sets, Bot_sets; simpl.
    intros.
    apply Sets_empty_included.
Qed.

#[export] Instance Equiv_equiv_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}:
  Equivalence (@equiv T _).
Proof.
  apply Sets_equiv_equiv.
Qed.

Arguments R_sets: simpl never.
Arguments Equiv_sets: simpl never.
Arguments oLub_sets: simpl never.
Arguments Bot_sets: simpl never.

Ltac unfold_CPO_defs :=
  unfold order_rel, equiv, omega_lub, bot,
         R_sets, Equiv_sets, oLub_sets, Bot_sets. 

End Sets_CPO.

Module StateRels_Funcs.
Import KleeneFix Sets_CPO.


(** 下面开始证明_[F(X) = (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)]_这个函
    数的单调性与连续性。整体证明思路是：(1) _[F(X) = X]_是单调连续的；(2) 如果
    _[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也是单调连续的；(3) 如果_[F]_是单
    调连续的，那么_[G(X) = F(X) ∪ Y]_也是单调连续的；其中_[Y]_是给定的二元关系。

    下面证明前面提到的步骤(2)：如果_[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也
    是单调连续的。主结论为_[BinRel_concat_left_mono_and_continuous]_，其用到了两
    条下面的辅助引理以及前面证明过的复合函数单调连续性定理。*)

Lemma BinRel_concat_left_mono:
  forall (A B C: Type) (Y: A -> B -> Prop),
    mono (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold mono. unfold_CPO_defs.
  intros.
  rewrite H; reflexivity.
Qed.

Lemma BinRel_concat_left_continuous:
  forall (A B C: Type) (Y: A -> B -> Prop),
    continuous (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold continuous, increasing; unfold_CPO_defs.
  intros.
  apply Rels_concat_indexed_union_distr_l.
Qed.

Lemma BinRel_concat_left_mono_and_continuous:
  forall
    (A B C: Type)
    (Y: A -> B -> Prop)
    (f: (B -> C -> Prop) -> (B -> C -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => Y ∘ f X) /\ continuous (fun X => Y ∘ f X).
Proof.
  intros.
  destruct H.
  pose proof BinRel_concat_left_mono _ _ C Y.
  pose proof BinRel_concat_left_continuous _ _ C Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

(** 下面证明前面提到的步骤(3)：如果_[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也
    是单调连续的。主结论为_[union_right2_mono_and_continuous]_，其用到了两条下面
    的辅助引理以及前面证明过的复合函数单调连续性定理。*)

Lemma union_right2_mono:
  forall (A B: Type) (Y: A -> B -> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono; unfold_CPO_defs.
  Sets_unfold.
  intros R R' H st1 st2.
  specialize (H st1 st2).
  tauto.
Qed.

Lemma union_right2_continuous:
  forall (A B: Type) (Y: A -> B -> Prop),
    continuous (fun X => X ∪ Y).
Proof.
  intros.
  unfold continuous, increasing; unfold_CPO_defs.
  Sets_unfold.
  intros l H st1 st2.
  split; intros.
  + destruct H0 as [ [ n ? ] | ?].
    - exists n; tauto.
    - exists O; tauto.
  + destruct H0 as [n [? | ? ] ].
    - left.
      exists n; tauto.
    - tauto.
Qed.

Lemma union_right2_mono_and_continuous:
  forall
    (A B: Type)
    (Y: A -> B -> Prop)
    (f: (A -> B -> Prop) -> (A -> B -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => f X ∪ Y) /\ continuous (fun X => f X ∪ Y).
Proof.
  intros.
  destruct H.
  pose proof union_right2_mono _ _ Y.
  pose proof union_right2_continuous _ _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

End StateRels_Funcs.

Module DntSem_SimpleWhile5.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       KleeneFix Sets_CPO StateRels_Funcs.


(** 最终我们可以用Kleene不动点定义while语句运行终止的情况。

    首先给出语义定义。*)
Definition while_sem
             (D0: state -> bool)
             (D: state -> state -> Prop):
  state -> state -> Prop :=
  Kleene_LFix (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)).

(** 下面可以直接使用Kleene不动点定理证明上述定义就是我们要的最小不动点。*)
Theorem while_sem_is_least_fix: forall D0 D,
  (test_true(D0) ∘ D ∘ while_sem D0 D) ∪ test_false(D0) == while_sem D0 D /\
  (forall X,
    (test_true(D0) ∘ D ∘ X) ∪ test_false(D0) == X -> while_sem D0 D ⊆ X).
Proof.
  intros.
  assert (mono (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)) /\
          continuous (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0))).
  {
    apply union_right2_mono_and_continuous.
    apply BinRel_concat_left_mono_and_continuous.
    apply BinRel_concat_left_mono_and_continuous.
    split.
    + apply id_mono.
    + apply id_continuous.
  }
  destruct H.
  split.
  + apply (Kleene_LFix_is_fix (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)));
      tauto.
  + intros.
    apply (Kleene_LFix_is_least_fix (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)));
      tauto.
Qed.


End DntSem_SimpleWhile5.


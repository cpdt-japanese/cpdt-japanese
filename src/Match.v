(* Copyright (c) 2008-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(*
(** %\chapter{Proof Search in Ltac}% *)
 *)
(** %\chapter{Ltac による証明探索}% *)

(**
(* We have seen many examples of proof automation so far, some with tantalizing code snippets from Ltac, Coq's domain-specific language for proof search procedures.  This chapter aims to give a bottom-up presentation of the features of Ltac, focusing in particular on the Ltac %\index{tactics!match}%[match] construct, which supports a novel approach to backtracking search.  First, though, we will run through some useful automation tactics that are built into Coq.  They are described in detail in the manual, so we only outline what is possible. *)

これまで多くの証明の自動化の例を見てきましたが、
Coqの証明探索の手続きのためのドメイン固有言語(domain-specific language)である Ltac に
よって、一部のコードの断片は魅力的なものでした(some with tantalizing code snippets)。
この章は、Ltac の機能をボトムアップに示すことを目標に、
特に、バックトラッキング探索のための独創的なアプローチをサポートする、
Ltac の %\index{tactics!match}%[match] 構成要素(construct)に焦点をあてます。
最初に、Coqに組み込まれている便利な自動化タクティクをいくつか実行します。
それらの詳細はマニュアルに記載されているので、出来ることを概説するだけにします。
 *)

(*
(** * Some Built-In Automation Tactics *)
 *)
(** * 組み込み 自動化タクティク *)

(**
(* A number of tactics are called repeatedly by [crush].  The %\index{tactics!intuition}%[intuition] tactic simplifies propositional structure of goals.  The %\index{tactics!congruence}%[congruence] tactic applies the rules of equality and congruence closure, plus properties of constructors of inductive types.  The %\index{tactics!omega}%[omega] tactic provides a complete decision procedure for a theory that is called %\index{linear arithmetic}%quantifier-free linear arithmetic or %\index{Presburger arithmetic}%Presburger arithmetic, depending on whom you ask.  That is, [omega] proves any goal that follows from looking only at parts of that goal that can be interpreted as propositional formulas whose atomic formulas are basic comparison operations on natural numbers or integers, with operands built from constants, variables, addition, and subtraction (with multiplication by a constant available as a shorthand for addition or subtraction).
*)

多くのタクティクが [crush] によって繰り返し呼び出されます。

%\index{tactics!intuition}%[intuition] タクティクは、
ゴールの命題論理的構造を簡略化(simplifies)します。

%\index{tactics!congruence}%[congruence] タクティクは、
等式と合同閉包(congruence closure)のルールに加え、帰納型のコンストラクタの属性を適用します。

%\index{tactics!omega}%[omega] タクティクは、あなたの求めに応じて(depending on whom you ask)、
%\index{linear arithmetic}%quantifier-free linear arithmetic 量化子のない線形算術、または、
%\index{Presburger arithmetic}%Presburger arithmetic プレスバーガー算術と呼ばれる
理論に対する完全な決定手続きを提供します。

すなわち [omega] は、
その原始式(atomic formulas)が、自然数または整数を基本的な比較演算の対象とし、
そのオペランドが定数、変数、加算および減算から構成された、
（加算または減算の省略形として利用可能な定数による乗算を含む）
命題論理の式として解釈されることのできる、
ゴールの部分のみを見ることに続く
(that follows from looking only at parts of that goal)
任意のゴールを証明します。

(*
   The %\index{tactics!ring}%[ring] tactic solves goals by appealing to the axioms of rings or semi-rings (as in algebra), depending on the type involved.  Coq developments may declare new types to be parts of rings and semi-rings by proving the associated axioms.  There is a similar tactic [field] for simplifying values in fields by conversion to fractions over rings.  Both [ring] and [field] can only solve goals that are equalities.  The %\index{tactics!fourier}%[fourier] tactic uses Fourier's method to prove inequalities over real numbers, which are axiomatized in the Coq standard library.
*)

%\index{tactics!ring}%[ring] は、
関与する型に依存して、(代数のように)環まはた半環の公理を適用することによって、
ゴールを解きます。
Coqの開発では、関連する公理を証明することによって、
新しい型を環と半環の一部として宣言することができます。
環における分数に変換することで、
体の値を簡略化するための同様のタクティク [field] があります。
[ring] と [field] の両方は、等式のゴールだけを解くことができます。
%\index{tactics!fourier}%[fourier] タクティクは、
Coq標準ライブラリで公理化された実数の不等式を証明するフーリエの方法を使用します。

(*
   The%\index{setoids}% _setoid_ facility makes it possible to register new equivalence relations to be understood by tactics like [rewrite].  For instance, [Prop] is registered as a setoid with the equivalence relation "if and only if."  The ability to register new setoids can be very useful in proofs of a kind common in math, where all reasoning is done after "modding out by a relation."
*)

The%\index{setoids}% _setoid_ の手法(facility)は、
[rewrite] のようなタクティクによって理解される
新しい等価関係(equivalence relations)を
登録することを可能にします。

たとえば [Prop] は、"if and only if" の等価関係を setoid として登録されています。
新しい setoid を登録する能力は、
すべての推論(reasoning)が、
「関係によって改変された(modding out by a relation)」後に実行される箇所において、
数学で一般的な種類の証明において非常に有用です。

(*
   There are several other built-in "black box" automation tactics, which one can learn about by perusing the Coq manual.  The real promise of Coq, though, is in the coding of problem-specific tactics with Ltac. *)

Coq マニュアルを熟読することで学ぶことのできる、
組み込みの「ブラックボックス」な自動化タクティクがあります。

Coqの本当の約束事は、Ltacを使って、
問題に特化したタクティクのコーディングのなかにあります。
 *)

(*
(** * Ltac Programming Basics *)
 *)
(** * Ltac プログラミングの基礎 *)

(**
(* We have already seen many examples of Ltac programs.  In the rest of this chapter, we attempt to give a thorough introduction to the important features and design patterns.

   One common use for [match] tactics is identification of subjects for case analysis, as we see in this tactic definition. *)

すでに Ltac プロラムの多くの例を見てきました。
本章の残りでは、重要な機能とデザインパターンを徹底的に紹介しようとします。

[match] タクティクのひとつの共通の使い方は、
このタクティクの定義にあるように、
条件分析(case analysis)のための内容の識別です。
 *)

(* begin thide *)
Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.
(* end thide *)

(**
(* The tactic checks if the conclusion is an [if], [destruct]ing the test expression if so.  Certain classes of theorem are trivial to prove automatically with such a tactic. *)

このタクティクは結論が [if] かどうかチェックし、もしそうなら、
条件式(test expression)を [destruct] します。
ある特定の種類の定理は、このようなタクティクによって、
自動的に証明することが簡単(trivial)です。
 *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
(* begin thide *)
  intros; repeat find_if; constructor.
Qed.
(* end thide *)

(**
(* The %\index{tactics!repeat}%[repeat] that we use here is called a%\index{tactical}% _tactical_, or tactic combinator.  The behavior of [repeat t] is to loop through running [t], running [t] on all generated subgoals, running [t] on _their_ generated subgoals, and so on.  When [t] fails at any point in this search tree, that particular subgoal is left to be handled by later tactics.  Thus, it is important never to use [repeat] with a tactic that always succeeds.

   Another very useful Ltac building block is%\index{context patterns}% _context patterns_. *)

ここで使った %\index{tactics!repeat}%[repeat] は、
%\index{tactical}% _tactical_ タクティカル または タクティク・コンビネータ(tactic combinator)
と呼ばれます。
[repeat t] の振る舞いは、[t] を実行し、
すべての生成されたサブゴールに [t] を実行し、
＿それら＿ が生成したサブゴールに [t] を実行し、というぐあいに、
繰り返し続けることです。
この探索木の任意の点で [t] が失敗したとき、その特定のサブゴールは、
後のタクティクのによって扱われるために残されます。
なので、いつも成功するタクティクと一緒に [repeat] を使用しないことが重要です。
(* suhara: 繰り返しが終わらなくなるから *)

他のとても便利な Ltac の構成要素(building block)は、
%\index{context patterns}% _context patterns_ コンテキスト・パターン
です。
 *)

(* begin thide *)
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.
(* end thide *)

(**
(* The behavior of this tactic is to find any subterm of the conclusion that is an [if] and then [destruct] the test expression.  This version subsumes [find_if]. *)

このタクティクの振る舞いは、結論の
[if] であり、その後に条件式を [destruct] する任意の部分項(subterm)を見つけることです。
このバージョンは [find_if] を含みます。
 *)

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
(* begin thide *)
  intros; repeat find_if_inside; constructor.
Qed.
(* end thide *)

(**
(* We can also use [find_if_inside] to prove goals that [find_if] does not simplify sufficiently. *)

[find_if-inside] を
[find_if] が十分に簡約できなかったゴールを証明するために使うことができます。
*)

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
(* begin thide *)
  intros; repeat find_if_inside; reflexivity.
Qed.
(* end thide *)

(**
(* Many decision procedures can be coded in Ltac via "[repeat match] loops."  For instance, we can implement a subset of the functionality of [tauto]. *)

多くの決定性の手続きは 「[repeat match] ループ」によって Ltac で記述されます。
たとえば、[tauto] のサブセットの機能を実装することができます。
 *)

(* begin thide *)
Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => destruct H
	   | [ H : _ /\ _ |- _ ] => destruct H
	   | [ H : _ \/ _ |- _ ] => destruct H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
	 end.
(* end thide *)

(**
(* Since [match] patterns can share unification variables between hypothesis and conclusion patterns, it is easy to figure out when the conclusion matches a hypothesis.  The %\index{tactics!exact}%[exact] tactic solves a goal completely when given a proof term of the proper type.

   It is also trivial to implement the introduction rules (in the sense of %\index{natural deduction}%natural deduction%~\cite{TAPLNatDed}%) for a few of the connectives.  Implementing elimination rules is only a little more work, since we must give a name for a hypothesis to [destruct].

   The last rule implements modus ponens, using a tactic %\index{tactics!specialize}%[specialize] which will replace a hypothesis with a version that is specialized to a provided set of arguments (for quantified variables or local hypotheses from implications).  By convention, when the argument to [specialize] is an application of a hypothesis [H] to a set of arguments, the result of the specialization replaces [H].  For other terms, the outcome is the same as with [generalize]. *)

[match] のパターンはユニフィケーション変数を仮定と結論のパターンの間で共有することができ、
結論が仮説といつマッチするかを把握することは容易です。
%\index{tactics!exact}%[exact] タクティクは、適切な型の証明項が与えられているとき、
ゴールを完全に解きます。

（\index{natural deduction}%natural deduction%~\cite{TAPLNatDed}% 自然演繹の意味において）
いくつかの結合子(* suhara: ∧と∨ *)についての導入のルールを実装することは自明です。

最後のルールは、
仮説を与えられた引数の集合（量化された変数、または、含意による局所的仮説のため）
に特化したバージョンに置き換える
%\index{tactics!specialize}%[specialize] タクティクを使って
三段論法(modus ponens)を実装します。
慣例によって、
[specialize] への引数が一連の引数に対する仮説 [H] の適用である場合、そ
の特殊化の結果が [H] に置き換えられます。
 他の項については、結果は [generalize] と同じです。
 *)

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
(* begin thide *)
    my_tauto.
  Qed.
(* end thide *)
End propositional.

(**
(* It was relatively easy to implement modus ponens, because we do not lose information by clearing every implication that we use.  If we want to implement a similarly complete procedure for quantifier instantiation, we need a way to ensure that a particular proposition is not already included among our hypotheses.  To do that effectively, we first need to learn a bit more about the semantics of [match].
*)

すべての含意(implication)を消すこと(clearing)によって情報を失なわないので、
三段論法の実装をするのは比較的簡単です。
もし、量化された含意についての同様の完全な手続きを実装するなら、
特定の命題がまだ仮説に含まれていないことを保証する方法が必要です。
これを効果的に行うには、最初に [match] の意味についてもう少し学ぶ必要があります。

(*
It is tempting to assume that [match] works like it does in ML.  In fact, there are a few critical differences in its behavior.  One is that we may include arbitrary expressions in patterns, instead of being restricted to variables and constructors.  Another is that the same variable may appear multiple times, inducing an implicit equality constraint.
*)

マッチはMLのように動作すると想定するのは魅力的です。 
実際、その動作にはいくつかの重要な違いがあります。
ひとつは、変数やコンストラクタに制限されることなく、パターンに任意の式を含めることです。 
もうひとつは、同じ変数が複数回現れることがあり、暗黙に等値の制約を含むことです。

(*
There is a related pair of two other differences that are much more important than the others.  The [match] construct has a _backtracking semantics for failure_.  In ML, pattern matching works by finding the first pattern to match and then executing its body.  If the body raises an exception, then the overall match raises the same exception.  In Coq, failures in case bodies instead trigger continued search through the list of cases.
*)

他のふたつの違いは、他のものよりはるかに重要です。
[match] 構文は、＿失敗によるバックトラッキングの意味＿ を持っています。 
MLでは、パターンマッチングは、一致させる最初のパターンを見つけてから、
その本体を実行することによって動作します。 
本体が例外を発生させた場合、全体の一致は同じ例外を発生させます。
Coqでは、ケース条件本体の失敗は、代わりにケースのリストを通じて検索を続行します。

(*
For instance, this (unnecessarily verbose) proof script works: *)

例えば、この（不必要で冗長な）証明のスクリプトはこのように動きます。
 *)

Theorem m1 : True.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
(* begin thide *)
Qed.
(* end thide *)

(**
(* The first case matches trivially, but its body tactic fails, since the conclusion does not begin with a quantifier or implication.  In a similar ML match, the whole pattern-match would fail.  In Coq, we backtrack and try the next pattern, which also matches.  Its body tactic succeeds, so the overall tactic succeeds as well.

   The example shows how failure can move to a different pattern within a [match].  Failure can also trigger an attempt to find _a different way of matching a single pattern_.  Consider another example: *)

最初のケースは簡単に一致しますが、その結論は限定子や含意から始まるわけではないので、
その本体のタクティクは失敗します。
同様のMLのマッチでは、パターンマッチ全体が失敗します。
Coqでは、次のパターンを取り戻して試してみます。これも一致します。
その本体のタクティクは成功するので、全体のタクティクも成功します。

この例では、失敗が [match] 内の別のパターンにどのように移動するかを示しています。
失敗はまた、単一のパターンにマッチする異なる方法を見つける試みを引き起こします。

別の例を考えてみましょう。
 *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.

  (**
(* Coq prints "[H1]".  By applying %\index{tactics!idtac}%[idtac] with an argument, a convenient debugging tool for "leaking information out of [match]es," we see that this [match] first tries binding [H] to [H1], which cannot be used to prove [Q].  Nonetheless, the following variation on the tactic succeeds at proving the goal: *)
  
Coq は [H1] を印刷します。
(* suhara: Goalが仮定H1と同じと言っているが、GoalがQで、仮定は H:P, H0:Q, H1:R である。 *)
ひとつの引数を取って %\index{tactics!idtac}%[idtac] を適用することは、
[match] 情報を取り出すための便利なデバッキングツールです。
この [match] は最初に [H] を [H1] に束縛しようとしますが、
[H1] は [Q] を証明するために使用できません。
(* suhara: H1 は H0 *)
それにもかかわらず、タクティクの次のバリエーションはゴールを証明するのに成功します：
   *)

(* begin thide *)
  match goal with
    | [ H : _ |- _ ] => exact H
  end.
Qed.
(* end thide *)

(**
(* The tactic first unifies [H] with [H1], as before, but [exact H] fails in that case, so the tactic engine searches for more possible values of [H].  Eventually, it arrives at the correct value, so that [exact H] and the overall tactic succeed. *)

タクティクは最初に [H] と [H1] (* suhara: [H] とするべき *) をユニファイします、
その場合は [exact H] が失敗するため、戦術エンジンは [H] の可能な値をさらに検索します。
最終的には、正しい値 (* suhara: [H0] *) に到達するので、[exact H] と全体のタクティクは成功します。
 *)

(**
(* Now we are equipped to implement a tactic for checking that a proposition is not among our hypotheses: *)

では、命題が私たちの仮説の中にないことを確認するためのタクティクを実装する用意ができました：
 *)

(* begin thide *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.
(* end thide *)

(**
(* We use the equality checking that is built into pattern-matching to see if there is a hypothesis that matches the proposition exactly.  If so, we use the %\index{tactics!fail}%[fail] tactic.  Without arguments, [fail] signals normal tactic failure, as you might expect.  When [fail] is passed an argument [n], [n] is used to count outwards through the enclosing cases of backtracking search.  In this case, [fail 1] says "fail not just in this pattern-matching branch, but for the whole [match]."  The second case will never be tried when the [fail 1] is reached.
*)

パターン・マッチングにに組み込まれている等価性検査(equality checking)を使用して、
命題に正確に一致する仮説があるかどうかを調べます。もしそうなら、
%\index{tactics!fail}%[fail] タクティクを使用します。 

引数がなければ、期待通りに、[fail] は通常のタクティクの失敗を通知します。
[fail] に引数 [n] が渡されると、
[n] は、バックトラック探索の囲む条件(case)を通して外側に向かってカウントするように使用されます。
この場合、[fail 1]は、「パターン・マッチングの分岐ではなく、[macth] 全体を失敗させる」
ことを示します。
[fail 1] に達すると、2番目の条件(case)は決して試行されません。

(*
This second case, used when [P] matches no hypothesis, checks if [P] is a conjunction.  Other simplifications may have split conjunctions into their component formulas, so we need to check that at least one of those components is also not represented.  To achieve this, we apply the %\index{tactics!first}%[first] tactical, which takes a list of tactics and continues down the list until one of them does not fail.  The [fail 2] at the end says to [fail] both the [first] and the [match] wrapped around it.
*)

第2の条件(case)は、[P] が仮説と一致しないときに使用され、
[P] が連言(conjunction)であるかどうかをチェックします。

他の簡略化(simplification)では連言(conjunction)をその成分の式(component formula)
に分割することがあるため、
これらの成分の少なくともひとつも表現されていない
(* suhara: 成分の式がどれも「仮説を使って」表現されてない *)
ことを確認する必要があります。

これを達成するために、 %\index{tactics!first}%[first] タクティカルを適用します。
これはタクティクのリストを取り、
それらのひとつが失敗しないまで (* suhara: 最初のひとつが成功するまで *)
リストを続けます。
最後の [fail 2] は、[first] とその周囲に巻き込まれた [match] の両方が失敗することを示します。

(*
The body of the [?P1 /\ ?P2] case guarantees that, if it is reached, we either succeed completely or fail completely.  Thus, if we reach the wildcard case, [P] is not a conjunction.  We use %\index{tactics!idtac}%[idtac], a tactic that would be silly to apply on its own, since its effect is to succeed at doing nothing.  Nonetheless, [idtac] is a useful placeholder for cases like what we see here.
*)

[?P1 /\ ?P2] の場合のボディ(* suhara: [=>] の右辺 *) は、
到達すれば完全に成功するか完全に失敗するかを保証します。

ワイルドカードの場合、[P] は連言ではありませんから、
%\index {tactics!idtac}％[idtac] を使用します。
これは、何もしないことで成功する効果があるため、単独で適用することは愚かなタクティクです。
それにもかかわらず、[idtac] は、ここで見ているような場合に便利な代用品(placeholder)です。

(*
With the non-presence check implemented, it is easy to build a tactic that takes as input a proof term and adds its conclusion as a new hypothesis, only if that conclusion is not already present, failing otherwise. *)

存在しないことのチェックを実装したことによって、
入力として証明項をとり、結論がまだ存在しない場合だけ、新しい仮説としてその結論を加え、
さもなければ失敗するタクティクを作ることは簡単です。
 *)

(* begin thide *)
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.
(* end thide *)

(**
(* We see the useful %\index{tactics!type of}%[type of] operator of Ltac.  This operator could not be implemented in Gallina, but it is easy to support in Ltac.  We end up with [t] bound to the type of [pf].  We check that [t] is not already present.  If so, we use a [generalize]/[intro] combo to add a new hypothesis proved by [pf].  The tactic %\index{tactics!generalize}%[generalize] takes as input a term [t] (for instance, a proof of some proposition) and then changes the conclusion from [G] to [T -> G], where [T] is the type of [t] (for instance, the proposition proved by the proof [t]).
*)

Ltacの有用な %\index{tactics!type}%[type of] 演算子があります。
この演算子はGallinaでは実装できませんでしたが、Ltacでサポートするのは簡単です。

最終的に [t] は [pf] の型を束縛します。
[t] がまだ存在していないことを確認します。
もしそうなら、[generalize] / [intro] の組み合わせを使って、
[pf] によって証明された新しい仮説を追加します。 

タクティク %\index{tactics!generalize}%[generalize] は、
入力として [t]（例えば命題の証明）をとり、
[T] が [t] の型であるとき、[G] から [T -> G] に結論を変えます。

(*
   With these tactics defined, we can write a tactic [completer] for, among other things, adding to the context all consequences of a set of simple first-order formulas. *)

これらの定義されたタクティクで、
単純な一階論理の式の集合のすべての結果(consequence)
をコンテキストに加えるためのタクティク [completer] を書くことができます。
 *)

(* begin thide *)
Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro    (* これは P x -> S x もintroする。 *)

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.
(* end thide *)

(**
(* We use the same kind of conjunction and implication handling as previously.  Note that, since [->] is the special non-dependent case of [forall], the fourth rule handles [intro] for implications, too.
*)
前の扱ったのと同じ種類の連言と含意を使います。
[->] は [forall] の(* suhara: 全称量化の変数に *) 依存しない特別な場合なので、
第4のルールでは [intro] で含意も扱うことに注意してください。

(*
   In the fifth rule, when we find a [forall] fact [H] with a premise matching one of our hypotheses, we add the appropriate instantiation of [H]'s conclusion, if we have not already added it.
*)

第5のルールでは、私たちが仮説のひとつにマッチする前提で [forall] (を含む)事実 [H] を見つけたら、
まだ追加していなければ、[H] の結論を適切に具体化(instantiation)したものを追加します。

(*
   We can check that [completer] is working properly, with a theorem that introduces a spurious variable whose didactic purpose we will come to shortly. *)

偽作(spurious)の変数を導入する、説明上の目的(didactic purpose)の定理を用いて、
すぐに、[completer] が正しく働いていることを確認することができます。
*)

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
(* begin thide *)
    completer.
    (** [[
  y : A
  x : A
  H : P x
  H0 : Q x
  H3 : R x
  H4 : S x
  ============================
   S x
   ]]
   *)

    assumption.
  Qed.
(* end thide *)
End firstorder.

(**
(* We narrowly avoided a subtle pitfall in our definition of [completer].  Let us try another definition that even seems preferable to the original, to the untrained eye.  (We change the second [match] case a bit to make the tactic smart enough to handle some subtleties of Ltac behavior that had not been exercised previously.) *)

かろうじて [completer] の定義における微妙な落とし穴を避けていました。
慣れていない目には、オリジナルよりも魅力的に見える別の定義を試してみましょう。

（2番目の [match] の場合を少し変更して、
これまでに行使されていなかったLtacの動作の微妙な部分を処理するのに
十分スマートなタクティクにしました）。
 *)

(* begin thide *)
Ltac completer' :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : ?P /\ ?Q |- _ ] => destruct H
(* suhara: この部分は影響しない。
             ;
             repeat match goal with
                      | [ H' : P /\ Q |- _ ] => clear H'
                    end
*)
           | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H') (* ！！！ *)
           (* suhara: ↑は、H2 : forall x, R x -> S x. や H1 .. にもマッチしてしまう。 *)
           (* specialize (H1 y) や specialize (H2 y) が実行されてしまう。  *)
           (* x より y のほうが、前にあるのもミソである。 *)
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.
(* end thide *)

(*
(** The only other difference is in the modus ponens rule, where we have replaced an unused uni
fication variable [?Q] with a wildcard.  Let us try our example again with this version: *)

他の唯一の違いは、未使用のユニフィケーション変数 [?Q] をワイルドカードに置き換えた三段論法
(modus ponens) のルールにあります。 このバージョンで再び例を試してみましょう：
 *)

Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall (y x : A), P x -> S x.
(*  suhara: completer' とおなじことを起こす例。
    intros y x H.
    specialize (@H1 y).
    specialize (@H2 y).
    Restart.
*)
    completer'.
    (** [[
  y : A
  H1 : P y -> Q y /\ R y
  H2 : R y -> S y
  x : A
  H : P x
  ============================
   S x
   ]]
(*
   The quantified theorems have been instantiated with [y] instead of [x], reducing a provable goal to one that is unprovable.  Our code in the last [match] case for [completer'] is careful only to instantiate quantifiers along with suitable hypotheses, so why were incorrect choices made?
   *)

証明できていたゴールを証明できないものに変形(reducing)することで、
量化された定理は、[x]ではなく[y]で具体化されてしまいます。

[completer'] のための最後の [match] の条件は、
適切な仮説とともに量化子を具体化するだけに注意深くしています。
なぜ間違った選択が行われたのですか？
     *)
  Abort.
(* end thide *)
End firstorder'.

(**
(* A few examples should illustrate the issue.  Here we see a [match]-based proof that works fine: *)

いくつかの例が問題を説明しているはずです。ここでは、
[match]ベースの証明がうまくいくのを見ています：
 *)

Theorem t1 : forall x : nat, x = x.
  match goal with
    | [ |- forall x, _ ] => trivial
  end.
(* begin thide *)
Qed.
(* end thide *)

(** This one fails. *)

(* begin thide *)
Theorem t1' : forall x : nat, x = x.
(** %\vspace{-.25in}%[[
  match goal with
    | [ |- forall x, ?P ] => trivial
  end.
]]

<<
User error: No matching clauses for match goal
>>
*)

Abort.                                      (* suhara: Coq 8.5では解けてしまう。 *)
(* end thide *)

(**
(* The problem is that unification variables may not contain locally bound variables.  In this case, [?P] would need to be bound to [x = x], which contains the local quantified variable [x].  By using a wildcard in the earlier version, we avoided this restriction.  To understand why this restriction affects the behavior of the [completer] tactic, recall that, in Coq, implication is shorthand for degenerate universal quantification where the quantified variable is not used.  Nonetheless, in an Ltac pattern, Coq is happy to match a wildcard implication against a universal quantification.
*)

問題は、ユニフィケーション変数にローカルに束縛された変数が含まれないことです。

(* suhara: forall x, Q や fun x => F の x のこと。P は、
xが含まれている Q や F とマッチしないが、ワイルドカードならマッチする。 *)

この場合、[?P] はローカルな量化変数 [x] を含む [x = x] に束縛される必要があります。
以前のバージョンでワイルドカードを使用することで、この制限は回避されました。
なぜこの制限が [completer] タクティクの振る舞いに影響を与えるのかを理解するために、
Coqでは、含意が縮退(degenerate)した全称量化の略記であることを思い出してください。
それにもかかわらず、Ltacパターンでは、
Coqはワイルドカードの含意と全称量化のマッチに満足してしまいます。

(*
   The Coq 8.2 release includes a special pattern form for a unification variable with an explicit set of free variables.  That unification variable is then bound to a function from the free variables to the "real" value.  In Coq 8.1 and earlier, there is no such workaround.  We will see an example of this fancier binding form in Section 15.5.
*)

Coq 8.2リリースには、明示的な自由変数の集合を持つユニフィケーション変数用の
特別なパターン形式が含まれています。
そのユニフィケーション変数は、
自由変数から「実」値への関数に束縛されます。
Coq 8.1以前では、このような回避策はありません。
15.5節でこの手の込んだバインディングフォームの例を見ていきます。

(*
   No matter which Coq version you use, it is important to be aware of this restriction.  As we have alluded to, the restriction is the culprit behind the surprising behavior of [completer'].  We unintentionally match quantified facts with the modus ponens rule, circumventing the check that a suitably matching hypothesis is available and leading to different behavior, where wrong quantifier instantiations are chosen.  Our earlier [completer] tactic uses a modus ponens rule that matches the implication conclusion with a variable, which blocks matching against non-trivial universal quantifiers.
*)

どのCoqバージョンを使用していても、この制限に注意することが重要です。
すでに示唆したように、その制限は [completer'] の驚くべき振る舞いの背後にある原因です。

(* suhara: match の
「| [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H') 」
の H が、
「H  : forall p : P, _        」 と解釈されて、
「H2 : forall x,    R x -> S x」 とマッチしてしまう。ワイルドカードなので変数xをふくんでよい。
そのため、specialize (H1 y) が実行されてしまう。
y のほうが x より前にあるのもミソである。
*)

私たちは間違って量化された事実を三段論法と突き合わせ、
適切に一致する仮説が利用可能であり、
誤った量化子の具体化が選択された異なる行動につながるというチェックを回避します。
私たちの初期の [completer] タクティクでは、
含意の結論と変数を組み合わせた三段論法を使用しています。

(*
   Actually, the behavior demonstrated here applies to Coq version 8.4, but not 8.4pl1.  The latter version will allow regular Ltac pattern variables to match terms that contain locally bound variables, but a tactic failure occurs if that variable is later used as a Gallina term. *)

実際、ここで示した動作はCoqバージョン8.4に適用されますが、8.4pl1には適用されません。
後者のバージョンでは、通常のLtacパターン変数がローカルに束縛された変数を含む項に
一致することができますが、
その変数が後にGallina項として使用されると、タクティクの失敗が発生します。
 *)

(*
(** * Functional Programming in Ltac *)
 *)
(** * Ltac による関数プログラミング *)

(* EX: Write a list length function in Ltac. *)

(**
(* Ltac supports quite convenient functional programming, with a Lisp-with-syntax kind of flavor.  However, there are a few syntactic conventions involved in getting programs to be accepted.  The Ltac syntax is optimized for tactic-writing, so one has to deal with some inconveniences in writing more standard functional programs.
*)

Ltacは、構文付きLisp(Lisp-with-syntax)風の非常に便利な関数型プログラミングをサポートしています。
受け入れてもらうための、プログラムに関係するいくつかの構文上の慣習があります。
Ltacの構文はタクティクの記述のために最適化されているので、
より標準的な関数プログラムを書く際にいくつかの不都合を扱わなければなりません。

(*
   To illustrate, let us try to write a simple list length function.  We start out writing it just as in Gallina, simply replacing [Fixpoint] (and its annotations) with [Ltac].
*)

説明のために、簡単なリストの長さを求める関数を記述しましょう。
あたかもGallinaのように、[Fixtpoint]（とその注釈(annotation)）
を[Ltac]に置き換えて書き始めます。

   [[
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ls' => S (length ls')
  end.
]]

<<
Error: The reference ls' was not found in the current environment
>>
(*
   At this point, we hopefully remember that pattern variable names must be prefixed by question marks in Ltac.
*)
この時点で、Ltacでは、
パターン変数の名前の先頭に疑問符を付ける必要があることを覚えておいてください。

   [[
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => S (length ls')
  end.
]]

<<
Error: The reference S was not found in the current environment
>>

(*
   The problem is that Ltac treats the expression [S (length ls')] as an invocation of a tactic [S] with argument [length ls'].  We need to use a special annotation to "escape into" the Gallina parsing nonterminal.%\index{tactics!constr}% *)

問題は、Ltacが式 [S (length ls')] を引数 [length ls'] を持つタクティク [S] の呼び出しとして
扱うことです。
Gallinaの非終端記号の構文解析を「エスケープ」するために特別なアノテーションを
使用する必要があります。 %\index{tactics!constr}% 
*)

(* begin thide *)
(* begin hide *)
Definition red_herring := O.
(* end hide *)
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => constr:(S (length ls'))
  end.

(**
(* This definition is accepted.  It can be a little awkward to test Ltac definitions like this one.  Here is one method. *)

この定義は受け入れられます。
このようなLtacの定義をテストするのはちょっと厄介です。
ひとつの方法があります。
 *)

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
  (** [[
  n := S (length (2 :: 3 :: nil)) : nat
  ============================
   False
   ]]

(*
   We use the %\index{tactics!pose}%[pose] tactic, which extends the proof context with a new variable that is set equal to a particular term.  We could also have used [idtac n] in place of [pose n], which would have printed the result without changing the context.
*)

特定の項に、等号でセットされた(set equal to)、新しい変数でもって、証明のコンテキストを拡張する
%\index{tactics!pose}%[pose] タクティクを使用します。

[pose n] の代わりに [idtac n] を使用することもできました。
これは、コンテキストを変更せずに結果を出力します。

(*
   The value of [n] only has the length calculation unrolled one step.  What has happened here is that, by escaping into the [constr] nonterminal, we referred to the [length] function of Gallina, rather than the [length] Ltac function that we are defining. *)

[n]の値は、長さの計算の1ステップだけ展開されます。
ここで起こったことは、[constr] 非終端記号にエスケープすることによって、
私たちが定義している Ltac関数 [length] は、Gallinaの関数 [length] を参照したことです。
   *)

Abort.

Reset length.
(* begin hide *)
Reset red_herring.
(* end hide *)

(**
(* The thing to remember is that Gallina terms built by tactics must be bound explicitly via [let] or a similar technique, rather than inserting Ltac calls directly in other Gallina terms. *)
覚えておくべきことは、タクティクによって作られた Gallina項は、
Ltac 呼び出しを他の Gallina項 に直接挿入するのではなく、
[let] または同様の手法を介して明示的に束縛する必要があるということです。
*)

(* begin hide *)
Definition red_herring := O.
(* end hide *)
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
  (** [[
  n := 3 : nat
  ============================
   False
   ]]
   *)

Abort.
(* end thide *)

(* EX: Write a list map function in Ltac. *)

(* begin hide *)
(* begin thide *)
Definition mapp := (map, list).
(* end thide *)
(* end hide *)

(**
(* We can also use anonymous function expressions and local function definitions in Ltac, as this example of a standard list [map] function shows. *)

標準のリストの [map] 関数のこの例が示すように、
Ltacで無名関数の式とローカルな関数定義を使用することもできます。
 *)

(* begin thide *)
Ltac map T f :=
  let rec map' ls :=
    match ls with
      | nil => constr:(@nil T)
      | ?x :: ?ls' =>
        let x' := f x in
          let ls'' := map' ls' in
            constr:(x' :: ls'')
    end in
  map'.

(**
(* Ltac functions can have no implicit arguments.  It may seem surprising that we need to pass [T], the carried type of the output list, explicitly.  We cannot just use [type of f], because [f] is an Ltac term, not a Gallina term, and Ltac programs are dynamically typed.  The function [f] could use very syntactic methods to decide to return differently typed terms for different inputs.  We also could not replace [constr:(@nil T)] with [constr:nil], because we have no strongly typed context to use to infer the parameter to [nil].  Luckily, we do have sufficient context within [constr:(x' :: ls'')].

Sometimes we need to employ the opposite direction of "nonterminal escape," when we want to pass a complicated tactic expression as an argument to another tactic, as we might want to do in invoking %\coqdocvar{%#<tt>#map#</tt>#%}%. *)

Ltac関数は暗黙の引数を持つことができません。
出力リストの要素の型(carried type of the output list)である[T]を
明示的に渡す必要があることは驚くようです。
[f] は Gallinaの項ではなくLtacの項であり、
Ltacプログラムは動的に型付けされているので、[type of f] を使うことはできません。
関数 [f] は、非常に構文的な方法を使用して、
異なる入力に対して異なる型の項を返すことを決定することができます。
[constr:(@nil T)] を [constr:nil] に置き換えることもできませんでした。
これは、パラメータを [nil] に推論するために使用する強く型付けされたコンテキストがないためです。
幸いにも、[constr:(x' :: ls'')] の中には十分なコンテキストを持っています。

複雑なタクティクの表現を別のタクティクに引数として渡したいときには、
%\coqdocvar{%#<tt>#map#</tt>#%}% を呼び出す際にしたように、
「非終端のエスケープ」の反対の方向を採用する必要がある場合があります。
 *)

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:(x, x)) (1 :: 2 :: 3 :: nil) in
    pose ls.
  (** [[
  l := (1, 1) :: (2, 2) :: (3, 3) :: nil : list (nat * nat)
  ============================
   False
   ]]
   *)

Abort.
(* end thide *)

(**
(* Each position within an Ltac script has a default applicable non-terminal, where [constr] and [ltac] are the main options worth thinking about, standing respectively for terms of Gallina and Ltac.  The explicit colon notation can always be used to override the default non-terminal choice, though code being parsed as Gallina can no longer use such overrides.  Within the [ltac] non-terminal, top-level function applications are treated as applications in Ltac, not Gallina; but the _arguments_ to such functions are parsed with [constr] by default.  This choice may seem strange, until we realize that we have been relying on it all along in all the proof scripts we write!  For instance, the [apply] tactic is an Ltac function, and it is natural to interpret its argument as a term of Gallina, not Ltac.  We use an [ltac] prefix to parse Ltac function arguments as Ltac terms themselves, as in the call to %\coqdocvar{%#<tt>#map#</tt>#%}% above.  For some simple cases, Ltac terms may be passed without an extra prefix.  For instance, an identifier that has an Ltac meaning but no Gallina meaning will be interpreted in Ltac automatically.
*)

Ltacスクリプトの中の各位置には、
既定の適用可能な非終端記号があります。
ここで、[constr]と[ltac]は、
GallinaとLtacの条件をそれぞれ念頭に置く価値のある主要なオプションです。
明示的なコロン表記は、既定の非終端選択を無効にするためにいつでも使用することができますが、
Gallinaとして解析されるコードではこのような上書きは使用できなくなります。
[ltac]非終端の関数アプリケーションは、GallinaではなくLtacのアプリケーションとして扱われます。
そのような関数への ＿引数＿ はデフォルトで [constr] で解析されます。
この選択は、私たちが書いているすべての証明スクリプトにすべて頼っていることがわかるまで、
奇妙に見えるかもしれません！
例えば、[apply] タクティクはLtac関数であり、
その引数をLtacではなくGallinaの項として解釈するのは当然です。
上記の %\coqdocvar{%#<tt>#map#</tt>#%}% の呼び出しのように、
[ltac]接頭辞を使用してLtac関数の引数をLtac項として解析します。
いくつかの単純なケースでは、Ltac項は余分なプレフィックスなしで渡されることがあります。
例えば、Ltacの意味を持ち、Gallinaの意味を持たない識別子は自動的にLtacで解釈されます。

(*
One other gotcha shows up when we want to debug our Ltac functional programs.  We might expect the following code to work, to give us a version of %\coqdocvar{%#<tt>#length#</tt>#%}% that prints a debug trace of the arguments it is called with. *)

Ltacの機能プログラムをデバッグしたいときには、もうひとつの問題があります。
呼び出された引数のデバッグ・トレースを出力する
%\coqdocvar{%#<tt>#length#</tt>#%}%
バージョンを提供するには、次のコードが必要です。
 *)

(* begin thide *)
Reset length.
(* begin hide *)
Reset red_herring.
(* end hide *)

(* begin hide *)
Definition red_herring := O.
(* end hide *)
Ltac length ls :=
  idtac ls;
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

(**
(* Coq accepts the tactic definition, but the code is fatally flawed and will always lead to dynamic type errors. *)

Coqはタクティクの定義を受け入れますが、コードには致命的な欠陥があり、
常に動的なタイプのエラーにつながります。
 *)

Goal False.
(** %\vspace{-.15in}%[[
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
]]

<<
Error: variable n should be bound to a term.
>> *)
Abort.

(**
(* What is going wrong here?  The answer has to do with the dual status of Ltac as both a purely functional and an imperative programming language.  The basic programming language is purely functional, but tactic scripts are one "datatype" that can be returned by such programs, and Coq will run such a script using an imperative semantics that mutates proof states.  Readers familiar with %\index{monad}\index{Haskell}%monadic programming in Haskell%~\cite{Monads,IO}% may recognize a similarity.  Haskell programs with side effects can be thought of as pure programs that return _the code of programs in an imperative language_, where some out-of-band mechanism takes responsibility for running these derived programs.  In this way, Haskell remains pure, while supporting usual input-output side effects and more.  Ltac uses the same basic mechanism, but in a dynamically typed setting.  Here the embedded imperative language includes all the tactics we have been applying so far.
*)

ここで何がうまくいかないのでしょうか？
答えは、Ltacの、純粋に関数プログラミング言語と命令的プログラミング言語の両方としての
二重状態( dual status)と関係しています。

基本的なプログラミング言語は純粋に関数的ですが、
タクティクスクリプトはそのようなプログラムによって返される「データ型」のひとつで、
Coqは証明状態を変更する命令的なセマンティクスを使ってそのようなスクリプトを実行します。

%~\cite{Monads,IO}% Haskell の
%\index{monad}\index{Haskell}% モナド・プログラミング(monadic programming)に
精通している読者は、類似点を認識しているかもしれません。
副作用を伴うHaskellプログラムは、
＿命令型言語におけるプログラムのコード＿
(the code of programs in an imperative language) を
返す純粋なプログラムと考えることができます。

一部の帯域外(out-of-band)なメカニズムは、
これらの派生プログラムを実行する責任を負います。
このようにして、Haskellは純粋なままで、通常の入出力の副作用などをサポートします。
Ltacは同じ基本メカニズムを使用しますが、動的に型付けされます。
ここで埋め込まれた命令的言語には、これまで適用されてきたすべてのタクティクが含まれます。

(*
   Even basic [idtac] is an embedded imperative program, so we may not automatically mix it with purely functional code.  In fact, a semicolon operator alone marks a span of Ltac code as an embedded tactic script.  This makes some amount of sense, since pure functional languages have no need for sequencing: since they lack side effects, there is no reason to run an expression and then just throw away its value and move on to another expression.
*)

基本的な [idtac] も組み込みの命令型プログラムなので、
純粋に機能的なコードと自動的には混合しないかもしれません。
実際には、セミコロン演算子だけでLtacコードのスパンを
組み込みのタクティクのスクリプトとしてマークしています。
純粋な関数型言語では順序付けの必要がないので、
副作用がないため、式を実行してからその値を捨て、別の式に移る理由はありません。

(*
   An alternate explanation that avoids an analogy to Haskell monads (admittedly a tricky concept in its own right) is: An Ltac tactic program returns a function that, when run later, will perform the desired proof modification.  These functions are distinct from other types of data, like numbers or Gallina terms.  The prior, correctly working version of [length] computed solely with Gallina terms, but the new one is implicitly returning a tactic function, as indicated by the use of [idtac] and semicolon.  However, the new version's recursive call to [length] is structured to expect a Gallina term, not a tactic function, as output.  As a result, we have a basic dynamic type error, perhaps obscured by the involvement of first-class tactic scripts.
*)

Haskell のモナド（それ自体は巧妙な考え方であると思われますが）に対する類推を
避けるための代替的な説明は次のとおりです。
Ltacのタクティクのプログラムは、
後で実行されるときに望ましい証明の変形(proof modification)を実行する関数を返します。
これらの関数は、他のデータ型や数やGallina項とは異なります。
Gallina項でのみ計算された [length] の以前の正しく動作していたバージョンですが、
[idtac] とセミコロンの使用で示されるように、新しい関数は暗黙的に関数を返しています。
しかし、新しいバージョンの [length] の再帰的呼び出しは、
出力としてGallina項をタクティクの関数ではないと予想するように構成されています。
その結果、基本的な動的な型エラーが発生します。
おそらくファーストクラスのタクティクのスクリプトが関与しています。

(*
   The solution is like in Haskell: we must "monadify" our pure program to give it access to side effects.  The trouble is that the embedded tactic language has no [return] construct.  Proof scripts are about proving theorems, not calculating results.  We can apply a somewhat awkward workaround that requires translating our program into%\index{continuation-passing style}% _continuation-passing style_ %\cite{continuations}%, a program structuring idea popular in functional programming. *)

結果はHaskellに似ています。
純粋なプログラムを「モナド化」して、副作用にアクセスできるようにする必要があります。
問題は組み込まれたタクティクの言語には [return] の構造がないことです。
証明スクリプトは、結果を計算するのではなく、定理を証明することに関するものです。
プログラムを
%\index{continuation-passing style}%
＿継承渡しスタイル＿ (continuation-passing style) %\cite{continuations}%
に変換する必要があるやや難しい回避策を適用することができます。
 *)

Reset length.
(* begin hide *)
Reset red_herring.
(* end hide *)

Ltac length ls k :=
  idtac ls;
  match ls with
    | nil => k O
    | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
  end.
(* end thide *)

(**
(* The new [length] takes a new input: a _continuation_ [k], which is a function to be called to continue whatever proving process we were in the middle of when we called %\coqdocvar{%#<tt>#length#</tt>#%}%.  The argument passed to [k] may be thought of as the return value of %\coqdocvar{%#<tt>#length#</tt>#%}%. *)

新しい [length] は、新しい入力を受け取ります: ＿継続＿ (continuation) [k] は、
%\coqdocvar{%#<tt>#length#</tt>#%}% を呼び出した途中でどのようなプロセスがあったとしても
継続するために呼び出される関数です。
[k] に渡される引数は、%\coqdocvar{%#<tt>#length#</tt>#%}% の戻り値と考えることができます。
 *)

(* begin thide *)
Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
(** [[
(1 :: 2 :: 3 :: nil)
(2 :: 3 :: nil)
(3 :: nil)
nil
]]
*)
Abort.
(* end thide *)

(**
(* We see exactly the trace of function arguments that we expected initially, and an examination of the proof state afterward would show that variable [n] has been added with value [3].
*)

私たちは最初に期待した関数引数のトレースを正確に見て、
その後の証明に状態を調べると、変数[n]に値[3]が追加され
ていることがわかります。

(*
   Considering the comparison with Haskell's IO monad, there is an important subtlety that deserves to be mentioned.  A Haskell IO computation represents (theoretically speaking, at least) a transformer from one state of the real world to another, plus a pure value to return.  Some of the state can be very specific to the program, as in the case of heap-allocated mutable references, but some can be along the lines of the favorite example "launch missile," where the program has a side effect on the real world that is not possible to undo.
*)

HaskellのIOモナドとの比較を考えると、言及する価値のある微妙なことがあります。
HaskellのI/O計算は、実世界のある状態から別の状態への変換器と、返す純粋な値を
（理論的に言えば、少なくとも）表現します。
状態の一部は、ヒープ割り当ての変更可能な参照の場合のように、
プログラム固有のものもありますが、
プログラムが、現実世界に元に戻すことができない副作用を及ぼす
お気に入りの例「ミサイル発射」の線に沿っているものもあります。

(*
   In contrast, Ltac scripts can be thought of as controlling just two simple kinds of mutable state.  First, there is the current sequence of proof subgoals.  Second, there is a partial assignment of discovered values to unification variables introduced by proof search (for instance, by [eauto], as we saw in the previous chapter).  Crucially, _every mutation of this state can be undone_ during backtracking introduced by [match], [auto], and other built-in Ltac constructs.  Ltac proof scripts have state, but it is purely local, and all changes to it are reversible, which is a very useful semantics for proof search. *)

対照的に、Ltacのスクリプトは、単に2つの単純な種類の可変状態を制御するものと考えることができます。
第1に、証明のサブゴールの現在のシーケンスが存在します。
第2に、前の章で見たように、証明検索によって導入されたユニフィケーション変数に発見された値を部分的に
割り当てます（たとえば、[eauto]）。
重要なことは、[match]、[auto]、および、その他のLtacを構成する組み込みのものによって導かれた
バックトラッキングの間には、
＿この状態のあらゆる変異を元に戻すことができる＿ ということです。
Ltac証明スクリプトには状態がありますが、
それは純粋にローカルなものであり、すべての変更は可逆的です。
これは証明検索のための非常に便利なセマンティクスです。
 *)

(*
(** * Recursive Proof Search *)
 *)
(** * 再帰的な証明探索 *)

(**
(* Deciding how to instantiate quantifiers is one of the hardest parts of automated first-order theorem proving.  For a given problem, we can consider all possible bounded-length sequences of quantifier instantiations, applying only propositional reasoning at the end.  This is probably a bad idea for almost all goals, but it makes for a nice example of recursive proof search procedures in Ltac.
*)

量化子をどのように具体化するかの決定は、
自動化された一階の定理の証明の最も難しい部分のひとつです。
与えられた問題によっては、最終的に命題の推論だけを適用することで、
量化子のインスタンス可能な全てからなる有限長のシーケンスを考えることができます。
これは、ほぼすべてのゴールに対して悪い考えですが、
Ltacの再帰的な証明探索の手順の素晴らしい例になります。

(*
   We can consider the maximum "dependency chain" length for a first-order proof.  We define the chain length for a hypothesis to be 0, and the chain length for an instantiation of a quantified fact to be one greater than the length for that fact.  The tactic [inster n] is meant to try all possible proofs with chain length at most [n]. *)

一階の証明のために最大の「依存鎖(dependency chain)」の長さを考慮することができます。
仮説の鎖の長を0とし、
量化された事実を具体化したものの鎖長をその事実の長さより、1だけ大きいものと定義します。
タクティク [inster n] は、鎖の長さの最大 [n] で、可能なすべての証明を試すことを意図しています。
 *)

(* begin thide *)
Ltac inster n :=
  intuition;
    match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?T, _, y : ?T |- _ ] => generalize (H y); inster n'
        end
    end.
(* end thide *)

(**
(* The tactic begins by applying propositional simplification.  Next, it checks if any chain length remains, failing if not.  Otherwise, it tries all possible ways of instantiating quantified hypotheses with properly typed local variables.  It is critical to realize that, if the recursive call [inster n'] fails, then the [match goal] just seeks out another way of unifying its pattern against proof state.  Thus, this small amount of code provides an elegant demonstration of how backtracking [match] enables exhaustive search.
*)

このタクティクは、命題の単純化を適用することから始まります。
次に、鎖長が残っているかどうかをチェックし、そうでない場合は失敗します。
それ以外の場合は、適切に型付けされたローカル変数を使用して
量化された仮説を具体化するすべての可能な方法を試行します。
再帰呼び出し [inster n'] が失敗した場合、[match goal] は、
そのパターンを証明の状態とユニファイする別の方法を探していることに気付くことが重要です。
したがって、この少量のコードは、バックトラック [mactch] がどのように
徹底的な検索を可能にするかについてのエレガントなデモンストレーションを提供します。

(*
   We can verify the efficacy of [inster] with two short examples.  The built-in [firstorder] tactic (with no extra arguments) is able to prove the first but not the second. *)

ふたつの短い例で [inster] の有効性を検証することができます。
組み込みの [firstorder] タクティク（余計な引数なし）は、
最初のものを証明することができますが、2番目のものは証明できません。
 (* suhara: Goal : Q (f y) が残る。 *)
 *)

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
    inster 3.
  Qed.
End test_inster.

(**
(* The style employed in the definition of [inster] can seem very counterintuitive to functional programmers.  Usually, functional programs accumulate state changes in explicit arguments to recursive functions.  In Ltac, the state of the current subgoal is always implicit.  Nonetheless, recalling the discussion at the end of the last section, in contrast to general imperative programming, it is easy to undo any changes to this state, and indeed such "undoing" happens automatically at failures within [match]es.  In this way, Ltac programming is similar to programming in Haskell with a stateful failure monad that supports a composition operator along the lines of the [first] tactical.
*)

[inster] の定義に採用されているスタイルは、関数的なプログラマーには直観に反するように見えます。
通常、関数プログラムは、明示的な状態変化を再帰関数にの引数に蓄積します。
Ltacでは、現在のサブゴールの状態は常に暗黙的です。
それにもかかわらず、一般的な命令型プログラミングとは対照的に、
この前の節最後の議論を思い出すなら、この状態への変更を元に戻すのは簡単です。
実際、このような「undo」は、[match] 内の失敗で自動的に起こります。
このように、Ltacプログラミングは、[first] タクティカルの行に沿って合成演算子(composition operator)
をサポートするステートフルな failure モナドを持つHaskellのプログラミングと似ています。

(*
   Functional programming purists may react indignantly to the suggestion of programming this way.  Nonetheless, as with other kinds of "monadic programming," many problems are much simpler to solve with Ltac than they would be with explicit, pure proof manipulation in ML or Haskell.  To demonstrate, we will write a basic simplification procedure for logical implications.
*)

関数プログラミングの純粋主義者は、
このようなプログラミングの提案に対して憤慨して反応するかもしれません。
それにもかかわらず、他の種類の「モナド・プログラミング」と同様に、
多くの問題が
MLやHaskellでの明示的で純粋な証明操作よりも、
Ltacで解決するのがはるかに簡単です。
実証するために、論理的含意いのための基本的な簡略化手順を書くことにします。

(*
   This procedure is inspired by one for separation logic%~\cite{separation}%, where conjuncts in formulas are thought of as "resources," such that we lose no completeness by "crossing out" equal conjuncts on the two sides of an implication.  This process is complicated by the fact that, for reasons of modularity, our formulas can have arbitrary nested tree structure (branching at conjunctions) and may include existential quantifiers.  It is helpful for the matching process to "go under" quantifiers and in fact decide how to instantiate existential quantifiers in the conclusion.
*)

この手順は、分離論理 %~\cite{separation}% に影響を受けています。
ここでは、式のなかの連言(conjuncts in formulas)は「リソース」と見なされ、
含意の両辺で等しい連言を「交差させる」ことによって完全性を失うことはありません。
このプロセスは、モジュール性の理由から、式が任意の入れ子ツリー構造（連言での分岐）を持つことができ、
存在量化子を含むことができるという事実によって複雑になります。
これは、マッチングプロセスが量化子を「下にいく」ことに役立ち、
実際に、存在量化子をどのように具体化するかを決定するのに役立ちます。

(*
   To distinguish the implications that our tactic handles from the implications that will show up as "plumbing" in various lemmas, we define a wrapper definition, a notation, and a tactic. *)

我々のタクティクが扱う含意を
さまざまな補題で「配管」として現れる含意から区別するために、
ラッパー定義、ノーテーション、およびタクティクを定義します。
 *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

(**
(* These lemmas about [imp] will be useful in the tactic that we will write. *)

[imp]に関するこれらの補題は、我々が書くタクティクに役立つでしょう。
 *)

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
  imp.
Qed.

Theorem pick_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem pick_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
  imp.
Qed.

Theorem pick_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem pick_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
  imp.
Qed.

(**
(* The first order of business in crafting our [matcher] tactic will be auxiliary support for searching through formula trees.  The [search_prem] tactic implements running its tactic argument [tac] on every subformula of an [imp] premise.  As it traverses a tree, [search_prem] applies some of the above lemmas to rewrite the goal to bring different subformulas to the head of the goal.  That is, for every subformula [P] of the implication premise, we want [P] to "have a turn," where the premise is rearranged into the form [P /\ Q] for some [Q].  The tactic [tac] should expect to see a goal in this form and focus its attention on the first conjunct of the premise. *)

私たちの [matcher] タクティクを作る上での最初の作業(the first order of business)は、
式の木を検索するための補助的なサポートになります。
[search_prem] タクティクは
[imp] の前提のすべての部分式(subformula)で、引数[tac]を実行するように実装されます。
木を走査するとき、[search_prem] は上記の補題のいくつかを適用して、
異なる部分式(subformula)をゴールの頭部にもっていくことで、
ゴールを書き換えます。

すなわち、
その前提が、いくつかの[Q]に対して、[P /\ Q]のかたちに再配置されるところで、
含意の前提のそれぞれの部分式 [P] に対して、[P] を 「have a turn」しようとします。

(* suhara: 最後のmatchのひとつめのcaseのこと。Qは「_」。 *)

タクティク [tac] はこのかたちでゴールを見ることを期待し、
前提の最初の連言に注意を集中するでしょう。
 *)

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_prem1; search P1)
           || (apply pick_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.

(**
(* To understand how [search_prem] works, we turn first to the final [match].  If the premise begins with a conjunction, we call the [search] procedure on each of the conjuncts, or only the first conjunct, if that already yields a case where [tac] does not fail.  The call [search P] expects and maintains the invariant that the premise is of the form [P /\ Q] for some [Q].  We pass [P] explicitly as a kind of decreasing induction measure, to avoid looping forever when [tac] always fails.  The second [match] case calls a commutativity lemma to realize this invariant, before passing control to [search].  The final [match] case tries applying [tac] directly and then, if that fails, changes the form of the goal by adding an extraneous [True] conjunct and calls [tac] again.  The %\index{tactics!progress}%[progress] tactical fails when its argument tactic succeeds without changing the current subgoal.
*)

[search_prem] がどのように機能するかを理解するために、
最初に、最後の [match] に進みます。
前提が連言で始まる場合は、各連言で[search]手続きを呼び出します。 
[search P] の呼び出しは、ある [Q] のための前提が [P /\ Q] の形式であるという
不変性を期待し維持します。

[tac]が常に失敗したときに永久にループするのを避けるために、
一種の再帰の尺度として減少する、[P]を明示的に渡します。

2番目の[match]の場合は、制御を[search]に渡す前に、
この不変量を実現するために可換性(commutativity)の補題を呼び出します。

最終的な[match] の場合では [tac] を直接適用しようとしますが、
それが失敗すると、余分な[True]結合を追加してゴールの形を変え、
[tac]をもう一度呼び出します。
現在のサブゴールを変更せずに引数のタクティクが成功した場合、
%\index{tactics!progress}%[progress] タクティカルは失敗します。
(* suhara: progress は、証明が進まないことを検出したら失敗する。 *)

(*
   The [search] function itself tries the same tricks as in the last case of the final [match], using the [||] operator as a shorthand for trying one tactic and then, if the first fails, trying another.  Additionally, if neither works, it checks if [P] is a conjunction.  If so, it calls itself recursively on each conjunct, first applying associativity/commutativity lemmas to maintain the goal-form invariant.
*)

[search] 関数自体は最後の [match] の最後の場合と同じトリックを試みますが、
[||]演算子を使ってひとつの手法を試してみます。
さらに、いずれも動作しない場合、[P]が連言であるかどうかをチェックします。
そうであれば、それはそれぞれの連言に対して再帰的に自分自身を呼び出し、
最初に 結合性(associativity) と 可換性の補題を適用してゴールの式の不変性を維持します。

(*
   We will also want a dual function [search_conc], which does tree search through an [imp] conclusion. *)

また、[imp] の結論を通して木の検索を行う双対(dual)関数 [search_conc] が必要です。 *）

 *)

Ltac search_conc tac :=
  let rec search P :=
    tac
    || (apply and_True_conc; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_conc1; search P1)
           || (apply pick_conc2; search P2)
       end
  in match goal with
       | [ |- _ --> ?P /\ _ ] => search P
       | [ |- _ --> _ /\ ?P ] => apply comm_conc; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_conc; tac))
     end.

(**
(* Now we can prove a number of lemmas that are suitable for application by our search tactics.  A lemma that is meant to handle a premise should have the form [P /\ Q --> R] for some interesting [P], and a lemma that is meant to handle a conclusion should have the form [P --> Q /\ R] for some interesting [Q]. *)

ここでは、検索戦略によってアプリケーションに適したいくつかの補題を証明することができます。
前提を扱う補題は、[P]に関心をもった[P /\ Q -> R]の形式でなければならず、
結論を扱う補題は、[Q]に関心をもった[P --> Q /\ R]の形式でなければなりません。

 *)

(* begin thide *)
Theorem False_prem : forall P Q,
  False /\ P --> Q.
  imp.
Qed.

Theorem True_conc : forall P Q : Prop,
  (P --> Q)
  -> (P --> True /\ Q).
  imp.
Qed.

Theorem Match : forall P Q R : Prop,
  (Q --> R)
  -> (P /\ Q --> P /\ R).
  imp.
Qed.

Theorem ex_prem : forall (T : Type) (P : T -> Prop) (Q R : Prop),
  (forall x, P x /\ Q --> R)
  -> (ex P /\ Q --> R).
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
  (Q --> P x /\ R)
  -> (Q --> ex P /\ R).
  imp.
Qed.

(**
(* We will also want a "base case" lemma for finishing proofs where cancellation has removed every constituent of the conclusion. *)

取り消しが結論のすべての構成要素を取り除いた場合の証明を完成させるための
「基本ケース」補題も必要です。
 *)

Theorem imp_True : forall P,
  P --> True.
  imp.
Qed.

(**
(* Our final [matcher] tactic is now straightforward.  First, we [intros] all variables into scope.  Then we attempt simple premise simplifications, finishing the proof upon finding [False] and eliminating any existential quantifiers that we find.  After that, we search through the conclusion.  We remove [True] conjuncts, remove existential quantifiers by introducing unification variables for their bound variables, and search for matching premises to cancel.  Finally, when no more progress is made, we see if the goal has become trivial and can be solved by [imp_True].  In each case, we use the tactic %\index{tactics!simple apply}%[simple apply] in place of [apply] to use a simpler, less expensive unification algorithm. *)

今や、最終的な[matcher]タクティクは簡単です。

最初に、すべての変数をスコープに [intro] し、
単純な前提の単純化を試み、
[False]を見つけたら証明を完成させ、
見つかった存在量化子を取り除きます。

その後、結論を検索します。

[True] の連言を取り除き、
ユニフィケーション変数を導入することによって、束縛変数のための存在量化子を取り除き、
一致する前提を探して取り除きます。

最後に、それ以上の進展がなければ、ゴールが自明かどうかをみて、[imp_True] によって解くことができます。
それぞれの場合において、簡単にするために、[apply] の代わりに、
より安価なユニフィケーション・アルゴリズムである
%\index{tactics!simple apply}%[simple apply] タクティクを使います。
 *)

Ltac matcher :=
  intros;
    repeat search_prem ltac:(simple apply False_prem || (simple apply ex_prem; intro));
      repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
        || search_prem ltac:(simple apply Match));
      try simple apply imp_True.
(* end thide *)

(**
(* Our tactic succeeds at proving a simple example. *)

私たちの戦術は簡単な例を証明するのに成功します。
 *)

Theorem t2 : forall P Q : Prop,
  Q /\ (P /\ False) /\ P --> P /\ Q.
  matcher.
Qed.

(**
(* In the generated proof, we find a trace of the workings of the search tactics. *)
生成された証明では、検索手法の動作の痕跡が見つかります。
 *)

Print t2.
(** %\vspace{-.15in}% [[
t2 = 
fun P Q : Prop =>
comm_prem (pick_prem1 (pick_prem2 (False_prem (P:=P /\ P /\ Q) (P /\ Q))))
     : forall P Q : Prop, Q /\ (P /\ False) /\ P --> P /\ Q
     ]]

(*
%\smallskip{}%We can also see that [matcher] is well-suited for cases where some human intervention is needed after the automation finishes. *)

%\smallskip{}%
自動化が完了した後に人間の介入が必要な場合に[matcher]が適していることがわかります。
*)

Theorem t3 : forall P Q R : Prop,
  P /\ Q --> Q /\ R /\ P.
  matcher.
  (** [[
  ============================
   True --> R
 
   ]]
(*
   Our tactic canceled those conjuncts that it was able to cancel, leaving a simplified subgoal for us, much as [intuition] does. *)

私たちのタクティクは、それが取り消すことができたそれらの連言を取り消し、
[intuition]と同じように、私たちのための簡略化されたサブゴールを残しました。 *）

*)
Abort.

(**
(* The [matcher] tactic even succeeds at guessing quantifier instantiations.  It is the unification that occurs in uses of the [Match] lemma that does the real work here. *)

[matcher] タクティクは、量化の具体化を推測することにも成功します。
実際の作業を行う [Match] 補題の使用にあるのはユニフィケーションです。
  *)

Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) --> Q /\ (exists x, P x).
  matcher.
Qed.

Print t4.
(** %\vspace{-.15in}% [[
t4 = 
fun (P : nat -> Prop) (Q : Prop) =>
and_True_prem
  (ex_prem (P:=fun x : nat => P x /\ Q)
     (fun x : nat =>
      pick_prem2
        (Match (P:=Q)
           (and_True_conc
              (ex_conc (fun x0 : nat => P x0) x
                 (Match (P:=P x) (imp_True (P:=True))))))))
     : forall (P : nat -> Prop) (Q : Prop),
       (exists x : nat, P x /\ Q) --> Q /\ (exists x : nat, P x)
]]

(*
This proof term is a mouthful, and we can be glad that we did not build it manually! *)

この証明の項はひと口で、手作業で構築していないのはうれしいことです！
*)

(*
(** * Creating Unification Variables *)
 *)
(** * ユニフィケーション変数の生成 *)

(**
(* A final useful ingredient in tactic crafting is the ability to allocate new unification variables explicitly.  Tactics like [eauto] introduce unification variables internally to support flexible proof search.  While [eauto] and its relatives do _backward_ reasoning, we often want to do similar _forward_ reasoning, where unification variables can be useful for similar reasons.
*)

タクティクを作成するための最後の有用な要素は、新しいユニフィケーション変数を明示的に割り当てることです。
[eauto] のような戦術は、柔軟な証明検索をサポートするためにユニフィケーション変数を内部的に導入しています。
[eauto] とその親戚は ＿後ろ向き＿ の推論をしていますが、 
ユニフィケーション変数が同様の理由で有用であるとき、しばしば同様に ＿前向き＿ 推論をしたいからです。

(*
   For example, we can write a tactic that instantiates the quantifiers of a universally quantified hypothesis.  The tactic should not need to know what the appropriate instantiations are; rather, we want these choices filled with placeholders.  We hope that, when we apply the specialized hypothesis later, syntactic unification will determine concrete values.
*)

例えば、全称定化された仮説の定化子を具体化するタクティクを書くことができます。
タクティクは、適切な具体化が何であるかを知る必要はありません。
むしろ、これらの選択肢は代用品(placeholder)で満たされています。
後で、特化するための(specialized)仮説を適用すると、構文的なユニフィケーションによって、
具体的な値が決まることを願っています。

(*
   Before we are ready to write a tactic, we can try out its ingredients one at a time. *)

タクティクを書く準備が整う前に、一度にひとつずつ材料を試すことができます。
 *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
  intros.

  (** [[
  H : forall x : nat, S x > x
  ============================
   2 > 1
 
   ]]

(*
   To instantiate [H] generically, we first need to name the value to be used for [x].%\index{tactics!evar}% *)

一般的に、[H]を具体化するには、最初に[x]に使用する値の名前を付ける必要があります。%\index{tactics!evar}%
*)
  evar (y : nat).

  (** [[
  H : forall x : nat, S x > x
  y := ?279 : nat
  ============================
   2 > 1
 
   ]]

(*
   The proof context is extended with a new variable [y], which has been assigned to be equal to a fresh unification variable [?279].  We want to instantiate [H] with [?279].  To get ahold of the new unification variable, rather than just its alias [y], we perform a trivial unfolding in the expression [y], using the %\index{tactics!eval}%[eval] Ltac construct, which works with the same reduction strategies that we have seen in tactics (e.g., [simpl], [compute], etc.).  *)

証明コンテキストは新しい変数 [y] で拡張され、
新しいユニフィケーション変数 [?279] と等しくなるように割り当てられています。
[?279] と [H] を具体化する必要があります。
エイリアス [y] だけではなく、新しいユニフィケーション変数を取得するために、Ltac の
%\index{tactics!eval}%[eval]
要素使用して式 [y] で自明な展開(unfolding)を実行します。
タクティク（例えば、[simpl]、[compute]など）で見られたのと同じ簡約戦略(reduction strategies)です。
   *)
  
  let y' := eval unfold y in y in
    clear y; specialize (H y').

  (** [[
  H : S ?279 > ?279
  ============================
    2 > 1
 
   ]]

(*
   Our instantiation was successful.  We can finish the proof by using [apply]'s unification to figure out the proper value of [?279]. *)

具体化は成功しました。
[apply] のユニフィケーションを使って [?279] の固有な値を計算することで証明を終えることができます。
   *)
  
  apply H.
Qed.

(**
(* Now we can write a tactic that encapsulates the pattern we just employed, instantiating all quantifiers of a particular hypothesis. *)

今使っているパターンをカプセル化して、特定の仮説のすべての量化子を具体化する方法を書くことができます。
 *)

(* begin hide *)
Definition red_herring := O.
(* end hide *)
Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                 clear x; specialize (H x')
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
  intro H; insterU H; apply H.
Qed.

(**
(* This particular example is somewhat silly, since [apply] by itself would have solved the goal originally.  Separate forward reasoning is more useful on hypotheses that end in existential quantifications.  Before we go through an example, it is useful to define a variant of [insterU] that does not clear the base hypothesis we pass to it.  We use the Ltac construct %\index{tactics!fresh}%[fresh] to generate a hypothesis name that is not already used, based on a string suggesting a good name. *)

この特定の例は、[apply] 自体が本来の目的を達成していたので、やや馬鹿げています。
別の前方推論は、存在量化の定量化で終わる仮説により有用です。
例を見る前に、
私たちが渡すベースとなる仮説を除去(clear)していない [insterU] の変種の Ltac の構成要素
%\index{tactics!fresh}%[fresh] を使用して、（引数の)文字列で示唆されるよい名前に基づいた、
まだ使用されていない仮説名を生成します。
 *)

Ltac insterKeep H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros.

    (**
(* Neither [eauto] nor [firstorder] is clever enough to prove this goal.  We can help out by doing some of the work with quantifiers ourselves, abbreviating the proof with the %\index{tactics!do}%[do] tactical for repetition of a tactic a set number of times. *)

[eauto] も [firstorder] もこのゴールを証明するほどには賢くはありません。
量化子を使っていくつかの作業を自分で行い、%\index{tactics!do}%[do] タクティカルによって、
一定回数のタクティクを繰り返すことで、証明を省略します。
     *)
    
    do 2 insterKeep H1.

    (**
(* Our proof state is extended with two generic instances of [H1].
*)

証明状態は[H1]のふたつの一般的なインスタンスで拡張されています。

       [[
  H' : exists u : B, P ?4289 u
  H'0 : exists u : B, P ?4288 u
  ============================
   exists u1 : B, exists u2 : B, P (f v1 v2) (g u1 u2)
 
   ]]

(*
   Normal [eauto] still cannot prove the goal, so we eliminate the two new existential quantifiers.  (Recall that [ex] is the underlying type family to which uses of the [exists] syntax are compiled.) *)

通常の[eauto]はまだ目標を証明することができませんので、
ふたつの新しい存在量化子を削除します。
（[ex]は、[exists]構文の使用がコンパイルされるもとになる型ファミリであることを思い出してください）
     *)

    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end.

    (**
(* Now the goal is simple enough to solve by logic programming. *)

ゴールは、論理プログラミングで解くには、とても単純です。
*)
    eauto.
  Qed.
End t6.

(**
(* Our [insterU] tactic does not fare so well with quantified hypotheses that also contain implications.  We can see the problem in a slight modification of the last example.  We introduce a new unary predicate [Q] and use it to state an additional requirement of our hypothesis [H1]. *)

[insterU] タクティクは、含意も含む量化仮説ではあまりうまくいきません。
最後の例をわずかに変更して問題を見ることができます。
新しい単項の述語[Q]を導入し、仮説[H1]の追加の要求を表示するのに使います。
 *)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.
    (**
(* This proof script does not hit any errors until the very end, when an error message like this one is displayed.

この証明スクリプトは、このようなエラーメッセージが表示した最後まで、何のエラーも発生しません。
*)

<<
No more subgoals but non-instantiated existential variables :
Existential 1 =
>>
       %\vspace{-.35in}%[[
?4384 : [A : Type
         B : Type
         Q : A -> Prop
         P : A -> B -> Prop
         f : A -> A -> A
         g : B -> B -> B
         H1 : forall v : A, Q v -> exists u : B, P v u
         H2 : forall (v1 : A) (u1 : B) (v2 : A) (u2 : B),
              P v1 u1 -> P v2 u2 -> P (f v1 v2) (g u1 u2)
         v1 : A
         v2 : A
         H : Q v1
         H0 : Q v2
         H' : Q v2 -> exists u : B, P v2 u |- Q v2] 
         ]]

(*
         There is another similar line about a different existential variable.  Here, "existential variable" means what we have also called "unification variable."  In the course of the proof, some unification variable [?4384] was introduced but never unified.  Unification variables are just a device to structure proof search; the language of Gallina proof terms does not include them.  Thus, we cannot produce a proof term without instantiating the variable.
*)

別の存在変数(existential variable)についても同様の行があります。
ここで、「存在変数」とは、「ユニフィケーション変数」とも呼ばれるものを意味します。
証明の過程で、ユニフィケーション変数[?4384]が導入されましたが、
ユニフィケーションされませんでした。
ユニフィケーション変数は、証明検索を構造化するための単なる器(device)です。
Gallina言語の証明項にはそれらが含まれていません。
したがって、変数を具体化せずに証明項を生成することはできません。

(*
         The error message shows that [?4384] is meant to be a proof of [Q v2] in a particular proof state, whose variables and hypotheses are displayed.  It turns out that [?4384] was created by [insterU], as the value of a proof to pass to [H1].  Recall that, in Gallina, implication is just a degenerate case of [forall] quantification, so the [insterU] code to match against [forall] also matched the implication.  Since any proof of [Q v2] is as good as any other in this context, there was never any opportunity to use unification to determine exactly which proof is appropriate.  We expect similar problems with any implications in arguments to [insterU]. *)

エラーメッセージは、[?4384]が変数と仮説が表示されている特定の証明状態の
[Q v2]の証明であることを示しています。
それは[?4384]が[H1]に渡す証明の値として[insterU]によって作成されたことが判明しました。
Gallinaでは、含意は単に[forall]量化の縮退したかたちであるため、
[forall]と一致させる[insterU]コードもこの含意と一致したことを思い出してください。
この文脈で[Q v2]の証明は他の証明と同じくらい良いので、
どの証明が適切かを正確に判断するためにユニフィケーションを使う機会は決してありません。
同様に[insterU]の引数にある含意の問題を予期しています。
     *)
    
  Abort.
End t7.

Reset insterU.
(* begin hide *)
Reset red_herring.
(* end hide *)

(**
(* We can redefine [insterU] to treat implications differently.  In particular, we pattern-match on the type of the type [T] in [forall x : ?T, ...].  If [T] has type [Prop], then [x]'s instantiation should be thought of as a proof.  Thus, instead of picking a new unification variable for it, we instead apply a user-supplied tactic [tac].  It is important that we end this special [Prop] case with [|| fail 1], so that, if [tac] fails to prove [T], we abort the instantiation, rather than continuing on to the default quantifier handling.  Also recall that the tactic form %\index{tactics!solve}%[solve [ t ]] fails if [t] does not completely solve the goal. *)

[forall x : ?T, ...]の型[T]の型をパターンマッチさせる[T]に型[Prop]、
[x]の具体化は証明のために考える必要があります。
したがって、新しい統一変数を選択するのではなく、
ユーザーが指定した戦術[tac]を適用します。
[tac]が[T]を証明するのに失敗した場合、

デフォルトの量化の処理を続けるのではなく、
具体化を中止します。また、
%\index{tactics!solve}%
が目標を完全に解決しない場合、[solve [t]] は失敗します。*）
 *)

Ltac insterU tac H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T) by solve [ tac ];
                     specialize (H H'); clear H')
                 || fail 1
               | _ =>
                 let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

Ltac insterKeep tac H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU tac H'.

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).

    (**
(* We can prove the goal by calling [insterKeep] with a tactic that tries to find and apply a [Q] hypothesis over a variable about which we do not yet know any [P] facts.  We need to begin this tactic code with [idtac; ] to get around a strange limitation in Coq's proof engine, where a first-class tactic argument may not begin with a [match]. *)

まだ[P]の事実を知らない変数について[Q]仮説を見つけて適用しようとするタクティクで
[insterKeep]を呼び出すことによってゴールを証明することができます。

Coqの証明エンジンで、
ファーストクラスのタクティクの引数が、
[match]で始まらなければならないという奇妙な制限を回避するために、
このタクティクのコードを[idtac; ]で始める必要があります。
     *)
    
    intros; do 2 insterKeep ltac:(idtac; match goal with
                                           | [ H : Q ?v |- _ ] =>
                                             match goal with
                                               | [ _ : context[P v _] |- _ ] => fail 1
                                               | _ => apply H
                                             end
                                         end) H1;
    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7.

(**
(* It is often useful to instantiate existential variables explicitly.  A built-in tactic provides one way of doing so. *)

存在変数(existential variables)を明示的に具体化することはしばしば役に立ちます。
組み込みタクティクはそれをするひとつの方法を提供します。
 *)

Theorem t8 : exists p : nat * nat, fst p = 3.
  econstructor; instantiate (1 := (3, 2)); reflexivity.
Qed.

(**
(* The [1] above is identifying an existential variable appearing in the current goal, with the last existential appearing assigned number 1, the second-last assigned number 2, and so on.  The named existential is replaced everywhere by the term to the right of the [:=].
*)

上記の[1]は、現在のゴールに現れる存在変数を特定するもので、
最後に存在するものが番号1に割り当てられ、2番目に割り当てられた番号2が割り当てられます。
名前のついた存在（変数）は、どこでも[:=]の右側の項に置き換えられます。

(*
   The %\index{tactics!instantiate}%[instantiate] tactic can be convenient for exploratory proving, but it leads to very brittle proof scripts that are unlikely to adapt to changing theorem statements.  It is often more helpful to have a tactic that can be used to assign a value to a term that is known to be an existential.  By employing a roundabout implementation technique, we can build a tactic that generalizes this functionality.  In particular, our tactic [equate] will assert that two terms are equal.  If one of the terms happens to be an existential, then it will be replaced everywhere with the other term. *)

%\index{tactics!instantiate}%[instantiate] タクティクは
探索的な証明(exploratory proving)のためには便利かもしれませんが、
変化する定理には適応しにくい非常に脆い証明スクリプトにつながります。

実在すると判っている項に値を割り当てるために使用できるタクティクを持つことは、しばしば有用です。
婉曲な(roundabout)実装技術を採用することで、この機能を一般化するタクティクを作ることができます。
特に、我々の戦術[equate]は、2つの項が等しいことを主張します。
項のひとつが存在していれば、それはどこにでも置き換えられます。
 *)

Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.

(**
(* This tactic fails if it is not possible to prove [x = y] by [eq_refl].  We check the proof only for its unification side effects, ignoring the associated variable [dummy].  With [equate], we can build a less brittle version of the prior example. *)

[eq_refl]で[x = y]を証明することができない場合、この方法は失敗します。
関連する変数[dummy]を無視して、ユニフィケーションの副作用のみをチェックします。
[equate] によって先の例の脆弱なバージョンを作ることができます。
 *)

Theorem t9 : exists p : nat * nat, fst p = 3.
  econstructor; match goal with
                  | [ |- fst ?x = 3 ] => equate x (3, 2)
                end; reflexivity.
Qed.

(**
(* This technique is even more useful within recursive and iterative tactics that are meant to solve broad classes of goals. *)

このテクニックは、
広範囲のゴールを解決するための再帰な繰り返しのあるタクティクの中でさらに役立ちます。
 *)

(* END *)

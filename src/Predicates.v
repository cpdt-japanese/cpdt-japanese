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

(* Extra definitions to get coqdoc to choose the right fonts. *)

(* begin thide *)
Inductive unit := tt.
Inductive Empty_set := .
Inductive bool := true | false.
Inductive sum := .
Inductive prod := .
Inductive and := conj.
Inductive or := or_introl | or_intror.
Inductive ex := ex_intro.
Inductive eq := eq_refl.
Reset unit.
(* end thide *)
(* end hide *)

(**
(** %\chapter{Inductive Predicates}% *)
*)
(** %\chapter{帰納的な述語}% *)

(**
(** The so-called %\index{Curry-Howard correspondence}``%#"#Curry-Howard correspondence#"#%''~\cite{Curry,Howard}% states a formal connection between functional programs and mathematical proofs.  In the last chapter, we snuck in a first introduction to this subject in Coq.  Witness the close similarity between the types [unit] and [True] from the standard library: *)
*)

(**
いわゆる「Curry-Howard同型対応」というものがあり，それは，関数型プログラムと数学的証明の形式的な対応のことです．
前の章では，このテーマの最初の導入を行いました．
標準ライブラリの[unit]と[True]について非常に類似していることを見てみましょう．
*)

Print unit.
(** %\vspace{-.15in}%[[
  Inductive unit : Set :=  tt : unit
]]
*)

Print True.
(**
(** %\vspace{-.15in}%[[
  Inductive True : Prop :=  I : True
  ]]

Recall that [unit] is the type with only one value, and [True] is the proposition that always holds.  Despite this superficial difference between the two concepts, in both cases we can use the same inductive definition mechanism.  The connection goes further than this.  We see that we arrive at the definition of [True] by replacing [unit] by [True], [tt] by [I], and [Set] by [Prop].  The first two of these differences are superficial changes of names, while the third difference is the crucial one for separating programs from proofs.  A term [T] of type [Set] is a type of programs, and a term of type [T] is a program.  A term [T] of type [Prop] is a logical proposition, and its proofs are of type [T].  Chapter 12 goes into more detail about the theoretical differences between [Prop] and [Set].  For now, we will simply follow common intuitions about what a proof is.

The type [unit] has one value, [tt].  The type [True] has one proof, [I].  Why distinguish between these two types?  Many people who have read about Curry-Howard in an abstract context but who have not put it to use in proof engineering answer that the two types in fact _should not_ be distinguished.  There is a certain aesthetic appeal to this point of view, but I want to argue that it is best to treat Curry-Howard very loosely in practical proving.  There are Coq-specific reasons for preferring the distinction, involving efficient compilation and avoidance of paradoxes in the presence of classical math, but I will argue that there is a more general principle that should lead us to avoid conflating programming and proving.

The essence of the argument is roughly this: to an engineer, not all functions of type [A -> B] are created equal, but all proofs of a proposition [P -> Q] are.  This idea is known as%\index{proof irrelevance}% _proof irrelevance_, and its formalizations in logics prevent us from distinguishing between alternate proofs of the same proposition.  Proof irrelevance is compatible with, but not derivable in, Gallina.  Apart from this theoretical concern, I will argue that it is most effective to do engineering with Coq by employing different techniques for programs versus proofs.  Most of this book is organized around that distinction, describing how to program, by applying standard functional programming techniques in the presence of dependent types; and how to prove, by writing custom Ltac decision procedures.

With that perspective in mind, this chapter is sort of a mirror image of the last chapter, introducing how to define predicates with inductive definitions.  We will point out similarities in places, but much of the effective Coq user's bag of tricks is disjoint for predicates versus "datatypes."  This chapter is also a covert introduction to dependent types, which are the foundation on which interesting inductive predicates are built, though we will rely on tactics to build dependently typed proof terms for us for now.  A future chapter introduces more manual application of dependent types. *)
*)

(** %\vspace{-.15in}%[[
  Inductive True : Prop :=  I : True
  ]]

[unit]はただ1つの値をとる型で，[True]は常に成り立つ命題であったことを思い出してください．
この2つの概念には表面的な違いがありますが，両者ともにInductiveを使った定義になっている点は同じです．
[unit]と[True]の類似点はまだあります．
[unit]を[True]に，[tt]を[I]に，[Set]を[Prop]に置き換えると[True]の定義になるということがわかります．
最初の2つの違いは名前の変更なので重要ではありませんが，3つ目の違いは重要なもので，プログラムと証明をわけるものです．
[Set]型の[T]という項があればそれはプログラムの集合を表す型で，[T]型を持つ項はプログラムです．
[Prop]型の[T]という項があればそれは論理的な命題で，その証明は[T]型を持ちます．
12章ではもっと詳細に[Prop]と[Set]の理論的な違いを説明します．
今の所は，証明が何かということについて，一般的な感覚に基づいておくことにします．

[unit]という型は[tt]という1つの値を取ります．
[True]という型には[I]という1つの証明があります．
なぜこれらの型を区別するのでしょうか？
抽象的な文脈でカリーハワードのことを読んだことがあっても証明工学で使ったことのない人は，実はこれら2つの型は区別する＿べきではない＿と答えるでしょう．
確かにこの見方には美しさを訴えかけてくるものがあります．しかし，実用的な証明においてカリーハワードはとてもゆるく扱われるべきだということを私は言いたいのです．
このような区別をした方が良いCoq特有の理由があります．
コンパイルを効率的に行うことと古典主義の数学（論理学）に存在するパラドクスを避けるためというのもありますが，私はむしろ，証明とプログラミングを一緒にしなくなるようなより一般的な法則を主張します．

議論の重要なところはだいたいこのようなものです：[A -> B]の全ての関数が同じではありませんが，[P -> Q]という命題の全ての証明は等しいのです．
この考えは＿proof irrelevance＿として知られています．そしてそれを論理学において形式化すると同じ命題の異なる証明を区別するのが難しくなります．
Proof irrelevanceはGallinaでは互換性はあるけど推論はできません（？）．
このような理論的な懸念とは別に，私はCoqで開発をするのがもっとも効果的だと考えています．プログラムと証明に別々のテクニックを使えるからです．
この本のほとんどの部分はこの区別のもとに書かれています．
プログラムの際は依存型の存在を前提とした標準的な関数型プログタミングのテクニックを使います．
そして証明の際はカスタムのLtac決定手続きを書きます．

上記の見方に注意すると，この章は前章の鏡像のようなものです．帰納的な定義を使って命題を定義する方法を紹介します．
所々で類似性を指摘するでしょうが，効果的なCoqユーザーの知恵袋は命題とデータ型で交わりません．
依存型をもつ証明項を構築するタクティク使っていく一方で，この章はまた依存型のひそかな紹介でもあります．依存型は興味深い帰納的命題を作る土台になっています．
さらに先の章ではより手動による依存型の応用も扱って行きます．
*)

(**
(** * Propositional Logic *)
*)
(** * 命題論理 *)

(**
(** Let us begin with a brief tour through the definitions of the connectives for propositional logic.  We will work within a Coq section that provides us with a set of propositional variables.  In Coq parlance, these are just variables of type [Prop]. *)
*)

(**
命題論理に出てくる結合記号の定義を簡単に見ていくことから始めましょう．
これからしばらくの間は，命題変数の集合を定めたCoqセクションに入っておくことにします．
Coq用語では，命題とは単に[Prop]型の変数です．
*)

Section Propositional.
  Variables P Q R : Prop.

(**
  (** In Coq, the most basic propositional connective is implication, written [->], which we have already used in almost every proof.  Rather than being defined inductively, implication is built into Coq as the function type constructor.

We have also already seen the definition of [True].  For a demonstration of a lower-level way of establishing proofs of inductive predicates, we turn to this trivial theorem. *)
*)

(**
Coqでは，命題の結合記号のうち最も基本的なのは含意であり，[->]で表します．これは今までのほぼ全ての証明でも使ってきました．
含意は，帰納的に（Inductiveを使って）定義されているわけではなく，むしろCoqに関数型のコンストラクタとして組み込まれています．
既に[True]の定義は紹介してあります．
次の自明な定理を通して，帰納的な述語の証明における低レベル部分の様子を説明していきます．
*)
  
  Theorem obvious : True.
(* begin thide *)
    apply I.
(* end thide *)
  Qed.

(**
  (** We may always use the [apply] tactic to take a proof step based on applying a particular constructor of the inductive predicate that we are trying to establish.  Sometimes there is only one constructor that could possibly apply, in which case a shortcut is available:%\index{tactics!constructor}% *)
*)

(**
構成しようとしている帰納的な述語のコンストラクタをつかって証明を進めるために[apply]タクティクを使うことができます．
時には，適用しうるコンストラクタがただ1つしかないことがあります．そのような場合は以下のようにショートカットが使えます．
*)  

(* begin thide *)
  Theorem obvious' : True.
    constructor.
  Qed.

(* end thide *)

(**
  (** There is also a predicate [False], which is the Curry-Howard mirror image of [Empty_set] from the last chapter. *)
*)
(**
また，[False]という述語もあります．これは[Empty_set]のカリーハワード鏡像です．
*)

  Print False.
  (** %\vspace{-.15in}%[[
  Inductive False : Prop :=
  ]]
  
(*
  We can conclude anything from [False], doing case analysis on a proof of [False] in the same way we might do case analysis on, say, a natural number.  Since there are no cases to consider, any such case analysis succeeds immediately in proving the goal. *)
例えば自然数に対してと同じケース分析を[False]に対しても行うことで，[False]からはあらゆる結論を導くことができます．
考えるべきケースがないため，そのようなケース分析は即時に成功しゴールを証明してしまいます．
*)

  Theorem False_imp : False -> 2 + 2 = 5.
(* begin thide *)
    destruct 1.
(* end thide *)
  Qed.

(**
  (** In a consistent context, we can never build a proof of [False].  In inconsistent contexts that appear in the courses of proofs, it is usually easiest to proceed by demonstrating the inconsistency with an explicit proof of [False]. *)
*)

(**
無矛盾のコンテキストからは[False]の証明は作れません．
証明の過程の途中に出てくる矛盾したコンテキストでは，明確な[False]の証明により矛盾を証明して進むのが通常は最も簡単です．
*)

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
(* begin thide *)
    intro.

(**
    (** At this point, we have an inconsistent hypothesis [2 + 2 = 5], so the specific conclusion is not important.  We use the %\index{tactics!elimtype}%[elimtype] tactic.  For a full description of it, see the Coq manual.  For our purposes, we only need the variant [elimtype False], which lets us replace any conclusion formula with [False], because any fact follows from an inconsistent context. *)
*)

(**
この時点で，矛盾した仮定[2 + 2 = 5]があるので，特定の結論には意味がないのです．
このような時は[elimtype]タクティクを使います．
それの完全な説明はCoqドキュメントをあたってください．
ここで目的のためには，その変種の[elimtype False]のみを使って結論を[False]にします．なぜなら，矛盾したコンテキストからは任意の事実が従うからです．
*)

    elimtype False.
    (** [[
  H : 2 + 2 = 5
  ============================
   False
 
   ]]

   (** For now, we will leave the details of this proof about arithmetic to [crush]. *)
   ここで，算術の残っていますが，[crush]を使います．*)

    crush.
(* end thide *)
  Qed.

(**
  (** A related notion to [False] is logical negation. *)
  論理否定は[False]に関係のある概念です．
*)

  (* begin hide *)
  Definition foo := not.
  (* end hide *)

  Print not.
  (** %\vspace{-.15in}% [[
    not = fun A : Prop => A -> False
      : Prop -> Prop
     ]]

(**
     We see that [not] is just shorthand for implication of [False].  We can use that fact explicitly in proofs.  The syntax [~ P] %(written with a tilde in ASCII)% expands to [not P].
*)
上記で[not]は[False]への含意のことだとわかります．
この事実を照明中に明示的に使用することもできます．
[~ P]という文法（ASCII文字のチルダを使う）で[not P]と展開されます．
 *)

  Theorem arith_neq' : ~ (2 + 2 = 5).
(* begin thide *)
    unfold not.
    (** [[
  ============================
   2 + 2 = 5 -> False
   ]]
   *)

    crush.
(* end thide *)
  Qed.

(**
  (** We also have conjunction, which we introduced in the last chapter. *)
*)

(**
先の章で導入した連言（「かつ」のこと）もまたあります．
*)

  Print and.
(** %\vspace{-.15in}%[[
    Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
  ]]
  (**
  The interested reader can check that [and] has a Curry-Howard equivalent called %\index{Gallina terms!prod}%[prod], the type of pairs.  However, it is generally most convenient to reason about conjunction using tactics.  An explicit proof of commutativity of [and] illustrates the usual suspects for such tasks.  The operator [/\] is an infix shorthand for [and]. *)
興味を持った読者は [and] は [prod] （ペアの型）というカリーハワード同値を持つことを確かめられるでしょう．
しかし，連言を証明するにはタクティクを使ってするのが最も便利です．
[and] の可換性を明示的に証明することでそれが確認できます．
[/\]演算子は[and]の中置略記です．
*)

  Theorem and_comm : P /\ Q -> Q /\ P.

(* begin thide *)
(**
    (** We start by case analysis on the proof of [P /\ Q]. *)
[P /\ Q] のケース分析からはじめます．
*)

    destruct 1.
    (** [[
  H : P
  H0 : Q
  ============================
   Q /\ P
   
   ]]

(**
    Every proof of a conjunction provides proofs for both conjuncts, so we get a single subgoal reflecting that.  We can proceed by splitting this subgoal into a case for each conjunct of [Q /\ P].%\index{tactics!split}% *)
連言の証明はそれぞれの連言肢の証明を含んでいます（ので仮定がPとQになりました）．
それを反映したサブゴールができました．
このサブゴール [Q /\ P] のそれぞれの連言肢のケースに分割することで証明を進めることができます．
*)

    split.
(** [[
2 subgoals
  
  H : P
  H0 : Q
  ============================
   Q

subgoal 2 is

   P
 
 ]]

(**
 In each case, the conclusion is among our hypotheses, so the %\index{tactics!assumption}%[assumption] tactic finishes the process. *)
それぞのケースで，結論は過程と同じですので，[assumption]タクティクで証明を完了します．
*)

    assumption.
    assumption.
(* end thide *)
  Qed.

(**
  (** Coq disjunction is called %\index{Gallina terms!or}%[or] and abbreviated with the infix operator [\/]. *)
Coqの選言は[or]という名前で，中置演算子[\/]で使えます．
*)

  Print or.
(** %\vspace{-.15in}%[[
  Inductive or (A : Prop) (B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B
]]

(**
We see that there are two ways to prove a disjunction: prove the first disjunct or prove the second.  The Curry-Howard analogue of this is the Coq %\index{Gallina terms!sum}%[sum] type.  We can demonstrate the main tactics here with another proof of commutativity. *)
*)
(**
選言を証明する方法が2つあることがわかりました：1つめの連言肢を証明するか，2つめの連言肢を証明するかです．
カリーハワード対応による類似物はCoqの[sum]型です．
可換性をもう一度証明することで，主要なタクティクを実演しましょう．
*)

  Theorem or_comm : P \/ Q -> Q \/ P.

(* begin thide *)
(**
    (** As in the proof for [and], we begin with case analysis, though this time we are met by two cases instead of one. *)
*)
(**
[and]の証明のときと同様にケース分析から始めますが，今回はケースが2つあります．
*)

    destruct 1.
(** [[
2 subgoals
  
  H : P
  ============================
   Q \/ P

subgoal 2 is

 Q \/ P
 
 ]]

(**
 We can see that, in the first subgoal, we want to prove the disjunction by proving its second disjunct.  The %\index{tactics!right}%[right] tactic telegraphs this intent. *)
 *)
 (**
 最初のサブゴールにおいては，2つめの選言肢を証明することで（ゴールの）選言を証明したいのだとわかります．
 [right]タクティクによってその意図を伝えることができます．
 *)

    right; assumption.
(**
    (** The second subgoal has a symmetric proof.%\index{tactics!left}%
2つ目のサブゴールは対称的な証明を持ちます．
*)
       [[
1 subgoal
  
  H : Q
  ============================
   Q \/ P
   ]]
   *)

    left; assumption.

(* end thide *)
  Qed.


(* begin hide *)
(* In-class exercises *)

  Theorem contra : P -> ~P -> R.
(* begin thide *)
    unfold not.
    intros.
    elimtype False.
    apply H0.
    assumption.
(* end thide *)
  Admitted.

  Theorem and_assoc : (P /\ Q) /\ R -> P /\ (Q /\ R).
(* begin thide *)
    intros.
    destruct H.
    destruct H.
    split.
    assumption.
    split.
    assumption.
    assumption.
(* end thide *)
  Admitted.

  Theorem or_assoc : (P \/ Q) \/ R -> P \/ (Q \/ R).
(* begin thide *)
    intros.
    destruct H.
    destruct H.
    left.
    assumption.
    right.
    left.
    assumption.
    right.
    right.
    assumption.
(* end thide *)
  Admitted.

(* end hide *)

(**
  (** It would be a shame to have to plod manually through all proofs about propositional logic.  Luckily, there is no need.  One of the most basic Coq automation tactics is %\index{tactics!tauto}%[tauto], which is a complete decision procedure for constructive propositional logic.  (More on what "constructive" means in the next section.)  We can use [tauto] to dispatch all of the purely propositional theorems we have proved so far. *)
*)
(**
命題論理の全ての証明を手動でこつこつ進めないといけないというのは残念なことです．
幸運なことに，その必要はありません．
最も基本的なCoqの自動化タクティクの1つである[tauto]は，構成的な命題論理の完全な決定手続きです（「構成的」の意味については次の節でより詳しく説明します）．
ここまで証明してきた純粋な命題論理の定理は[tauto]を使うことで片付けることができます．
*)

  Theorem or_comm' : P \/ Q -> Q \/ P.
(* begin thide *)
    tauto.
(* end thide *)
  Qed.

(**
  (** Sometimes propositional reasoning forms important plumbing for the proof of a theorem, but we still need to apply some other smarts about, say, arithmetic.  The tactic %\index{tactics!intuition}%[intuition] is a generalization of [tauto] that proves everything it can using propositional reasoning.  When some further facts must be established to finish the proof, [intuition] uses propositional laws to simplify them as far as possible.  Consider this example, which uses the list concatenation operator %\coqdocnotation{%#<tt>#++#</tt>#%}% from the standard library. *)
*)

(**
命題論理的な理由づけは定理の証明の重要な部品になることもたまにはありますが，他の知恵が必要になることもあります．例えば算術です．
[intuition]タクティクは[tauto]の一般化で，命題論理的な推論で証明できる全てを証明できます．
証明を完了させるのにさらに他の事実が必要な場合でも，[intuition]は命題の法則を使ってなるべく簡単にしてくれます．
次の例を考えて下さい．ここでは標準ライブラリのリスト連結演算%\coqdocnotation{%#<tt>#++#</tt>#%}%を使っています．
*)

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
(* begin thide *)
    intuition.

(**
    (** A lot of the proof structure has been generated for us by [intuition], but the final proof depends on a fact about lists.  The remaining subgoal hints at what cleverness we need to inject. *)
*)

(**
多くの証明構造が[intuition]によって生成されますが，最終的な証明はリストに関する事実のみによっています．
残りのサブゴールは人間が他にどんな知恵を入れなければならないかを示しています．
*)

    (** [[
  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2
 
   ]]

(**
   We can see that we need a theorem about lengths of concatenated lists, which we proved last chapter and is also in the standard library. *)
連結されたリストの長さについての定理が必要だとわかります．その定理については前の章でも証明したし，標準ライブラリにも含まれています．
*)

    rewrite app_length.
    (** [[
  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length ls1 + length ls2 = 6 \/ length ls1 = length ls2
 
   ]]

(**
   Now the subgoal follows by purely propositional reasoning.  That is, we could replace [length ls1 + length ls2 = 6] with [P] and [length ls1 = length ls2] with [Q] and arrive at a tautology of propositional logic. *)
ここまで来たら，純粋な命題論理の推論でサブゴールは証明できます．
すなわち，[length ls1 + length ls2 = 6]を[P]と考え，[length ls1 = length ls2]を[Q]と考えて命題論理のトートロジに到達します．
*)

    tauto.
(* end thide *)
  Qed.

(**
  (** The [intuition] tactic is one of the main bits of glue in the implementation of [crush], so, with a little help, we can get a short automated proof of the theorem. *)
*)

(**
[intuition]タクティクは[crush]の実装の主要なつなぎの1つです．
そのため，少し助けることで定理に対する短くて自動化された証明を得ることができます．
*)

(* begin thide *)
  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.

    crush.
  Qed.
(* end thide *)

End Propositional.

(**
(** Ending the section here has the same effect as always.  Each of our propositional theorems becomes universally quantified over the propositional variables that we used. *)
*)

(**
セクションの終わりの意味はいつもと同じです．
ここで定義した命題の定理は普遍的に量化されます．
*)

(**
(** * What Does It Mean to Be Constructive? *)
*)
(** * 構成的とはどういうことか? *)

(**
(** One potential point of confusion in the presentation so far is the distinction between [bool] and [Prop].  The datatype [bool] is built from two values [true] and [false], while [Prop] is a more primitive type that includes among its members [True] and [False].  Why not collapse these two concepts into one, and why must there be more than two states of mathematical truth, [True] and [False]?

The answer comes from the fact that Coq implements%\index{constructive logic}% _constructive_ or%\index{intuitionistic logic|see{constructive logic}}% _intuitionistic_ logic, in contrast to the%\index{classical logic}% _classical_ logic that you may be more familiar with.  In constructive logic, classical tautologies like [~ ~ P -> P] and [P \/ ~ P] do not always hold.  In general, we can only prove these tautologies when [P] is%\index{decidability}% _decidable_, in the sense of %\index{computability|see{decidability}}%computability theory.  The Curry-Howard encoding that Coq uses for [or] allows us to extract either a proof of [P] or a proof of [~ P] from any proof of [P \/ ~ P].  Since our proofs are just functional programs which we can run, a general %\index{law of the excluded middle}%law of the excluded middle would give us a decision procedure for the halting problem, where the instantiations of [P] would be formulas like "this particular Turing machine halts."

A similar paradoxical situation would result if every proposition evaluated to either [True] or [False].  Evaluation in Coq is decidable, so we would be limiting ourselves to decidable propositions only.

Hence the distinction between [bool] and [Prop].  Programs of type [bool] are computational by construction; we can always run them to determine their results.  Many [Prop]s are undecidable, and so we can write more expressive formulas with [Prop]s than with [bool]s, but the inevitable consequence is that we cannot simply "run a [Prop] to determine its truth."

Constructive logic lets us define all of the logical connectives in an aesthetically appealing way, with orthogonal inductive definitions.  That is, each connective is defined independently using a simple, shared mechanism.  Constructivity also enables a trick called%\index{program extraction}% _program extraction_, where we write programs by phrasing them as theorems to be proved.  Since our proofs are just functional programs, we can extract executable programs from our final proofs, which we could not do as naturally with classical proofs.

We will see more about Coq's program extraction facility in a later chapter.  However, I think it is worth interjecting another warning at this point, following up on the prior warning about taking the Curry-Howard correspondence too literally.  It is possible to write programs by theorem-proving methods in Coq, but hardly anyone does it.  It is almost always most useful to maintain the distinction between programs and proofs.  If you write a program by proving a theorem, you are likely to run into algorithmic inefficiencies that you introduced in your proof to make it easier to prove.  It is a shame to have to worry about such situations while proving tricky theorems, and it is a happy state of affairs that you almost certainly will not need to, with the ideal of extracting programs from proofs being confined mostly to theoretical studies. *)
*)

(**
ここまで提示してきたことのなかで混乱しそうなことは，[bool]と[Prop]の区別です．
[bool]というデータ型は[true]と[false]という2つの値から構成されていますが，[Prop]はより原始的な型で，[True]や[False]といった要素は[Prop]に含まれます．
これら2つ（boolとProp）の概念を1つにまとめてしまってはどうでしょうか？
また，[True]と[False]という2つの真偽状態以外が存在するとはどのようなことでしょうか？

Coqは＿構成的＿あるいは＿直観主義的＿な論理学に基づいている，というとこから答えが出てきます．
古典論理だったら，もっと馴染みがあったでしょうが．
構成的な論理では，古典的な恒真命題すなわち[~ ~ P -> P]や[P \/ ~ P]は常には成り立ちません．
一般的には，これらの恒真命題を証明できるのは[P]が計算可能性の理論でいう＿決定可能＿の場合のみです．
Coqが使っている[or]のカリーハワード埋め込みによると，[P \/ ~ P]の証明から[P]の証明または[~ P]の証明が抽出できるということになります．
我々の証明は実行可能なただの関数型プログラムなので，一般的な排中律を許してしまうと停止問題への決定手続きを与えることになってしまうのです．停止問題として例えば「このチューリングマシンは停止する」というようなものも選べます．

同様の矛盾がある状況は全ての命題は[True]または[False]に評価されるとした倍にも発生します．
Coqにおける評価は決定可能ですので，命題も決定可能なものに限ることにしています．

ということで[bool]と[Prop]の区別があるのです．[bool]型のプログラムは作った時から計算的です・・・結果を決めるために実行することは常に可能です．
多くの[Prop]は決定不能なので，[bool]に比べて[Prop]を使えばより表現力豊かに式を書くことができます．
しかし，避けられない結末として，「真偽を確かめるために[Prop]を実行する」ことはできなくなってしまいます．

構成的な論理によって全ての論理結合記号を審美的な魅力のある方法で定義できるようになります．
直交した帰納的な定義です．
すなわち，それぞれの結合記号は単純な共通の仕組みを使って独立に定義されます．
構成的であることで，プログラム抽出ということもできるようになります．
そこでは，プログラムを定理として記述して証明します．
我々の証明はただの関数型プログラムなので，実行できるプログラムを最終的な証明から抽出できます．これは，古典的な証明からは自然に行うことはできませんでした．

後の章でCoqのプログラム抽出機能についてもっと見ていきます．
しかしここでひとつ注意をしておきましょう．先に注意したカリーハワード対応を文面通りに受け取りすぎることです．
プログラムをCoqの定理証明を使って書くことはできますが，そんなことをする人はほぼいません．
証明とプログラムの区別を常にしておくことは最も有用です．
もしも定理を証明することでプログラムを書いてしまったら，おそらく，証明を簡単にするためにアルゴリズムが非効率的になってしまうでしょう．
微妙な定理を証明してる時にそのような状況を心配しないといけないというのは恥ずかしいことです．ですが，おそらくそのような必要はありません．
というのは，証明からプログラムを抽出するという理想は理論的な研究に限定されているからです．
*)

(** * First-Order Logic *)

(** The %\index{Gallina terms!forall}%[forall] connective of first-order logic, which we have seen in many examples so far, is built into Coq.  Getting ahead of ourselves a bit, we can see it as the dependent function type constructor.  In fact, implication and universal quantification are just different syntactic shorthands for the same Coq mechanism.  A formula [P -> Q] is equivalent to [forall x : P, Q], where [x] does not appear in [Q].  That is, the "real" type of the implication says "for every proof of [P], there exists a proof of [Q]."

%\index{existential quantification}\index{Gallina terms!exists}\index{Gallina terms!ex}%Existential quantification is defined in the standard library. *)

  Print ex.
(** %\vspace{-.15in}%[[
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
    ]]

  (Note that here, as always, each [forall] quantifier has the largest possible scope, so that the type of [ex_intro] could also be written [forall x : A, (P x -> ex P)].)

  The family [ex] is parameterized by the type [A] that we quantify over, and by a predicate [P] over [A]s.  We prove an existential by exhibiting some [x] of type [A], along with a proof of [P x].  As usual, there are tactics that save us from worrying about the low-level details most of the time.

  Here is an example of a theorem statement with existential quantification.  We use the equality operator [=], which, depending on the settings in which they learned logic, different people will say either is or is not part of first-order logic.  For our purposes, it is. *)

Theorem exist1 : exists x : nat, x + 1 = 2.
(* begin thide *)
  (** remove printing exists *)
  (** We can start this proof with a tactic %\index{tactics!exists}%[exists], which should not be confused with the formula constructor shorthand of the same name.  %In the version of this document that you are reading, the reverse ``E'' appears instead of the text ``exists'' in formulas.% *)

  exists 1.

  (** The conclusion is replaced with a version using the existential witness that we announced.

     [[
  ============================
   1 + 1 = 2
   ]]
   *)

  reflexivity.
(* end thide *)
Qed.

(** printing exists $\exists$ *)

(** We can also use tactics to reason about existential hypotheses. *)

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
(* begin thide *)
  (** We start by case analysis on the proof of the existential fact. *)

  destruct 1.
  (** [[
  n : nat
  m : nat
  x : nat
  H : n + x = m
  ============================
   n <= m
 
   ]]

   The goal has been replaced by a form where there is a new free variable [x], and where we have a new hypothesis that the body of the existential holds with [x] substituted for the old bound variable.  From here, the proof is just about arithmetic and is easy to automate. *)

  crush.
(* end thide *)
Qed.


(* begin hide *)
(* In-class exercises *)

Theorem forall_exists_commute : forall (A B : Type) (P : A -> B -> Prop),
  (exists x : A, forall y : B, P x y) -> (forall y : B, exists x : A, P x y).
(* begin thide *)
  intros.
  destruct H.
  exists x.
  apply H.
(* end thide *)
Admitted.

(* end hide *)


(** The tactic [intuition] has a first-order cousin called %\index{tactics!firstorder}%[firstorder], which proves many formulas when only first-order reasoning is needed, and it tries to perform first-order simplifications in any case.  First-order reasoning is much harder than propositional reasoning, so [firstorder] is much more likely than [intuition] to get stuck in a way that makes it run for long enough to be useless. *)


(** * Predicates with Implicit Equality *)

(** We start our exploration of a more complicated class of predicates with a simple example: an alternative way of characterizing when a natural number is zero. *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
(* begin thide *)
  constructor.
(* end thide *)
Qed.

(** We can call [isZero] a%\index{judgment}% _judgment_, in the sense often used in the semantics of programming languages.  Judgments are typically defined in the style of%\index{natural deduction}% _natural deduction_, where we write a number of%\index{inference rules}% _inference rules_ with premises appearing above a solid line and a conclusion appearing below the line.  In this example, the sole constructor [IsZero] of [isZero] can be thought of as the single inference rule for deducing [isZero], with nothing above the line and [isZero 0] below it.  The proof of [isZero_zero] demonstrates how we can apply an inference rule.  (Readers not familiar with formal semantics should not worry about not following this paragraph!)

The definition of [isZero] differs in an important way from all of the other inductive definitions that we have seen in this and the previous chapter.  Instead of writing just [Set] or [Prop] after the colon, here we write [nat -> Prop].  We saw examples of parameterized types like [list], but there the parameters appeared with names _before_ the colon.  Every constructor of a parameterized inductive type must have a range type that uses the same parameter, whereas the form we use here enables us to choose different arguments to the type for different constructors.

For instance, our definition [isZero] makes the predicate provable only when the argument is [0].  We can see that the concept of equality is somehow implicit in the inductive definition mechanism.  The way this is accomplished is similar to the way that logic variables are used in %\index{Prolog}%Prolog (but worry not if not familiar with Prolog), and it is a very powerful mechanism that forms a foundation for formalizing all of mathematics.  In fact, though it is natural to think of inductive types as folding in the functionality of equality, in Coq, the true situation is reversed, with equality defined as just another inductive type!%\index{Gallina terms!eq}\index{Gallina terms!refl\_equal}% *)

Print eq.
(** %\vspace{-.15in}%[[
  Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x
  ]]

  Behind the scenes, uses of infix [=] are expanded to instances of [eq].  We see that [eq] has both a parameter [x] that is fixed and an extra unnamed argument of the same type.  The type of [eq] allows us to state any equalities, even those that are provably false.  However, examining the type of equality's sole constructor [eq_refl], we see that we can only _prove_ equality when its two arguments are syntactically equal.  This definition turns out to capture all of the basic properties of equality, and the equality-manipulating tactics that we have seen so far, like [reflexivity] and [rewrite], are implemented treating [eq] as just another inductive type with a well-chosen definition.  Another way of stating that definition is: equality is defined as the least reflexive relation.

Returning to the example of [isZero], we can see how to work with hypotheses that use this predicate. *)

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
(* begin thide *)
  (** We want to proceed by cases on the proof of the assumption about [isZero]. *)

  destruct 1.
  (** [[
  n : nat
  ============================
   n + 0 = n
 
   ]]

   Since [isZero] has only one constructor, we are presented with only one subgoal.  The argument [m] to [isZero] is replaced with that type's argument from the single constructor [IsZero].  From this point, the proof is trivial. *)

  crush.
(* end thide *)
Qed.

(** Another example seems at first like it should admit an analogous proof, but in fact provides a demonstration of one of the most basic gotchas of Coq proving. *)

Theorem isZero_contra : isZero 1 -> False.
(* begin thide *)
  (** Let us try a proof by cases on the assumption, as in the last proof. *)

  destruct 1.
  (** [[
  ============================
   False
 
   ]]

   It seems that case analysis has not helped us much at all!  Our sole hypothesis disappears, leaving us, if anything, worse off than we were before.  What went wrong?  We have met an important restriction in tactics like [destruct] and [induction] when applied to types with arguments.  If the arguments are not already free variables, they will be replaced by new free variables internally before doing the case analysis or induction.  Since the argument [1] to [isZero] is replaced by a fresh variable, we lose the crucial fact that it is not equal to [0].

     Why does Coq use this restriction?  We will discuss the issue in detail in a future chapter, when we see the dependently typed programming techniques that would allow us to write this proof term manually.  For now, we just say that the algorithmic problem of "logically complete case analysis" is undecidable when phrased in Coq's logic.  A few tactics and design patterns that we will present in this chapter suffice in almost all cases.  For the current example, what we want is a tactic called %\index{tactics!inversion}%[inversion], which corresponds to the concept of inversion that is frequently used with natural deduction proof systems.  (Again, worry not if the semantics-oriented terminology from this last sentence is unfamiliar.) *)

  Undo.
  inversion 1.
(* end thide *)
Qed.

(** What does [inversion] do?  Think of it as a version of [destruct] that does its best to take advantage of the structure of arguments to inductive types.  In this case, [inversion] completed the proof immediately, because it was able to detect that we were using [isZero] with an impossible argument.

Sometimes using [destruct] when you should have used [inversion] can lead to confusing results.  To illustrate, consider an alternate proof attempt for the last theorem. *)

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
  (** [[
  ============================
   1 + 1 = 4
 
   ]]

   What on earth happened here?  Internally, [destruct] replaced [1] with a fresh variable, and, trying to be helpful, it also replaced the occurrence of [1] within the unary representation of each number in the goal.  Then, within the [O] case of the proof, we replace the fresh variable with [O].  This has the net effect of decrementing each of these numbers. *)

Abort.

(** To see more clearly what is happening, we can consider the type of [isZero]'s induction principle. *)

Check isZero_ind.
(** %\vspace{-.15in}% [[
isZero_ind
     : forall P : nat -> Prop, P 0 -> forall n : nat, isZero n -> P n
   ]]

   In our last proof script, [destruct] chose to instantiate [P] as [fun n => S n + S n = S (S (S (S n)))].  You can verify for yourself that this specialization of the principle applies to the goal and that the hypothesis [P 0] then matches the subgoal we saw generated.  If you are doing a proof and encounter a strange transmutation like this, there is a good chance that you should go back and replace a use of [destruct] with [inversion]. *)


(* begin hide *)
(* In-class exercises *)

(* EX: Define an inductive type capturing when a list has exactly two elements.  Prove that your predicate does not hold of the empty list, and prove that, whenever it holds of a list, the length of that list is two. *)

(* begin thide *)
Section twoEls.
  Variable A : Type.

  Inductive twoEls : list A -> Prop :=
  | TwoEls : forall x y, twoEls (x :: y :: nil).

  Theorem twoEls_nil : twoEls nil -> False.
    inversion 1.
  Qed.

  Theorem twoEls_two : forall ls, twoEls ls -> length ls = 2.
    inversion 1.
    reflexivity.
  Qed.
End twoEls.
(* end thide *)

(* end hide *)


(** * Recursive Predicates *)

(** We have already seen all of the ingredients we need to build interesting recursive predicates, like this predicate capturing even-ness. *)

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

(** Think of [even] as another judgment defined by natural deduction rules.  The rule [EvenO] has nothing above the line and [even O] below the line, and [EvenSS] is a rule with [even n] above the line and [even (S (S n))] below.

The proof techniques of the last section are easily adapted. *)

Theorem even_0 : even 0.
(* begin thide *)
  constructor.
(* end thide *)
Qed.

Theorem even_4 : even 4.
(* begin thide *)
  constructor; constructor; constructor.
(* end thide *)
Qed.

(** It is not hard to see that sequences of constructor applications like the above can get tedious.  We can avoid them using Coq's hint facility, with a new [Hint] variant that asks to consider all constructors of an inductive type during proof search.  The tactic %\index{tactics!auto}%[auto] performs exhaustive proof search up to a fixed depth, considering only the proof steps we have registered as hints. *)

(* begin thide *)
Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

(* end thide *)

(** We may also use [inversion] with [even]. *)

Theorem even_1_contra : even 1 -> False.
(* begin thide *)
  inversion 1.
(* end thide *)
Qed.

Theorem even_3_contra : even 3 -> False.
(* begin thide *)
  inversion 1.
  (** [[
  H : even 3
  n : nat
  H1 : even 1
  H0 : n = 1
  ============================
   False
 
   ]]

   The [inversion] tactic can be a little overzealous at times, as we can see here with the introduction of the unused variable [n] and an equality hypothesis about it.  For more complicated predicates, though, adding such assumptions is critical to dealing with the undecidability of general inversion.  More complex inductive definitions and theorems can cause [inversion] to generate equalities where neither side is a variable. *)

  inversion H1.
(* end thide *)
Qed.

(** We can also do inductive proofs about [even]. *)

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
(* begin thide *)
  (** It seems a reasonable first choice to proceed by induction on [n]. *)

  induction n; crush.
  (** [[
  n : nat
  IHn : forall m : nat, even n -> even m -> even (n + m)
  m : nat
  H : even (S n)
  H0 : even m
  ============================
   even (S (n + m))
 
   ]]

   We will need to use the hypotheses [H] and [H0] somehow.  The most natural choice is to invert [H]. *)

  inversion H.
  (** [[
  n : nat
  IHn : forall m : nat, even n -> even m -> even (n + m)
  m : nat
  H : even (S n)
  H0 : even m
  n0 : nat
  H2 : even n0
  H1 : S n0 = n
  ============================
   even (S (S n0 + m))
 
   ]]

  Simplifying the conclusion brings us to a point where we can apply a constructor. *)

  simpl.
  (** [[
  ============================
   even (S (S (n0 + m)))
   ]]
   *)

  constructor.

(** [[
  ============================
   even (n0 + m)
 
   ]]

   At this point, we would like to apply the inductive hypothesis, which is:

   [[
  IHn : forall m : nat, even n -> even m -> even (n + m)
 
  ]]

  Unfortunately, the goal mentions [n0] where it would need to mention [n] to match [IHn].  We could keep looking for a way to finish this proof from here, but it turns out that we can make our lives much easier by changing our basic strategy.  Instead of inducting on the structure of [n], we should induct _on the structure of one of the [even] proofs_.  This technique is commonly called%\index{rule induction}% _rule induction_ in programming language semantics.  In the setting of Coq, we have already seen how predicates are defined using the same inductive type mechanism as datatypes, so the fundamental unity of rule induction with "normal" induction is apparent.

  Recall that tactics like [induction] and [destruct] may be passed numbers to refer to unnamed lefthand sides of implications in the conclusion, where the argument [n] refers to the [n]th such hypothesis. *)

Restart.

  induction 1.
(** [[
  m : nat
  ============================
   even m -> even (0 + m)
]]

%\noindent \coqdockw{subgoal} 2 \coqdockw{is}:%#<tt>subgoal 2 is</tt>#
[[
 even m -> even (S (S n) + m)
 
 ]]

 The first case is easily discharged by [crush], based on the hint we added earlier to try the constructors of [even]. *)

  crush.

  (** Now we focus on the second case: *)

  intro.
  (** [[
  m : nat
  n : nat
  H : even n
  IHeven : even m -> even (n + m)
  H0 : even m
  ============================
   even (S (S n) + m)
 
   ]]

   We simplify and apply a constructor, as in our last proof attempt. *)

  simpl; constructor.

(** [[
  ============================
   even (n + m)
 
   ]]

   Now we have an exact match with our inductive hypothesis, and the remainder of the proof is trivial. *)

  apply IHeven; assumption.

  (** In fact, [crush] can handle all of the details of the proof once we declare the induction strategy. *)

Restart.

  induction 1; crush.
(* end thide *)
Qed.

(** Induction on recursive predicates has similar pitfalls to those we encountered with inversion in the last section. *)

Theorem even_contra : forall n, even (S (n + n)) -> False.
(* begin thide *)
  induction 1.
  (** [[
  n : nat
  ============================
   False
]]

%\noindent \coqdockw{subgoal} 2 \coqdockw{is}:%#<tt>subgoal 2 is</tt>#
[[
 False
 
 ]]

 We are already sunk trying to prove the first subgoal, since the argument to [even] was replaced by a fresh variable internally.  This time, we find it easier to prove this theorem by way of a lemma.  Instead of trusting [induction] to replace expressions with fresh variables, we do it ourselves, explicitly adding the appropriate equalities as new assumptions. *)

Abort.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.

  (** At this point, it is useful to consider all cases of [n] and [n0] being zero or nonzero.  Only one of these cases has any trickiness to it. *)

  destruct n; destruct n0; crush.

  (** [[
  n : nat
  H : even (S n)
  IHeven : forall n0 : nat, S n = S (n0 + n0) -> False
  n0 : nat
  H0 : S n = n0 + S n0
  ============================
   False
 
   ]]

  At this point it is useful to use a theorem from the standard library, which we also proved with a different name in the last chapter.  We can search for a theorem that allows us to rewrite terms of the form [x + S y]. *)

  SearchRewrite (_ + S _).
(** %\vspace{-.15in}%[[
  plus_n_Sm : forall n m : nat, S (n + m) = n + S m
     ]]
     *)

  rewrite <- plus_n_Sm in H0.

  (** The induction hypothesis lets us complete the proof, if we use a variant of [apply] that has a %\index{tactics!with}%[with] clause to give instantiations of quantified variables. *)

  apply IHeven with n0; assumption.

  (** As usual, we can rewrite the proof to avoid referencing any locally generated names, which makes our proof script more readable and more robust to changes in the theorem statement.  We use the notation [<-] to request a hint that does right-to-left rewriting, just like we can with the [rewrite] tactic. *)

  Restart.

  Hint Rewrite <- plus_n_Sm.

  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.
Qed.

(** We write the proof in a way that avoids the use of local variable or hypothesis names, using the %\index{tactics!match}%[match] tactic form to do pattern-matching on the goal.  We use unification variables prefixed by question marks in the pattern, and we take advantage of the possibility to mention a unification variable twice in one pattern, to enforce equality between occurrences.  The hint to rewrite with [plus_n_Sm] in a particular direction saves us from having to figure out the right place to apply that theorem.

The original theorem now follows trivially from our lemma, using a new tactic %\index{tactics!eauto}%[eauto], a fancier version of [auto] whose explanation we postpone to Chapter 13. *)

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

(** We use a variant %\index{tactics!apply}%[eapply] of [apply] which has the same relationship to [apply] as [eauto] has to [auto].  An invocation of [apply] only succeeds if all arguments to the rule being used can be determined from the form of the goal, whereas [eapply] will introduce unification variables for undetermined arguments.  In this case, [eauto] is able to determine the right values for those unification variables, using (unsurprisingly) a variant of the classic algorithm for _unification_ %\cite{unification}%.

By considering an alternate attempt at proving the lemma, we can see another common pitfall of inductive proofs in Coq.  Imagine that we had tried to prove [even_contra'] with all of the [forall] quantifiers moved to the front of the lemma statement. *)

Lemma even_contra'' : forall n' n, even n' -> n' = S (n + n) -> False.
  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.

  (** One subgoal remains:

     [[
  n : nat
  H : even (S (n + n))
  IHeven : S (n + n) = S (S (S (n + n))) -> False
  ============================
   False
 
   ]]

   We are out of luck here.  The inductive hypothesis is trivially true, since its assumption is false.  In the version of this proof that succeeded, [IHeven] had an explicit quantification over [n].  This is because the quantification of [n] _appeared after the thing we are inducting on_ in the theorem statement.  In general, quantified variables and hypotheses that appear before the induction object in the theorem statement stay fixed throughout the inductive proof.  Variables and hypotheses that are quantified after the induction object may be varied explicitly in uses of inductive hypotheses. *)

Abort.

(** Why should Coq implement [induction] this way?  One answer is that it avoids burdening this basic tactic with additional heuristic smarts, but that is not the whole picture.  Imagine that [induction] analyzed dependencies among variables and reordered quantifiers to preserve as much freedom as possible in later uses of inductive hypotheses.  This could make the inductive hypotheses more complex, which could in turn cause particular automation machinery to fail when it would have succeeded before.  In general, we want to avoid quantifiers in our proofs whenever we can, and that goal is furthered by the refactoring that the [induction] tactic forces us to do. *)
(* end thide *)




(* begin hide *)
(* In-class exercises *)

(* EX: Define a type [prop] of simple Boolean formulas made up only of truth, falsehood, binary conjunction, and binary disjunction.  Define an inductive predicate [holds] that captures when [prop]s are valid, and define a predicate [falseFree] that captures when a [prop] does not contain the "false" formula.  Prove that every false-free [prop] is valid. *)

(* begin thide *)
Inductive prop : Set :=
| Tru : prop
| Fals : prop
| And : prop -> prop -> prop
| Or : prop -> prop -> prop.

Inductive holds : prop -> Prop :=
| HTru : holds Tru
| HAnd : forall p1 p2, holds p1 -> holds p2 -> holds (And p1 p2)
| HOr1 : forall p1 p2, holds p1 -> holds (Or p1 p2)
| HOr2 : forall p1 p2, holds p2 -> holds (Or p1 p2).

Inductive falseFree : prop -> Prop :=
| FFTru : falseFree Tru
| FFAnd : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (And p1 p2)
| FFNot : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (Or p1 p2).

Hint Constructors holds.

Theorem falseFree_holds : forall p, falseFree p -> holds p.
  induction 1; crush.
Qed.
(* end thide *)


(* EX: Define an inductive type [prop'] that is the same as [prop] but omits the possibility for falsehood.  Define a proposition [holds'] for [prop'] that is analogous to [holds].  Define a function [propify] for translating [prop']s to [prop]s.  Prove that, for any [prop'] [p], if [propify p] is valid, then so is [p]. *)

(* begin thide *)
Inductive prop' : Set :=
| Tru' : prop'
| And' : prop' -> prop' -> prop'
| Or' : prop' -> prop' -> prop'.

Inductive holds' : prop' -> Prop :=
| HTru' : holds' Tru'
| HAnd' : forall p1 p2, holds' p1 -> holds' p2 -> holds' (And' p1 p2)
| HOr1' : forall p1 p2, holds' p1 -> holds' (Or' p1 p2)
| HOr2' : forall p1 p2, holds' p2 -> holds' (Or' p1 p2).

Fixpoint propify (p : prop') : prop :=
  match p with
    | Tru' => Tru
    | And' p1 p2 => And (propify p1) (propify p2)
    | Or' p1 p2 => Or (propify p1) (propify p2)
  end.

Hint Constructors holds'.

Lemma propify_holds' : forall p', holds p' -> forall p, p' = propify p -> holds' p.
  induction 1; crush; destruct p; crush.
Qed.

Theorem propify_holds : forall p, holds (propify p) -> holds' p.
  intros; eapply propify_holds'; eauto.
Qed.
(* end thide *)

(* end hide *)

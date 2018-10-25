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


(**
(*
%\part{Basic Programming and Proving}

\chapter{Introducing Inductive Types}%
*)
%\part{基本になるプログラミングと証明}
 
\chapter{帰納型の導入}%
*)

(** 
(* The logical foundation of Coq is the Calculus of Inductive Constructions, or CIC.  In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.  From this modest foundation, we can prove essentially all of the theorems of math and carry out effectively all program verifications, with enough effort expended.  This chapter introduces induction and recursion for functional programming in Coq.  Most of our examples reproduce functionality from the Coq standard library, and I have tried to copy the standard library's choices of identifiers, where possible, so many of the definitions here are already available in the default Coq environment.
*)
Coqが論理の基盤としているのはCIC(Calculus of Inductive Constructions)です．
ある意味では，CICを構成するのは，関数型(function type)と帰納型(inductive type)という2つの簡単な機能だけです．
この簡素な基盤から，本質的にはあらゆる数学の定理を証明できますし，
それなりに手間をかければ，あらゆるプログラム検証を効果的に実行できます．
本章ではCoqにおける関数プログラミングに関して，帰納と再帰の概念を導入します．
またこの章の例は大部分は，Coqの標準ライブラリにある機能を再現するものです．
それに，識別子は可能なかぎり標準ライブラリのものを使うようにしましたので，ここにある定義の多くは，デフォルトのCoq環境では使えるものです．

(*
The last chapter took a deep dive into some of the more advanced Coq features, to highlight the unusual approach that I advocate in this book.  However, from this point on, we will rewind and go back to basics, presenting the relevant features of Coq in a more bottom-up manner.  A useful first step is a discussion of the differences and relationships between proofs and programs in Coq.
*)
前章でCoqの深淵に潜り，本書で主張している特異なアプローチに焦点をあてましたが，ここから先は基本に戻って関連のあるCoqの機能をボトムアップ示しましょう．
はじめの一歩としては，証明とCoqのプログラムの違いと関連について議論するのがよいでしょう．
*)


(**
(* * Proof Terms *)
* 証明項
*)

(** 
(*
Mainstream presentations of mathematics treat proofs as objects that exist outside of the universe of mathematical objects.  However, for a variety of reasoning tasks, it is convenient to encode proofs, traditional mathematical objects, and programs within a single formal language.  Validity checks on mathematical objects are useful in any setting, to catch typos and other uninteresting errors.  The benefits of static typing for programs are widely recognized, and Coq brings those benefits to both mathematical objects and programs via a uniform mechanism.  In fact, from this point on, we will not bother to distinguish between programs and mathematical objects.  Many mathematical formalisms are most easily encoded in terms of programs.
*)
数学では証明を数学の世界の外側にあるものとして扱うのが主流です．
しかし，さまざまな論証作業を行うには，証明や伝統的な数学の対象，
そしてプログラムを単一の形式的言語で符号化するのが便利です．
数学の対象に関して正当性を検査すれば，書き間違いやつまらないミスを見つけるのに役立ちます．
プログラムに静的型付けを行えば，有益であることは広く認知されていることです．
Coqは数学の対象についてもプログラムに関しても同じ機構を使って役に立ってくれます．
そういうわけで，これ以降はプログラムと数学の対象との区別に悩むことはやめします．
多くの数学的形式は簡単にプログラムで符号化できます．

(*
Proofs are fundamentally different from programs, because any two proofs of a theorem are considered equivalent, from a formal standpoint if not from an engineering standpoint.  However, we can use the same type-checking technology to check proofs as we use to validate our programs.  This is the%\index{Curry-Howard correspondence}% _Curry-Howard correspondence_ %\cite{Curry,Howard}%, an approach for relating proofs and programs.  We represent mathematical theorems as types, such that a theorem's proofs are exactly those programs that type-check at the corresponding type.
*)
証明は基本的にはプログラムとは違うものです．
工学的な見方ではなく正式な見方では，1つの定理に対する2つの証明は同じものだからです．
そうはいうものの，証明を検査するにも，プログラムを検証するにも同じ型検査技術が使用できます．
これは，%\index{Curry-Howard対応}% %\emph{Curry-Howard対応}% %\cite{Curry,Howard}%という証明とプログラムを関連付ける方法です．
数学的定理を型として表現すると，その型をもつことが確認されたプログラムそのものが証明になります．

(*
The last chapter's example already snuck in an instance of Curry-Howard.  We used the token [->] to stand for both function types and logical implications.  One reasonable conclusion upon seeing this might be that some fancy overloading of notations is at work.  In fact, functions and implications are precisely identical according to Curry-Howard!  That is, they are just two ways of describing the same computational phenomenon.
*)
前章の例にはCurry-Howardの具体例を忍び込ませていました．
[->]という字句を関数型と論理含意との両方を表すのに使っています．
これを見れば，記法を多重定義しているのだろうと考えるのが理にかないます．

(*
A short demonstration should explain how this can be.  The identity function over the natural numbers is certainly not a controversial program.
*)
どのような仕組みかは簡単な例で示せるはずです．
自然数上の恒等関数は自明なプログラムです．

*)

Check (fun x : nat => x).
(** [: nat -> nat] *)

(**
(*
%\smallskip{}%Consider this alternate program, which is almost identical to the last one.
*)
%\smallskip{}%さきほどとほぼ同じ別の関数を考えましょう．
*)

Check (fun x : True => x).
(** [: True -> True] *)

(**
(* 
%\smallskip{}%The identity program is interpreted as a proof that %\index{Gallina terms!True}%[True], the always-true proposition, implies itself!  What we see is that Curry-Howard interprets implications as functions, where an input is a proposition being assumed and an output is a proposition being deduced.  This intuition is not too far from a common one for informal theorem proving, where we might already think of an implication proof as a process for transforming a hypothesis into a conclusion.
*)
%\smallskip{}%この恒等プログラムは，%\index{Gallina terms!True}%[True]すなわち自分自身を含意する恒真命題の証明と解釈されます．
これかから判ることは，Curry-Howard対応では含意を関数として解釈するということです．
このときの関数への入力は仮定の命題であり，関数からの出力は演繹された命題になります．
この直観は，非形式的におこなわれる定理証明に対する一般的な直観とかけはなれたものではありません．
非形式的な定理証明においても，含意の証明を仮定から結論への変換過程と見なしていると考えられます．

(*
There are also more primitive proof forms available.  For instance, the term %\index{Gallina terms!I}%[I] is the single proof of [True], applicable in any context.
*)
もっとプリミティブな形式を使えます．
たとえば，%\index{Gallina terms!I}%[I]という項は[True]の唯一の証明で，あらゆる文脈で適用可能です．
*)

Check I.
(** [: True] *)

(**
(*
%\smallskip{}%With [I], we can prove another simple propositional theorem.
*)
%\smallskip{}%[I]を使って，別の命題論理における定理が証明できます．
*)

Check (fun _ : False => I).
(** [: False -> True] *)

(**
(* %\smallskip{}%No proofs of %\index{Gallina terms!False}%[False] exist in the top-level context, but the implication-as-function analogy gives us an easy way to, for example, show that [False] implies itself.
*)
%\smallskip{}% %\index{Gallina terms!False}%[False]の証明はトップレベルの文脈には存在しません．
しかし，「関数としての含意」という類推によれば，たとえば，[False]が自分自身を含意することは，簡単に示せます．
*)

Check (fun x : False => x).
(** [: False -> False] *)

(**
(*
%\smallskip{}%Every one of these example programs whose type looks like a logical formula is a%\index{proof term}% _proof term_.  We use that name for any Gallina term of a logical type, and we will elaborate shortly on what makes a type logical.
*)
%\smallskip{}%型が論理式のように見えるこれらのプログラム例は，どれも%\index{しょうめいこう@証明項}% %\emph{証明項}%です．
この術語を論理型の任意のGallina項を表すのに使っています．
型論理を構成するものについては，後で詳細に解説します．

本章の残りの部分では，型を定義する方法をいくつか導入します．
例に挙げる型はそれぞれ別にプログラムあるいは証明の型として解釈できます．

(*
One of the first types we introduce will be [bool], with constructors [true] and [false].  Newcomers to Coq often wonder about the distinction between [True] and [true] and the distinction between [False] and [false].  One glib answer is that [True] and [False] are types, but [true] and [false] are not.  A more useful answer is that Coq's metatheory guarantees that any term of type [bool] _evaluates_ to either [true] or [false].  This means that we have an _algorithm_ for answering any question phrased as an expression of type [bool].  Conversely, most propositions do not evaluate to [True] or [False]; the language of inductively defined propositions is much richer than that.  We ought to be glad that we have no algorithm for deciding our formalized version of mathematical truth, since otherwise it would be clear that we could not formalize undecidable properties, like almost any interesting property of general-purpose programs.
*)
最初に導入する型は[bool]で，構成子[true]および[false]があります．
Coqに初めて触れると[True]と[true]あるいは[False]と[false]の違いに戸惑うことがよくあります．
表面的にいうなら，[True]と[False]は型であり，[true]と[false]は型ではないということです．
もう少しましな答としては，Coqのメタ定理が[bool]型の任意の項は%\emph{評価する}%と[true]か[false]のどちらかになることを保証している，ということになります．
その意味は，型が[bool]である式で表されたどのような問題に対しても，それに答える%\emph{アルゴリズム}%があるということです．
逆にほとんどの命題は評価しても[True]あるいは[False]になることはないということです．
帰納的に定義された命題の言語は，これよりもはるかに豊かな表現力があります．(* 意味がよくわからない -nobsun *)
形式化された数学的真理を決定するアルゴリズムがないことは喜ぶべきことです．
もし，そのようなアルゴリズムがあるとすれば，汎用プログラムの興味深い性質がそうであるような，決定不能な性質を形式化できないということになるからです．
*)


(** 
(* * Enumerations *)
* 列挙
*)

(**
(* Coq inductive types generalize the %\index{algebraic datatypes}%algebraic datatypes found in %\index{Haskell}%Haskell and %\index{ML}%ML.  Confusingly enough, inductive types also generalize %\index{generalized algebraic datatypes}%generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic-datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.
*)
Coqの帰納型は，%\index{Haskell}%Haskellや%\index{ML}%MLにある%\index{だいすうデータがた@代数データ型}%代数データ型を一般化したものです．
さらにややこしいことに，帰納型は，型依存性を追加することでGADT（一般化代数データ型）の一般化にもなっています．
それでも，前章の例をひとまずおいて，帰納データ型を使う基本的な代数的データを見る価値はあります．
こうした型の値に関するなにがしかを証明する機会によって，HaskellやMLでの実践以上の知恵が得られます．

(*
The singleton type [unit] is an inductive type:%\index{Gallina terms!unit}\index{Gallina terms!tt}%
*)
シングルトン型[unit]は帰納型です%\index{Gallinaこう@Gallina項!unit}\index{Gallinaこう@Gallina項!tt}%．
*)

Inductive unit : Set :=
  | tt.

(**
(* 
This vernacular command defines a new inductive type [unit] whose only value is [tt].
We can verify the types of the two identifiers we introduce: 
*)
このCoqのコマンドは，[tt]がその唯一の値であるような新しい帰納型[unit]を定義しています．
ここで導入した2つの識別子の型を検証できます．
*)

Check unit.
(** [unit : Set] *)

Check tt.
(** [tt : unit] *)

(**
(*
%\smallskip{}%We can prove that [unit] is a genuine singleton type. 
*)
%\smallskip{}%[unit]が確かにシングルトン（値を一つしか持たない）型であることを証明できます．
*)

Theorem unit_singleton : forall x : unit, x = tt.

(**
(*
The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x].%\index{tactics!induction}%
*)
帰納型に関して重要なことは，なにも驚くようなことではなく，その値上で帰納法を用いられるということです．
そして，帰納法はこの定理を証明するためのまさに鍵になっています．
*)

(* begin thide *)
  induction x.

(**
(*
The goal changes to:
*)
ゴールを以下のように変更します．
[[
 tt = tt
]]
*)

  (**
  (* 
  %\noindent{}%...which we can discharge trivially.
  *)
  %\noindent{}%...これは自明．(* うまい訳を思いつかない-nobsun *)
  *)

  reflexivity.
Qed.
(* end thide *)

(**
(*
It seems kind of odd to write a proof by induction with no inductive hypotheses.  We could have arrived at the same result by beginning the proof with:%\index{tactics!destruct}% [[
  destruct x.
]]
*)
帰納法の仮定がない帰納法による証明を書くというのは奇妙なものに思えます．
%\index{tactics!destruct}% [[
  destruct x.
]]
というタクティクスを使った証明から始めると同じ結果になるでしょう．

(*
%\noindent%...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.
*)
%\noindent%「...これは」というのは古典数学での「すべての場合を尽しての証明」に対応します．
非再帰的帰納型では，この2つのタクティクスは同じ振舞です．
すべての場合を尽すというやりかたは，再帰型に関する証明においても使えることが多いものです．
また，不要な帰納法の仮定をせずに済むという点で優れています．

(*
What exactly _is_ the %\index{induction principles}%induction principle for [unit]?  We can ask Coq:
*)
では，[unit]に対する%\index{induction principles}%帰納法原理とは%\emph{何}%でしょうか．
*)

Check unit_ind.
(** [unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u] *)

(**
(* 
%\smallskip{}%Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Recall from the last section that our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type %\index{Gallina terms!Prop}%[Prop], which appears in our induction principle; and the type %\index{Gallina terms!Set}%[Set], which we have seen a few times already.
*)
%\smallskip{}%ある型[T]を定義する[Inductive]コマンドはどれも[T_ind]という帰納法原理を定義します．
前節で，型，それに対する操作，論証のための帰納法原理はどれも同じ言語に存在し，同じ型システムで表現されています．
プログラムとは何か，証明とは何かをいい当てるための鍵は，帰納法原理で見た%\index{Gallinaこう@Gallina項!Prop}%[Prop]型と，何度か見ている%\index{Gallinaこう@Gallina項!Set}%[Set]型とをはっきり区別することにあります．

(*
The convention goes like this: [Set] is the type of normal types used in programming, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.
*)
慣習としての規約では，[Set]はプログラミングで使われている通常の型を表す型で，その値はプログラムです．
[Prop]は論理命題を表す型で，その値はその型の証明です．
したがって，帰納法原理の型は，証明を構成するための関数を示す型になります．

(*
Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].
*)
特に[unit_ind]は，[unit]値の上の述語[P]を限量化します．
述語[P]が[tt]であることの証明を示せれば，[P]が[unit]型の任意の値[u]について成り立つことを証明したことになります．

(*
The definition of [unit] places the type in [Set].  By replacing [Set] with [Prop], [unit] with [True], and [tt] with [I], we arrive at precisely the definition of [True] that the Coq standard library employs!  The program type [unit] is the Curry-Howard equivalent of the proposition [True].  We might make the tongue-in-cheek claim that, while philosophers have expended much ink on the nature of truth, we have now determined that truth is the [unit] type of functional programming.
*)
[unit]は[Set]の要素である型と定義されています．
[Set]を[Prop]と，[unit]を[True]と，[tt]を[I]と取り替えると，Coqの標準ライブラリが採用している[True]の定義とぴったり一致します．

%\medskip%

(*
We can define an inductive type even simpler than [unit]:%\index{Gallina terms!Empty\_set}%
*)
[unit]:%\index{Gallinaこう@Gallina項!Empty\_set}%よりも単純な帰納型も定義できます．
*)

Inductive Empty_set : Set := .

(**
(* [Empty_set] has no elements.  We can prove fun theorems about it:
*)
[Empty_set]は要素を持ちません．
これに関して面白い定理を証明してみましょう．
*)

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
(* begin thide *)
  destruct 1.
Qed.
(* end thide *)

(**
(*
Because [Empty_set] has no elements, the fact of having an element of this type implies anything.  We use [destruct 1] instead of [destruct x] in the proof because unused quantified variables are relegated to being referred to by number.  (There is a good reason for this, related to the unity of quantifiers and implication.  At least within Coq's logical foundation of %\index{constructive logic}%constructive logic, which we elaborate on more in the next chapter, an implication is just a quantification over a proof, where the quantified variable is never used.  It generally makes more sense to refer to implication hypotheses by number than by name, and Coq treats our quantifier over an unused variable as an implication in determining the proper behavior.)
*)
[Empty_set]は要素を持ちませんので，この型の要素が一つあるという事実はすべてを含意します．
証明の中で[destruct x]ではなく[destruct 1]を使っているのは，使用しない被限量化変数は格下げされて，数字で参照するようになるからです．
（このようになっているには，限量化子と含意を統一した扱いにすることに関連する，正当な理由があります．
少くとも，Coqの%\index{こうせいてきろんり@構成的論理}%構成的論理の論理的基盤（次章で詳しく説明する）においては，含意は被限量化変数を使わない証明を限量化しているにすぎないのです．
含意の仮定を変数名で参照するより数字で参照するほうが理にかなっており，Coqは適切な振舞を決定するにあたって，使用しない変数に対する限量化子を含意として扱います．）

(*
We can see the induction principle that made this proof so easy:
*)
この証明を生みだす帰納法原理は簡単です．
*)

Check Empty_set_ind.
(** [Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e] *)

(**
(* %\smallskip{}%In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].
*)
%\smallskip{}%いいかえれば，空集合に属する値上の任意の述語は，そのような要素について何も表明していないということです．(* 良いいいまわしを思いつかない-nobsun *)
直前の証明では，述語として[(fun _ : Empty_set => 2 + 2 = 5)]を選んでいます．

(*
We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: 
*)
この魔法の切り札をプログラミングの場面に応用することもできます．
以下は[Empty_set]の値を[unit]の値に変換する横着な方法です．
*)

Definition e2u (e : Empty_set) : unit := match e with end.

(**
(* We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.  It turns out that [Empty_set] is the Curry-Howard equivalent of [False].  As for why [Empty_set] starts with a capital letter and not a lowercase letter like [unit] does, we must refer the reader to the authors of the Coq standard library, to which we try to be faithful.
*)
前章で，パターン照合に[match]を採用しています．
構成子を持たない型の値の照合なので，選択肢は必要ありません．
[Empty_set]はCurry-Howard対応により[False]と同等であることが判ります．
[Empty_set]が[unit]と違って大文字から始まる理由は，本書ではCoq標準ライブラリの作成者のやり方に忠実に従っていて，読者にそれに従ってもらうためである．(* ちょっと訳に自信なし-nobsun *)

%\medskip%

(*
Moving up the ladder of complexity, we can define the Booleans:%\index{Gallina terms!bool}\index{Gallina terms!true}\index{Gallina terms!false}%
*)
より複雑なものへ移行すると論理値を定義できます．%\index{Gallinaこう@Gallina項!bool}\index{Gallinaこう@Gallina項!true}\index{Gallinaこう@Gallina項!false}%
*)

Inductive bool : Set :=
| true
| false.

(**
(* 
We can use less vacuous pattern matching to define Boolean negation.%\index{Gallina terms!negb}% 
*)
空ではないパターン照合を使って論理否定を定義できます．%\index{Gallinaこう@Gallina項!negb}%
*)

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(**
(*
An alternative definition desugars to the above, thanks to an %\index{Gallina terms!if}%[if] notation overloaded to work with any inductive type that has exactly two constructors: 
*)
上の定義を構文糖衣を使わず行うこともできます．
それには%\index{Gallinaこう@Gallina項!if}%[if]記法を使い，ちょうど2つの構成子をもつ任意の帰納型上で機能するようにします．
*)

Definition negb' (b : bool) : bool :=
  if b then false else true.

(**
(*
We might want to prove that [negb] is its own inverse operation.
*)
[negb]がそれ自身の逆演算になることを証明したいとしましょう．
*)

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
(* begin thide *)
  destruct b.

  (**
  (*
  After we case-analyze on [b], we are left with one subgoal for each constructor of [bool].
  *)
  [b]上のすべての場合を調べてしまえば，[bool]のそれぞれの構成子に対するサブゴールがが1つずつ残ります．
[[
  2 subgoals

  ============================
   negb (negb true) = true

subgoal 2 is

 negb (negb false) = false
]]
(*
The first subgoal follows by Coq's rules of computation, so we can dispatch it easily: 
*)
最初のサブゴールはCoqのコンピュテーション規則に従いますので，ディスパッチするのは簡単です．
*)

  reflexivity.

(**
(* 
Likewise for the second subgoal, so we can restart the proof and give a very compact justification.%\index{Vernacular commands}%
*)
2つめのサブゴールについても同様です．
証明を再開すればきわめてコンパクトに正当化できます．%\index{Vernacularこまんど@Vernacularコマンド!Restart}%
*)

Restart.

  destruct b; reflexivity.
Qed.
(* end thide *)

(**
(*
Another theorem about Booleans illustrates another useful tactic.%\index{tactics!discriminate}%
*)
論理値に関する別の定理を使ってもう1つ便利なタクティックを説明しましょう．%\index{たくてぃくす@タクティクス!discriminate}%
*)

Theorem negb_ineq : forall b : bool, negb b <> b.
(* begin thide *)
  destruct b; discriminate.
Qed.
(* end thide *)

(**
(*
The [discriminate] tactic is used to prove that two values of an inductive type are not equal, whenever the values are formed with different constructors.  In this case, the different constructors are [true] and [false].
*)
[discriminate]タクティックを使うと，ある帰納型の2つの値がそれぞれ別の構成子で形成されるなら等しくないことを証明できます．

(*
At this point, it is probably not hard to guess what the underlying induction principle for [bool] is.
*)
ここまでくれば，[bool]の対する帰納法原理がどのようなものであるか推測するのは難しくありません．
*)

Check bool_ind.
(** [bool_ind : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b] *)

(**
(*
%\smallskip{}%That is, to prove that a property describes all [bool]s, prove that it describes both [true] and [false].
*)
%\smallskip{}%すなわち，すべての[bool]値についてある性質が成り立つことを証明するには，その性質が[true]と[false]の両方で成り立つことを証明すればよいということです．

(*
There is no interesting Curry-Howard analogue of [bool].  Of course, we can define such a type by replacing [Set] by [Prop] above, but the proposition we arrive at is not very useful.  It is logically equivalent to [True], but it provides two indistinguishable primitive proofs, [true] and [false].   In the rest of the chapter, we will skip commenting on Curry-Howard versions of inductive definitions where such versions are not interesting.
*)
[bool]に関するCurr-Howard対応の類推には興味深いことはなにもありません．
もちろん，上述の[Set]を[Prop]に置き換えて[bool]のような型を定義できますが，それで得られた命題はあまり使いではありません．
これは論理的には[True]に相当しますが，区別不可能な2つのプリミティブな証明，すなわち，[true]と[false]を提供することになります．(* ここは意味がよくわからない-nobsun *)
本章の残りの部分では，このような興味を持てない機能的定義のCurry-Howard対応版に対するコメントしません．
*)


(**
(*
* Simple Recursive Types
*)
* 単純再帰型
*)

(**
(* 
The natural numbers are the simplest common example of an inductive type that actually deserves the name.%\index{Gallina terms!nat}\index{Gallina terms!O}\index{Gallina terms!S}%
*)
自然数はその名に値する帰納型の最も単純でだれもが知る例です．%\index{Gallinaこう@Gallina項!nat}\index{Gallinaこう@Gallina項!O}\index{Gallinaこう@Gallina項!S}%
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(**
(*
The constructor [O] is zero, and [S] is the successor function, so that [0] is syntactic sugar for [O], [1] for [S O], [2] for [S (S O)], and so on.
*)
構成子[O]は零のことであり，[S]は後者関数です．したがって，[0]は[O]の構文糖衣であり，[1]は[S O]の，[2]は[S (S O)]のそれぞれ構文糖衣です．

(*
Pattern matching works as we demonstrated in the last chapter:%\index{Gallina terms!pred}%
*)
前章で示したようにパターン照合が上手く効きます．
*)

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** 
(*
We can prove theorems by case analysis with [destruct] as for simpler inductive types, but we can also now get into genuine inductive theorems.  First, we will need a recursive function, to make things interesting.%\index{Gallina terms!plus}%
*)
もっと単純な帰納型であれば[destruct]を使って場合を尽せば定理を証明することも可能ですが，本物の帰納的定理を探索することも可能です．
話を面白くするのにまず必要なのは再帰関数です．
*)

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(**
(*
Recall that [Fixpoint] is Coq's mechanism for recursive function definitions.  Some theorems about [plus] can be proved without induction.
*)
[Fixpoint]はCoqで再帰関数を定義するための機構であることを思い出してください．
[plus]に関する定理で帰納法を使わずに証明できるものがあります．
*)

Theorem O_plus_n : forall n : nat, plus O n = n.
(* begin thide *)
  intro; reflexivity.
Qed.
(* end thide *)

(**
(*
Coq's computation rules automatically simplify the application of [plus], because unfolding the definition of [plus] gives us a [match] expression where the branch to be taken is obvious from syntax alone.  If we just reverse the order of the arguments, though, this no longer works, and we need induction.
*)
Coqのコンピュテーション規則は自動的に[plus]の適用を単純化します．
[plus]の定義を展開すると，構文だけ見れば採用されることが明らかな選択肢しかない[match]式になるからです．
引数の順序を逆にするだけで，もう動かなくなり，帰納法が必要になります．
*)

Theorem n_plus_O : forall n : nat, plus n O = n.
(* begin thide *)
  induction n.

(**
(*
Our first subgoal is [plus O O = O], which _is_ trivial by computation.
*)
最初のサブゴールは[plus O O = O]で，これはコンピュテーションにより%\emph{自明}%です．
*)

  reflexivity.

(**
(*
Our second subgoal requires more work and also demonstrates our first inductive hypothesis.
*)
2つめのサブゴールについてはもっと手をかけなければなりません．
最初の帰納法の仮定を示します．

[[
  n : nat
  IHn : plus n O = n
  ============================
   plus (S n) O = S n
 
]]

(*
We can start out by using computation to simplify the goal as far as we can.%\index{tactics!simpl}%
*)
コンピュテーションを使ってこのゴールを単純化するところから始めて行けるところまで行きましょう．%\index{たくてぃくす@タクティクス!simpl}%
*)

  simpl.

(**
(*
Now the conclusion is [S (plus n O) = S n].  Using our inductive hypothesis:
*)
これで，結論は[S (plus n O) = S n]となります．
ここで，帰納法の仮定を使います．
*)

  rewrite IHn.

(**
(*
%\noindent{}%...we get a trivial conclusion [S n = S n].
*)
%\noindent{}%そうすると自明な結論[S n = S n]が得られます．
*)

  reflexivity.

(**
(*
Not much really went on in this proof, so the [crush] tactic from the [CpdtTactics] module can prove this theorem automatically.
*)
この証明はこれ以上進みません．
そこで，[CpdtTactics]モジュールの[crush]タクティックを使うとこの定理は自動的に証明できます．
*)

Restart.

  induction n; crush.
Qed.
(* end thide *)

(**
(*
We can check out the induction principle at work here:
*)
ここで効いている帰納法原理を確認できます．
*)

Check nat_ind.
(** %\vspace{-.15in}% [[
  nat_ind : forall P : nat -> Prop,
            P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  ]]

(*
Each of the two cases of our last proof came from the type of one of the arguments to [nat_ind].  We chose [P] to be [(fun n : nat => plus n O = n)].  The first proof case corresponded to [P O] and the second case to [(forall n : nat, P n -> P (S n))].  The free variable [n] and inductive hypothesis [IHn] came from the argument types given here.
*)
前述の証明における2つの場合それぞれは，[nat_ind]への引数のうちの1つの型に由来します．
[P]を[(fun n : nat => plus n O = n)]としましょう．
1つめの証明は[P O]に対応し，2つめは[(forall n : nat, P n -> P (S n))]に対応します．
自由変数[n]および帰納法の仮定[IHn]はここで与えられた引数の型に由来します．

(*
Since [nat] has a constructor that takes an argument, we may sometimes need to know that that constructor is injective.%\index{tactics!injection}\index{tactics!trivial}%
*)
[nat]は引数を1つとる構成子を持ちますので，この構成子が単射であることを知らなけれならないこともあります．%\index{たくてぃくす@タクティクス!injection}\index{たくてぃくす@タクティクス!trivial}%
*)

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  injection 1; trivial.
Qed.
(* end thide *)

(**
(*
The [injection] tactic refers to a premise by number, adding new equalities between the corresponding arguments of equated terms that are formed with the same constructor.  We end up needing to prove [n = m -> n = m], so it is unsurprising that a tactic named [trivial] is able to finish the proof.  This tactic attempts a variety of single proof steps, drawn from a user-specified database that we will later see how to extend.
*)
[injection]タクティックでは前提を数字で指定します．
新しい同等性(* equalities が複数形なのはなぜ-nobsun *)を同じ構成子で構成された対象項の引数間に追加します．
最後に[n = m -> n = m]を証明しなければならないところに至ります．
したがって，[trivial]という名前のタクティックで，この証明を終了できても不思議ではありません．
この[injection]タクティックは，ユーザ指定のデータベース（これについては後で拡張方法を説明します）から引いてきた様々な単一証明ステップを試します．

(*
There is also a very useful tactic called %\index{tactics!congruence}%[congruence] that can prove this theorem immediately.  The [congruence] tactic generalizes [discriminate] and [injection], and it also adds reasoning about the general properties of equality, such as that a function returns equal results on equal arguments.  That is, [congruence] is a%\index{theory of equality and uninterpreted functions}% _complete decision procedure for the theory of equality and uninterpreted functions_, plus some smarts about inductive types.
*)
この定理を一発で証明できる%\index{たくてぃくす@タクティクス!congruence}%[congruence]というきわめて役に立つタクティックもあります．
[congruence]タクティックは[discriminate]および[injection]を一般化したもので，関数は等しい引数について等しい結果を返すという同等性に関する一般的な性質の論証を追加します．
すなわち，[congruence]は%\index{みかいしゃくかんすうのどうとうせいりろん@未解釈関数の同等性理論}%%\emph{未解釈関数の同等性理論に対する完全決定手続}%であり，帰納型に関してもスマートなタクティックです．
(* the theory of equality and uninterpreted functions は何のことか？-nobsun *)

%\medskip%

(*
We can define a type of lists of natural numbers.
*)
以下のように自然数のリストの型を定義できます．
*)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

(**
(*
Recursive definitions over [nat_list] are straightforward extensions of what we have seen before.
*)
[nat_list]上の再帰的定義は既に説明したものの素直な拡張になっています．
*)

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

(**
(*
Inductive theorem proving can again be automated quite effectively.
*)
帰納的定理の証明はきわめて効率的に自動化可能です．
*)

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2)
  = plus (nlength ls1) (nlength ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

Check nat_list_ind.
(** %\vspace{-.15in}% [[
  nat_list_ind
     : forall P : nat_list -> Prop,
       P NNil ->
       (forall (n : nat) (n0 : nat_list), P n0 -> P (NCons n n0)) ->
       forall n : nat_list, P n
]]

%\medskip%

(*
In general, we can implement any "tree" type as an inductive type.  For example, here are binary trees of naturals.
*)
一般的には，任意の「木(ツリー)」型を帰納型として実装可能です．
たとえば，以下は自然数の二分木です．
*)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

(**
(*
Here are two functions whose intuitive explanations are not so important.  The first one computes the size of a tree, and the second performs some sort of splicing of one tree into the leftmost available leaf node of another. 
*)
以下に2つの関数を示す（その直観的説明はあまり重要ではありません）．
1つめは木のサイズを計算する関数で，2つめは一方の木を他方の木の最も左にある葉に接合します．
*)

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => S O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
    | NLeaf => NNode tr2 O NLeaf
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
(* begin thide *)
  induction n1; crush.
Qed.
(* end thide *)

Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
  = plus (nsize tr2) (nsize tr1).
(* begin thide *)
  induction tr1; crush.
Qed.
(* end thide *)

(**
(*
It is convenient that these proofs go through so easily, but it is still useful to look into the details of what happened, by checking the statement of the tree induction principle.
*)
これらの証明が簡単に行えるというのは便利なことですが，木（ツリー）の帰納法原理のステートメントを確認し，何が起こったのかを詳しく調べることも有効です．
*)

Check nat_btree_ind.
(** %\vspace{-.15in}% [[
  nat_btree_ind
     : forall P : nat_btree -> Prop,
       P NLeaf ->
       (forall n : nat_btree,
        P n -> forall (n0 : nat) (n1 : nat_btree), P n1 -> P (NNode n n0 n1)) ->
       forall n : nat_btree, P n
]]

(*
We have the usual two cases, one for each constructor of [nat_btree].
*)
通常の場合分けは2通りで，それぞれ[nat_btree]の構成子に対応しています．
*)

(**
(*
* Parameterized Types
*)
* パラメタライズド型
(* parameterized type の定訳は？-nobsun *)
*)

(**
(*
We can also define %\index{polymorphism}%polymorphic inductive types, as with algebraic datatypes in Haskell and ML.%\index{Gallina terms!list}\index{Gallina terms!Nil}\index{Gallina terms!Cons}\index{Gallina terms!length}\index{Gallina terms!app}% 
*)
HaskellやMLにおける代数データ型のように%\index{たそうせい@多相性}%多相帰納型を定義できます．
%\index{Gallinaこう@Gallina項!list}\index{Gallinaこう@Gallina項!Nil}\index{Gallinaこう@Gallina項!Cons}\index{Gallinaこう@Gallina項!length}\index{Gallinaこう@Gallina項!app}% 
*)

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app : forall T (ls1 ls2 : list T), length (app ls1 ls2)
  = plus (length ls1) (length ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

(**
(*
There is a useful shorthand for writing many definitions that share the same parameter, based on Coq's%\index{sections}\index{Vernacular commands!Section}\index{Vernacular commands!Variable}% _section_ mechanism.  The following block of code is equivalent to the above:
*)
同じパラメータを共有する多くの定義を書くための便利な省略形があります．
これらはCoqの%\index{せくしょん@セクション}\index{Vernacularこんまんど@Vernacularコマンド!Section}\index{Vernacularこまんど@Vernacularコマンド!Variable}\emph{セクション}%機構に基づくものです．
*)

(* begin hide *)
Reset list.
(* end hide *)

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2)
    = plus (length ls1) (length ls2).
(* begin thide *)
    induction ls1; crush.
  Qed.
(* end thide *)
End list.

Implicit Arguments Nil [T].

(**
(*
After we end the section, the [Variable]s we used are added as extra function parameters for each defined identifier, as needed.  With an [Implicit Arguments]%~\index{Vernacular commands!Implicit Arguments}% command, we ask that [T] be inferred when we use [Nil]; Coq's heuristics already decided to apply a similar policy to [Cons], because of the [Set Implicit Arguments]%~\index{Vernacular commands!Set Implicit Arguments}% command elided at the beginning of this chapter.  We verify that our definitions have been saved properly using the [Print] command, a cousin of [Check] which shows the definition of a symbol, rather than just its type.
*)
このセクションを終端すると，使用した[Variable]は定義された各識別子に対し，必要に応じて，追加の関数パラメータとして付加されます．
[Implicit Arguments]%~\index{Vernacularこまんど@Vernacularコマンド!Implicit Arguments}%コマンドを使うと，[Nil]を使用したときに[T]が推論されるようにできます．
Coqのヒューリスティックは，似た方針を[Cons]に適用することを決定ずみです．
それは，この章の冒頭で[Set Implicit Aruguments]%~\index{Vernacularこまんど@Vernacularコマンド!Set Implicit Arguments}%コマンドを省略したからです．
[Print]コマンドを使って，定義が適切に保存されたかどうかを確認します．
[Check]コマンドはシンボルの型だけではなく定義も表示します．
*)

Print list.
(** %\vspace{-.15in}% [[
  Inductive list (T : Set) : Set :=
    Nil : list T | Cons : T -> list T -> list T
]]

(*
The final definition is the same as what we wrote manually before.  The other elements of the section are altered similarly, turning out exactly as they were before, though we managed to write their definitions more succinctly.
*)
最終的な定義は以前に手書きしたものと同じです．
セクションの他の要素も同様に変更されています．
しかし，定義をより簡潔に記述したにもかかわらず，以前のものとぴったり同じになっています．
*)

Check length.
(** %\vspace{-.15in}% [[
  length
     : forall T : Set, list T -> nat
]]

(*
The parameter [T] is treated as a new argument to the induction principle, too.
*)
パラメータ[T]は帰納法原理の新しい引数としても扱われます．
*)

Check list_ind.
(** %\vspace{-.15in}% [[
  list_ind
     : forall (T : Set) (P : list T -> Prop),
       P (Nil T) ->
       (forall (t : T) (l : list T), P l -> P (Cons t l)) ->
       forall l : list T, P l
]]

(*
Thus, despite a very real sense in which the type [T] is an argument to the constructor [Cons], the inductive case in the type of [list_ind] (i.e., the third line of the type) includes no quantifier for [T], even though all of the other arguments are quantified explicitly.  Parameters in other inductive definitions are treated similarly in stating induction principles.
*)
このように，型[T]が構成子[Cons]への引数になっているというきわめて現実的な意味があるにもかかわらず，さらに他の引数はどれも明示的に限量化修飾されているにもかかわらず，[list_ind]の型の場合分けにおける帰納部（たとえば上の3行目）には，[T]への限量子がありません．
他の帰納的定義におけるパラメータは帰納法原理で表明されているとおりの扱いを受けます．
*)


(**
(*
* Mutually Inductive Types
*)
* 相互帰納型
*)

(**
(*
We can define inductive types that refer to each other:
*)
相互参照する帰納型を以下のように定義できます．
*)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

(**
(*
Everything is going roughly the same as in past examples, until we try to prove a theorem similar to those that came before.
*)
すでに見たのと同じような定理を証明しようとしない限りは，どの型も見たことのある例とだいたい同じように見えます．
*)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
(* begin thide *)
  induction el1; crush.

  (** One goal remains: [[

  n : nat
  o : odd_list
  el2 : even_list
  ============================
   S (olength (oapp o el2)) = S (plus (olength o) (elength el2))
   ]]

  (*
  We have no induction hypothesis, so we cannot prove this goal without starting another induction, which would reach a similar point, sending us into a futile infinite chain of inductions.  The problem is that Coq's generation of [T_ind] principles is incomplete.  We only get non-mutual induction principles generated by default.
  *)
  帰納法の仮定がありませんので，別の帰納法から始めないとこのゴールを証明できません．
  そのようにするとまた同じところに到達することになり，無駄な帰納法の無限連鎖を辿ることになってしまいます．
  この問題はCoqが[T_ind]の帰納原理を不完全にしか生成しないことに起因します．
  デフォルトでは非相互帰納的な原理のみしか生成されません．
  *)

Abort.
Check even_list_ind.
(** %\vspace{-.15in}% [[
  even_list_ind
     : forall P : even_list -> Prop,
       P ENil ->
       (forall (n : nat) (o : odd_list), P (ECons n o)) ->
       forall e : even_list, P e
]]

(*
We see that no inductive hypotheses are included anywhere in the type.  To get them, we must ask for mutual principles as we need them, using the %\index{Vernacular commands!Scheme}%[Scheme] command.
*)
この型には帰納法の仮定がどこにも含まれていません．
これらを得るには%\index{Vernacularこまんど@Vernacularコマンド!Scheme}%[Scheme]コマンドを使って，必要な相互帰納法の原理を求めなければなりません．
*)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

(**
(*
This invocation of [Scheme] asks for the creation of induction principles [even_list_mut] for the type [even_list] and [odd_list_mut] for the type [odd_list].  The [Induction] keyword says we want standard induction schemes, since [Scheme] supports more exotic choices.  Finally, [Sort Prop] establishes that we really want induction schemes, not recursion schemes, which are the same according to Curry-Howard, save for the [Prop]/[Set] distinction.
*)
このように[Scheme]を呼び出して，型[even_list]の帰納法原理[even_list_mut]および型[odd_list]の帰納法原理[odd_list_mut]を作るように指示します．
[Scheme]キーワードはより奇妙な選択肢までサポートしているので，[Induction]キーワードを使って，標準の帰納法スキームが必要なことを示しています．
最後の[Srot Prop]は，[Prop]と[Set]との違いを除けば，必要なものは帰納法スキームであって，Curry-Howard対応に関する再帰スキームではないことを確認するためのコマンドです．
*)

Check even_list_mut.
(** %\vspace{-.15in}% [[
  even_list_mut
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
]]

(*
This is the principle we wanted in the first place.
*)
これが最初に必要であった帰納法原理です．

(*
The [Scheme] command is for asking Coq to generate particular induction schemes that are mutual among a set of inductive types (possibly only one such type, in which case we get a normal induction principle).  In a sense, it generalizes the induction scheme generation that goes on automatically for each inductive definition.  Future Coq versions might make that automatic generation smarter, so that [Scheme] is needed in fewer places.  In a few sections, we will see how induction principles are derived theorems in Coq, so that there is not actually any need to build in _any_ automatic scheme generation.
*)
[Scheme]コマンドはCoqに帰納型の集合において，相互に関連する帰納法原理を具体的に生成するためものです（通常の帰納法原理として得られるときには，そのような型は1つだけです）．
ある意味これは，帰納法スキーム生成の一般化で，それぞれの帰納的定義に対して自動的に行われます．
将来のCoqのバージョンでは，この自動生成がもっとスマートになるかもしれませんので，[Scheme]コマンドが必要な場所は限られてくるでしょう．
この後のいくつかのセクションを通じて，Coqでは帰納法原理がどのようにして定理として導出されるかを説明します．
そこで，%\emph{任意の}%自動スキーム生成において構築すべきものはなにもないことが判ります．

(*
There is one more wrinkle left in using the [even_list_mut] induction principle: the [induction] tactic will not apply it for us automatically.  It will be helpful to look at how to prove one of our past examples without using [induction], so that we can then generalize the technique to mutual inductive types.%\index{tactics!apply}% 
*)
帰納法原理[even_list_mut]を使うにあたって残念なことがもう1つあります．
[induction]タクティックが自動的に適用されないことです．
以前に見た例のうちで，[induction]を使わずに証明しているものがあるので，そのやりかたを相互帰納型に一般化すればよいでしょう．%\index{たくてぃくす@タクティクス!apply}%
*)

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply nat_ind.
  (**
  (*
  Here we use [apply], which is one of the most essential basic tactics.  When we are trying to prove fact [P], and when [thm] is a theorem whose conclusion can be made to match [P] by proper choice of quantified variable values, the invocation [apply thm] will replace the current goal with one new goal for each premise of [thm].
  *)
  ここで使っている[apply]は基本タクティクスのうちでも最も重要なものです．
  [P]を証明しようとするときや，[thm]が定理であって被量子化変数の値を適切に選択することでその結論を[P]に照合できるときには[apply thm]を起動すれば，現在のゴールを[thm]のそれぞれの仮定に対する新たなゴールに置き換えられます．

  (*
  This use of [apply] may seem a bit _too_ magical.  To better see what is going on, we use a variant where we partially apply the theorem [nat_ind] to give an explicit value for the predicate that gives our induction hypothesis.
  *)
  このような[apply]の使い方は，魔法じみていると感じるかもしれません．
  なにが起っているのかをもうすこしよく理解するために，定理[nat_ind]を部分適用する方法を使ってみましょう．
  それには，帰納法の仮定を与える述語に明示的に値を渡します．
  *)

  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

(**
(*
From this example, we can see that [induction] is not magic.  It only does some bookkeeping for us to make it easy to apply a theorem, which we can do directly with the [apply] tactic.
*)
この例を見れば，[induction]は少しも魔法ではないことが判ります．
やっていることといえば，ある種の記録付けだけです．
これのおかげで，定理の適用が簡単になり，[apply]タクティックを直接使えるようになります．

(*
This technique generalizes to our mutual example:
この技法を一般化して相互帰納の例に使いましょう．
*)

*)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).

  apply (even_list_mut
    (fun el1 : even_list => forall el2 : even_list,
      elength (eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol : odd_list => forall el : even_list,
      olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.
(* end thide *)

(**
(*
We simply need to specify two predicates, one for each of the mutually inductive types.  In general, it is not a good idea to assume that a proof assistant can infer extra predicates, so this way of applying mutual induction is about as straightforward as we may hope for.
*)
相互帰納型のそれぞれに対応する2つの述語を指定するだけですみます．
一般に，証明補助機構が追加の述語を推論できると仮定するのは良いとはいえないことを考えると，
相互帰納を適用するこの方法は望みどおりすっきりした方法です．
*)


(**
(*
* Reflexive Types
*)
* 反映型
*)

(**
(*
A kind of inductive type called a _reflexive type_ includes at least one constructor that takes as an argument _a function returning the same type we are defining_.  One very useful class of examples is in modeling variable binders.  Our example will be an encoding of the syntax of first-order logic.  Since the idea of syntactic encodings of logic may require a bit of acclimation, let us first consider a simpler formula type for a subset of propositional logic.  We are not yet using a reflexive type, but later we will extend the example reflexively.
*)
帰納型のある種のものを%\emph{反映型}%と呼びます．
反映型は%\emph{定義しようとしている型と同じ型を返す関数}%を引数とする構成子を少くとも1つもつ型のことです．
きわめて有用な例としては，変数束縛のモデリングがあります．
以下の例は一階論理の構文を符号化しようとするものです．
論理の構文を符号化するというアイデアにはすこし慣れが必要なので，まず，命題論理のサブセットに対するより単純な論理式型を考えましょう．
ここではまだ反映型を使っていませんが，後でこれを反映型に拡張します．
*)

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula.

(* begin hide *)
(* begin thide *)
Definition prod' := prod.
(* end thide *)
(* end hide *)

(**
(*
A key distinction here is between, for instance, the _syntax_ [Truth] and its _semantics_ [True].  We can make the semantics explicit with a recursive function.  This function uses the infix operator %\index{Gallina operators!/\textbackslash}%[/\], which desugars to instances of the type family %\index{Gallina terms!and}%[and] from the standard library.  The family [and] implements conjunction, the [Prop] Curry-Howard analogue of the usual pair type from functional programming (which is the type family %\index{Gallina terms!prod}%[prod] in Coq's standard library).
*)
ここで鍵となるのは，たとえば，%\emph{構文}%[Truth]とその%\emph{意味}%[True]との区別です．
再帰関数を使って意味を明示できます．
この関数は中置演算子%\index{Gallinaえんざんし@Gallina演算子!/\textbackslash}%[/\]を使っています．
この演算子は標準ライブラリにある型族のインスタンス%\index{Gallinaこう@Gallina項!and}%[and]に展開されます．
型族[and]は連言の実装で，ここの[Prop]はCurry-Howard対応の類推から関数プログラミングでは通常ペア型（Coqの標準ライブラリにある型族%\index{Gallinaこう@Gallina項!prod}%[prod]）にあたるものです．
*)

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

(**
(*
This is just a warm-up that does not use reflexive types, the new feature we mean to introduce.  When we set our sights on first-order logic instead, it becomes very handy to give constructors recursive arguments that are functions.
*)
これは，まだ反映型を使っていないウォーミングアップです．
一階論理に同様のアイデアを持ち込むと，構成子に関数である再帰的な引数を与えるのに便利です．
*)

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

(**
(*
Our kinds of formulas are equalities between naturals, conjunction, and universal quantification over natural numbers.  We avoid needing to include a notion of "variables" in our type, by using Coq functions to encode the syntax of quantification.  For instance, here is the encoding of [forall x : nat, x = x]:%\index{Vernacular commands!Example}%
*)
ここでの論理式は自然数間の同等性，連言，自然数上での全称限量化です．(* equalityの訳語に迷う-nobsun *)
ここでは「変数」の概念が必要にならないようにしています．
Coqの関数を使って限量化の構文を符号化すると「変数」が必要になります．
たとえば，以下は[forall x : nat, x = x]の符号化です．%\index{Vernacularこまんど@Vernacularコマンド!Example}%
*)

Example forall_refl : formula := Forall (fun x => Eq x x).

(**
(*
We can write recursive functions over reflexive types quite naturally.  Here is one translating our formulas into native Coq propositions.
*)
反映型上の再帰関数はごく自然に書けます．
以下はいままでの論理式をCoqの命題に翻訳するものです．
*)

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

(** We can also encode a trivial formula transformation that swaps the order of equality and conjunction operands. *)

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

(**
(*
It is helpful to prove that this transformation does not make true formulas false.
*)
これは，この変換によって真が偽になることはないことの証明に使えます．
*)


Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
(* begin thide *)
  induction f; crush.
Qed.
(* end thide *)

(**
(*
We can take a look at the induction principle behind this proof.
*)
この証明の背後にある帰納法原理を見られます．
*)

Check formula_ind.
(** %\vspace{-.15in}% [[
  formula_ind
     : forall P : formula -> Prop,
       (forall n n0 : nat, P (Eq n n0)) ->
       (forall f0 : formula,
        P f0 -> forall f1 : formula, P f1 -> P (And f0 f1)) ->
       (forall f1 : nat -> formula,
        (forall n : nat, P (f1 n)) -> P (Forall f1)) ->
       forall f2 : formula, P f2
]]

(*
Focusing on the [Forall] case, which comes third, we see that we are allowed to assume that the theorem holds _for any application of the argument function [f1]_.  That is, Coq induction principles do not follow a simple rule that the textual representations of induction variables must get shorter in appeals to induction hypotheses.  Luckily for us, the people behind the metatheory of Coq have verified that this flexibility does not introduce unsoundness.
*)
[Forall]の場合で3つめにあるものに注目すると，この定理が%\emph{引数である関数[f1]の任意の適用}%で成り立つと考えてよりことがわかります．
つまり，Coqの帰納法原理は帰納変数のテキスト上の表現が帰納法の仮定によって必ず短くなるという単純な法則に従っているわけではないということです．
幸い，Coqのこのメタ定理を準備した人たちが，このような柔軟性があっても系が不健全にならないという検証をしてくれています．

%\medskip%

(*
Up to this point, we have seen how to encode in Coq more and more of what is possible with algebraic datatypes in %\index{Haskell}%Haskell and %\index{ML}%ML.  This may have given the inaccurate impression that inductive types are a strict extension of algebraic datatypes.  In fact, Coq must rule out some types allowed by Haskell and ML, for reasons of soundness.  Reflexive types provide our first good example of such a case; only some of them are legal.
*)
ここまでは，%\index{Haskell}%Haskellや%\index{ML}%MLの代数データ型できることを次々にCoqで符号化する方法を見ました．
このことが帰納型が代数データ型の拡張であるという不正確な印象を与えるかもしれません．
実際，Coqでは，HaskellやMLの代数データ型では許されているある種の型を排除する必要があります．
これは健全性を維持するためです．
反映型はその最初の良い例で，そのうちいくつかだけが許されています．

(*
Given our last example of an inductive type, many readers are probably eager to try encoding the syntax of %\index{lambda calculus}%lambda calculus.  Indeed, the function-based representation technique that we just used, called%\index{higher-order abstract syntax}\index{HOAS|see{higher-order abstract syntax}}% _higher-order abstract syntax_ (HOAS)%~\cite{HOAS}%, is the representation of choice for lambda calculi in %\index{Twelf}%Twelf and in many applications implemented in Haskell and ML.  Let us try to import that choice to Coq:
*)
さきほどの帰納型の例を考えれば，%\index{らむだけいさん@λ計算}%λ計算の構文をエンコードしようとする読者も多いかと思います．
実際には，いま使ったばかりの関数を基本として表現の技法は%\index{こうかいちゅうしょうこうぶん@高階抽象構文}\index{HOAS|see{高階抽象構文}}%%\emph{高階抽象構文}%（HOAS）%~\cite{HOAS}%と呼ばれるもので，%\index{Twelf}%Twelfをはじめとする多くのHaskellやMLで実装されたアプリケーションで，λ計算の表現として用いられます．
この技法をCoqでも使ってみましょう．
*)

(* begin hide *)
(* begin thide *)
Inductive term : Set := App | Abs.
Reset term.
Definition uhoh := O.
(* end thide *)
(* end hide *)
(** [[
Inductive term : Set :=
| App : term -> term -> term
| Abs : (term -> term) -> term.
]]

<<
Error: Non strictly positive occurrence of "term" in "(term -> term) -> term"
>>

(*
We have run afoul of the%\index{strict positivity requirement}\index{positivity requirement}% _strict positivity requirement_ for inductive definitions, which says that the type being defined may not occur to the left of an arrow in the type of a constructor argument.  It is important that the type of a constructor is viewed in terms of a series of arguments and a result, since obviously we need recursive occurrences to the lefts of the outermost arrows if we are to have recursive occurrences at all.  Our candidate definition above violates the positivity requirement because it involves an argument of type [term -> term], where the type [term] that we are defining appears to the left of an arrow.  The candidate type of [App] is fine, however, since every occurrence of [term] is either a constructor argument or the final result type.
*)
これは帰納的定義に対する%\index{げんみつようせいようけん@厳密陽性要件}\index{ようせいようけん@陽性要件}%%\emph{厳密陽性要件}%を犯しているからです．
とにかく再帰的な出現があれば，一番外側の矢印の左側に再帰的な出現が必要なことは明らかですから，厳密陽性要件では構成子の引数の型の矢印の左側に定義しようとしている型が現れてはいけないことになっています．
いまの[Abs]では，矢印の左側にいま定義しようとしている[term]型が現れる[term -> term]型の引数を含みますので，陽性要件に違反します．
[App]の方は問題ありません．
[term]の出現はどれも構成子の引数であるか最終結果の型だからです．

(*
Why must Coq enforce this restriction?  Imagine that our last definition had been accepted, allowing us to write this function:
*)
なぜ，Coqにはこのような制限があるのでしょうか．
さきほどの定義が許容されるとどうなるか想像してみましょう．
以下の関数が書けることになります．

%\vspace{-.15in}%[[
Definition uhoh (t : term) : term :=
  match t with
    | Abs f => f t
    | _ => t
  end.
]]

(*
Using an informal idea of Coq's semantics, it is easy to verify that the application [uhoh (Abs uhoh)] will run forever.  This would be a mere curiosity in OCaml and Haskell, where non-termination is commonplace, though the fact that we have a non-terminating program without explicit recursive function definitions is unusual.
*)
Coqの意味論に関する非形式的アイデアを使えば，[uho (Abs uho)]のような適用は無限ループになってしまうことが容易に確認できます．
停止しないことが普通にあるOCamlやHaskellでは，だからどうした，ということになるでしょうが，はっきりとした再帰が見えないプログラムが停止しないという事実は普通ではありません．

(*
%\index{termination checking}%For Coq, however, this would be a disaster.  The possibility of writing such a function would destroy all our confidence that proving a theorem means anything.  Since Coq combines programs and proofs in one language, we would be able to prove every theorem with an infinite loop.
*)
%\index{ていしせいけんさ@停止性検査}%しかし，Coqではこれを認めると酷いことになります．
このような関数を書けてしまうことは，定理を証明することの意味における信頼を破壊してしまいます．
Coqはプログラムや証明を1つの言語で組み合わせますので，無限ループですべての定理が証明できることになってしまいます．

(*
Nonetheless, the basic insight of HOAS is a very useful one, and there are ways to realize most benefits of HOAS in Coq.  We will study a particular technique of this kind in the final chapter, on programming language syntax and semantics. 
*)
とはいうものの，HOASに関する基本的な洞察はきわめて有用で，CoqでHOASの利点のほとんどを実現する方法があります．
この手の具体的な技法については最終章で，プログラミング言語の構文と意味に関して研究することにします．
*)

(**
(*
* An Interlude on Induction Principles
*)
* 帰納法原理についての間奏曲
*)

(**
(*
As we have emphasized a few times already, Coq proofs are actually programs, written in the same language we have been using in our examples all along.  We can get a first sense of what this means by taking a look at the definitions of some of the %\index{induction principles}%induction principles we have used.  A close look at the details here will help us construct induction principles manually, which we will see is necessary for some more advanced inductive definitions.
*)
なんどか強調したように，Coqの証明は実のところプログラムで，いままでの例はどれも同じ言語言語で書いたものです．
いままでに使った%\index{きのうほうのげんり@帰納法の原理}%帰納法の原理にはひと目でその意味を理解できるものがあります．
ここでじっくりと詳細に観察しておくと，帰納法の原理を自分の手で構成するのに役立ちます．
これを理解しておくことは，より進んだ帰納的定義を構成するのに必要です．
*)

Print nat_ind.
(** %\vspace{-.15in}%[[
nat_ind = 
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

(*
We see that this induction principle is defined in terms of a more general principle, [nat_rect].  The <<rec>> stands for "recursion principle," and the <<t>> at the end stands for [Type].
*)
この帰納法の原理は，さらに一般的な帰納法の原理[nat_rect]を用いて定義されていることがわかります．
<<rec>>は再帰原理を表し，最後についている<<t>>は[Type]を表すものです．
*)


Check nat_rect.
(** %\vspace{-.15in}% [[
nat_rect
     : forall P : nat -> Type,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

(*
The principle [nat_rect] gives [P] type [nat -> Type] instead of [nat -> Prop].  This [Type] is another universe, like [Set] and [Prop].  In fact, it is a common supertype of both.  Later on, we will discuss exactly what the significances of the different universes are.  For now, it is just important that we can use [Type] as a sort of meta-universe that may turn out to be either [Set] or [Prop].  We can see the symmetry inherent in the subtyping relationship by printing the definition of another principle that was generated for [nat] automatically:
*)
帰納法の原理[nat_rect]は[na -> Prop]型ではなく[nat -> Type]型の[P]を与えるものです．
この[Type]は[Set]や[Prop]とは別の領域です．(* universe の訳語は「領域」でよいか-nobsun *)
実際は[Set]と[Prop]の両方に共通の上位型です． (* supertype の訳語は「上位型」でよいか-nobsun *)
異なる領域であることの意味についての正確な議論は後で行います．
今のところは，[Type]は[Set]か[Prop]のどちらかになりうるメタ領域の一種として使えるということが重要です．
部分型付け関係における継承の対称性については，[nat]用に自動生成された別の帰納法原理の定義を表示すれば確認できます．
*)

Print nat_rec.
(** %\vspace{-.15in}%[[
nat_rec = 
fun P : nat -> Set => nat_rect P
     : forall P : nat -> Set,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

(*
This is identical to the definition for [nat_ind], except that we have substituted [Set] for [Prop].  For most inductive types [T], then, we get not just induction principles [T_ind], but also %\index{recursion principles}%recursion principles [T_rec].  We can use [T_rec] to write recursive definitions without explicit [Fixpoint] recursion.  For instance, the following two definitions are equivalent:
*)
これは，[Prop]を[Set]に置き換えた以外は，[nat_ind]の定義と同じです．
したがって，ほとんどの帰納型[T]に対して帰納法原理[T_ind]だけではなく，%\index{さいきほうのげんり@再帰法の原理}%再帰法の原理[T_rec]も手に入ります．
[T_rec]を使えば，[Fixpoint]を明示した再帰を使わなくても再帰的定義が書けます．
たとえば，以下の2つの定義は同じです．
*)

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
    | O => fun m => m
    | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).

Theorem plus_equivalent : plus_recursive = plus_rec.
  reflexivity.
Qed.

(**
(*
Going even further down the rabbit hole, [nat_rect] itself is not even a primitive.  It is a functional program that we can write manually.
*)
さらに不思議の国を進んでいきましょう．
[nat_rect]自身はプリミティブでさえありません．
自分の手で書くこともできる関数プログラムです．
*)

Print nat_rect.
(** %\vspace{-.15in}%[[
nat_rect = 
fun (P : nat -> Type) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

(*
The only new wrinkles here are, first, an anonymous recursive function definition, using the %\index{Gallina terms!fix}%[fix] keyword of Gallina (which is like [fun] with recursion supported); and, second, the annotations on the [match] expression.  This is a%\index{dependent pattern matching}% _dependently typed_ pattern match, because the _type_ of the expression depends on the _value_ being matched on.  We will meet more involved examples later, especially in Part II of the book.
*)
ここで，少し煩雑なのものの1つめは，Gallinaのキーワード%\index{Gallinaこう@Gallina項!fix}%[fix]（[fun]のように再帰をサポートしています）を使った無名再帰関数で，2つめは，[match]式上の注釈です．
この式の%\emph{型}%は，照合した%\emph{値}%に依存するので，このことを%\index{dependent pattern matching}%%\emph{依存型付けパターンマッチ}%といいます．
より詳しい説明は，後で，特に第2部で行います．

(*
%\index{type inference}%Type inference for dependent pattern matching is undecidable, which can be proved by reduction from %\index{higher-order unification}%higher-order unification%~\cite{HOU}%.  Thus, we often find ourselves needing to annotate our programs in a way that explains dependencies to the type checker.  In the example of [nat_rect], we have an %\index{Gallina terms!as}%[as] clause, which binds a name for the discriminee; and a %\index{Gallina terms!return}%[return] clause, which gives a way to compute the [match] result type as a function of the discriminee.
*)
%\index{かたすいろん@型推論}%依存型付けパターンマッチに対する型推論は非決定的です．
このことは%\index{こうかいたんいつか@高階単一化}%高階単一化の簡約により証明できます．
したがって，たびたび，依存関係を型検査器に教えるための注釈をプログラムに付ける必要にせまられます．
[nat_rect]の例では，%\index{Gallinaこう@Gallina項!as}%[as]節を用いて識別対象の名前を束縛し，%\index{Gallinaこう@Gallina項!return}%[return]節を用いて，識別対象の関数として[match]の結果の型を計算します．(* 判りにくい，よい表現がないものか-nobsun *)

(*
To prove that [nat_rect] is nothing special, we can reimplement it manually.
*)
手で再実装してみれば，[nat-rect]がなにも特別なものではないことを示せます．
*)

Fixpoint nat_rect' (P : nat -> Type) 
  (HO : P O)
  (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
    | O => HO
    | S n' => HS n' (nat_rect' P HO HS n')
  end.

(**
(*
We can understand the definition of [nat_rect] better by reimplementing [nat_ind] using sections.
*)
セクションを使って[nat_ind]を再実装すれば，この[nat_rect]の定義がよりよいものだと理解できます．
*)

Section nat_ind'.
   (**
   (*
   First, we have the property of natural numbers that we aim to prove.
   *)
   まず，証明すべき自然数の性質です．
   *)

  Variable P : nat -> Prop.

   (**
   (*
   Then we require a proof of the [O] case, which we declare with the command %\index{Vernacular commands!Hypothesis}%[Hypothesis], which is a synonym for [Variable] that, by convention, is used for variables whose types are propositions.
   *)
   それから，[O]の場合の証明が必要です．これを%\index{Vernacularこまんど@Vernacularコマンド!Hypothesis}%[Hypothesis]コマンドで宣言します．
   このコマンドは利便のためのもので，[Variable]のシノニムになっています．
   *)

  Hypothesis O_case : P O.

   (**
   (*
   Next is a proof of the [S] case, which may assume an inductive hypothesis.
   *)
   次は[S]の場合の証明です．
   ここで，帰納法の仮定が使えます．
   *)

  Hypothesis S_case : forall n : nat, P n -> P (S n).

   (**
   (*
   Finally, we define a recursive function to tie the pieces together.
   *)
   最後に，これらのピースをつなぐ再帰関数を定義します．
   *)

  Fixpoint nat_ind' (n : nat) : P n :=
    match n with
      | O => O_case
      | S n' => S_case (nat_ind' n')
    end.
End nat_ind'.

(**
(*
Closing the section adds the [Variable]s and [Hypothesis]es as new [fun]-bound arguments to [nat_ind'], and, modulo the use of [Prop] instead of [Type], we end up with the exact same definition that was generated automatically for [nat_rect].
*)
セクションを閉じたところで，[Variable]と[Hypothesis]が，新しい[nat_ind']への[fun]に束縛された引数を追加し，[Type]の代りに[Prop]を法として[nat_rect]の全く同じ定義を自動生成されました．

%\medskip%

(*
We can also examine the definition of [even_list_mut], which we generated with [Scheme] for a mutually recursive type.
*)
これは[even_list_mut]の定義でも確認するできます．
以前には相互再帰型に対しては[Scheme]を使って生成したものです．
*)

Print even_list_mut.
(** %\vspace{-.15in}%[[
  even_list_mut = 
  fun (P : even_list -> Prop) (P0 : odd_list -> Prop) 
    (f : P ENil) (f0 : forall (n : nat) (o : odd_list), P0 o -> P (ECons n o))
    (f1 : forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) =>
  fix F (e : even_list) : P e :=
    match e as e0 return (P e0) with
    | ENil => f
    | ECons n o => f0 n o (F0 o)
    end
  with F0 (o : odd_list) : P0 o :=
    match o as o0 return (P0 o0) with
    | OCons n e => f1 n e (F e)
    end
  for F
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
]]

(*
We see a mutually recursive [fix], with the different functions separated by %\index{Gallina terms!with}%[with] in the same way that they would be separated by <<and>> in ML.  A final %\index{Gallina terms!for}%[for] clause identifies which of the mutually recursive functions should be the final value of the [fix] expression.  Using this definition as a template, we can reimplement [even_list_mut] directly.
*)
相互再帰する[fix]を見ると，異なる関数は，MLだと<<and>>で分けるように，%\index{Gallinaこう@Gallina項!with}%[with]で分けることが判ります．
最後の%\index{Gallinaこう@Gallina項!for}%[for]節は，相互に再帰している関数のどちらが[fix]式の最終的な値になるべきかを識別します．
この定義をテンプレートにすると[even_list_mut]は以下のように直接定義できます．
*)

Section even_list_mut'.
  (**
  (*
  First, we need the properties that we are proving.
  *)
  まず，必要なのは証明すべき性質です．
  *)

  Variable Peven : even_list -> Prop.
  Variable Podd : odd_list -> Prop.

  (**
  (*
  Next, we need proofs of the three cases.
  *)
  次に3つの場合の証明がそれぞれ必要です．
  *)
  
  Hypothesis ENil_case : Peven ENil.
  Hypothesis ECons_case : forall (n : nat) (o : odd_list), Podd o -> Peven (ECons n o).
  Hypothesis OCons_case : forall (n : nat) (e : even_list), Peven e -> Podd (OCons n e).

  (**
  (*
  Finally, we define the recursive functions.
  *)
  最後に再帰関数を定義します．
  *)

  Fixpoint even_list_mut' (e : even_list) : Peven e :=
    match e with
      | ENil => ENil_case
      | ECons n o => ECons_case n (odd_list_mut' o)
    end
  with odd_list_mut' (o : odd_list) : Podd o :=
    match o with
      | OCons n e => OCons_case n (even_list_mut' e)
    end.
End even_list_mut'.

(**
(*
Even induction principles for reflexive types are easy to implement directly.  For our [formula] type, we can use a recursive definition much like those we wrote above.
*)
反映型の帰納法原理であっても直接実装するのは簡単です．
前に見た[formula]型なら，上で書いたものとほとんど同じように再帰的な定義が使えます．
*)

Section formula_ind'.
  Variable P : formula -> Prop.
  Hypothesis Eq_case : forall n1 n2 : nat, P (Eq n1 n2).
  Hypothesis And_case : forall f1 f2 : formula,
    P f1 -> P f2 -> P (And f1 f2).
  Hypothesis Forall_case : forall f : nat -> formula,
    (forall n : nat, P (f n)) -> P (Forall f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
      | Eq n1 n2 => Eq_case n1 n2
      | And f1 f2 => And_case (formula_ind' f1) (formula_ind' f2)
      | Forall f' => Forall_case f' (fun n => formula_ind' (f' n))
    end.
End formula_ind'.

(**
(*
It is apparent that induction principle implementations involve some tedium but not terribly much creativity.
*)
帰納法原理を実装するのはとんでもなく創造的というわけではなく，多少退屈であることは否めません．
*)


(**
(*
* Nested Inductive Types
*)
* ネストした帰納型
*)

(**
(*
Suppose we want to extend our earlier type of binary trees to trees with arbitrary finite branching.  We can use lists to give a simple definition.
*)
以前に見た二分木の型を有限分岐の多分木の型に拡張したいとしましょう．
リストを使って以下のように単純に定義できます．
*)

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.

(**
(*
This is an example of a%\index{nested inductive type}% _nested_ inductive type definition, because we use the type we are defining as an argument to a parameterized type family.  Coq will not allow all such definitions; it effectively pretends that we are defining [nat_tree] mutually with a version of [list] specialized to [nat_tree], checking that the resulting expanded definition satisfies the usual rules.  For instance, if we replaced [list] with a type family that used its parameter as a function argument, then the definition would be rejected as violating the positivity restriction.
*)
これは，定義しようとして型をパラメタ化した型族の引数として使っているので，%\index{ねすとしたきのうがた@ネストした帰納型}%%\emph{ネストした}%帰納型の定義例です．
Coqではこのような定義はどれも許されていません．
[nat_tree]で特定化したリストと相互参照的に[nat_tree]を定義しようとしているので，これを展開した定義が通常の規則を満すかどうかの検査にひっかかるということです．
たとえば，[list]を，関数を引数をもつ型族に置き換えると，定義が陽性要件違反となり，拒絶されます．

(*
As we encountered with mutual inductive types, we find that the automatically generated induction principle for [nat_tree] is too weak.
*)
相互帰納型のときに遭遇したように，自動生成した[nat_tree]の帰納法原理では弱いのだということが判ります．
*)

(* begin hide *)
(* begin thide *)
Check Forall.
(* end thide *)
(* end hide *)

Check nat_tree_ind.
(** %\vspace{-.15in}% [[
  nat_tree_ind
     : forall P : nat_tree -> Prop,
       (forall (n : nat) (l : list nat_tree), P (NNode' n l)) ->
       forall n : nat_tree, P n
]]

(*
There is no command like [Scheme] that will implement an improved principle for us.  In general, it takes creativity to figure out _good_ ways to incorporate nested uses of different type families.  Now that we know how to implement induction principles manually, we are in a position to apply just such creativity to this problem.
*)
より改善された原理を実装する[Scheme]のようなコマンドはありません．
一般的に，異なる型族をネストして使う%\emph{うまい}%方法を実現するには創造性が必要です．
相互帰納法原理の実装方法が判っているので，このような創造性をこの問題に適用する番です．

(*
Many induction principles for types with nested uses of [list] could benefit from a unified predicate capturing the idea that some property holds of every element in a list.  By defining this generic predicate once, we facilitate reuse of library theorems about it.  (Here, we are actually duplicating the standard library's [Forall] predicate, with a different implementation, for didactic purposes.)
*)
[list]をネストして使用する型に対する帰納法原理の多くは，リストの各要素がなんらかの性質を満すことを捕捉する単一の述語があれば，役に立ちます．
このような汎用的な述語をいったん定義してしまえば，ライブラリの定理を再利用するのが容易になります．
（ここでは，説明のために，標準ライブラリの[Forall]述語をそのまま写して別名で実装しています．）
*)

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | Nil => True
      | Cons h t => P h /\ All t
    end.
End All.

(**
(*
It will be useful to review the definitions of [True] and [/\], since we will want to write manual proofs of them below.
*)
以下にこれらの証明を書き下したいので，[True]および[/\]の定義を復習しておくと役に立ちます．
*)

Print True.
(** %\vspace{-.15in}%[[
  Inductive True : Prop :=  I : True
  ]]

(*
That is, [True] is a proposition with exactly one proof, [I], which we may always supply trivially.
*)
すなわち，[True]は，常に自明としてよい証明[I]を1つだけ持つ命題です．

(*
Finding the definition of [/\] takes a little more work.  Coq supports user registration of arbitrary parsing rules, and it is such a rule that is letting us write [/\] instead of an application of some inductive type family.  We can find the underlying inductive type with the %\index{Vernacular commands!Locate}%[Locate] command, whose argument may be a parsing token.%\index{Gallina terms!and}%
*)
[/\]の定義はもうすこし考えることがあります．
Coqは利用者が任意の構文解析規則を登録できるようになっており，帰納型族の適用ではなく[/\]を書ける規則を登録できます．
引数として構文解析トークンを取れる%\index{Vernacularこまんど@Vernacularコマンド!Locate}%[Locate]コマンドを使って，土台になる帰納型を見つけられます．
*)

Locate "/\".
(** %\vspace{-.15in}%[[
  "A /\ B" := and A B  : type_scope (default interpretation)
]]
*)

Print and.
(** %\vspace{-.15in}%[[
  Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
]]
%\vspace{-.1in}%
<<
  For conj: Arguments A, B are implicit
>>

(*
In addition to the definition of [and] itself, we get information on %\index{implicit arguments}%implicit arguments (and some other information that we omit here).  The implicit argument information tells us that we build a proof of a conjunction by calling the constructor [conj] on proofs of the conjuncts, with no need to include the types of those proofs as explicit arguments.
*)
[and]自体の定義のほかに，%\index{あんもくのひきすう@暗黙の引数}%に関する情報（および，ここでは省略したその他の情報）が得られます．
暗黙の引数に関する情報は，その連言の証明上で構成子[conj]を呼んで，証明を構成すること教えてくれます．
このとき，証明の型を引数に明示的に含める必要はありません．

%\medskip%

(*
Now we create a section for our induction principle, following the same basic plan as in the previous section of this chapter.
*)
帰納法原理のセクションを作ったので，次にこの章の直前の節で見たのと同じやり方で進めましょう．
*)

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.

  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree),
    All P ls -> P (NNode' n ls).

  (* begin hide *)
  (* begin thide *)
  Definition list_nat_tree_ind := O.
  (* end thide *)
  (* end hide *)

  (**
  (*
  A first attempt at writing the induction principle itself follows the intuition that nested inductive type definitions are expanded into mutual inductive definitions.
  *)
  ネストした帰納型の定義は相互帰納の定義に展開されるという直観にしたがって，まず帰納法原理自身を書きましょう．

  %\vspace{-.15in}%[[
  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls (list_nat_tree_ind ls)
    end

  with list_nat_tree_ind (ls : list nat_tree) : All P ls :=
    match ls with
      | Nil => I
      | Cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
    end.
  ]]

  (*
  Coq rejects this definition, saying
  *)
  Coqは以下のメッセージを残してこの定義を拒絶します．

<<
  Recursive call to nat_tree_ind' has principal argument equal to "tr"
  instead of rest.
>>

  (*
  There is no deep theoretical reason why this program should be rejected; Coq applies incomplete termination-checking heuristics, and it is necessary to learn a few of the most important rules.  The term "nested inductive type" hints at the solution to this particular problem.  Just as mutually inductive types require mutually recursive induction principles, nested types require nested recursion.
  *)
  このプログラムが拒絶される理由は深い理論的なものではありません．
  Coqは不完全な停止性判定のヒューリスティクスを適用しています．
  ここでは，最も重要な規則について学んでおく必要があります．
  *)

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
          match ls with
            | Nil => I
            | Cons tr' rest => conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
          end) ls)
    end.

  (**
  (*
  We include an anonymous [fix] version of [list_nat_tree_ind] that is literally _nested_ inside the definition of the recursive function corresponding to the inductive definition that had the nested use of [list].
  *)
  [list]をネストして使っている帰納的定義に関係する再帰関数の定義において，文字どおり%\emph{ネスト}の内側に無名[fix]を使った%[list_nat_tree_ind]を含めます．
  *)

End nat_tree_ind'.

(**
(*
We can try our induction principle out by defining some recursive functions on [nat_tree] and proving a theorem about them.  First, we define some helper functions that operate on lists.
*)
[nat_tree]上の再帰関数を定義し，それらに関する定理を証明することで，帰納法原理を試せます．
まず，リストを操作する補助関数をいくつか定義しましょう．
*)

Section map.
  Variables T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
      | Nil => Nil
      | Cons h t => Cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | Nil => O
    | Cons h t => plus h (sum t)
  end.

(**
(*
Now we can define a size function over our trees.
*)
これで木（ツリー）のサイズを測る関数を定義できます．
*)

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NNode' _ trs => S (sum (map ntsize trs))
  end.

(**
(*
Notice that Coq was smart enough to expand the definition of [map] to verify that we are using proper nested recursion, even through a use of a higher-order function.
*)
Coqは賢いので，高階関数を使っても[map]の定義を展開してネストした再帰を適切に使っていることを検証できます．
*)

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
    | NNode' n Nil => NNode' n (Cons tr2 Nil)
    | NNode' n (Cons tr trs) => NNode' n (Cons (ntsplice tr tr2) trs)
  end.

(**
(*
We have defined another arbitrary notion of tree splicing, similar to before, and we can prove an analogous theorem about its relationship with tree size.  We start with a useful lemma about addition.
*)
前回，別の木（ツリー）接合の概念を適当に定義したのと同じように，木（ツリー）のサイズとの関係について同様の定理を証明できます．
*)

(* begin thide *)
Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
  induction n1; crush.
Qed.
(* end thide *)

(**
(*
Now we begin the proof of the theorem, adding the lemma [plus_S] as a hint.
*)
これで，ヒントとして補題[plus_S]を追加して件の定理を証明します．
*)

Hint Rewrite plus_S.

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2)
  = plus (ntsize tr2) (ntsize tr1).
(* begin thide *)
  (**
  (*
  We know that the standard induction principle is insufficient for the task, so we need to provide a %\index{tactics!using}%[using] clause for the [induction] tactic to specify our alternate principle.
  *)
  標準の帰納法原理では不十分ということがわかりましたので，%\index{たくてぃっく@タクティック!using}%[induction]タクティックで[using]節を使って代替の原理を指定します．
  *)

  induction tr1 using nat_tree_ind'; crush.

  (**
  (*
  One subgoal remains: [[
  *)
  サブゴールが一つのこっています． [[
  n : nat
  ls : list nat_tree
  H : All
        (fun tr1 : nat_tree =>
         forall tr2 : nat_tree,
         ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1)) ls
  tr2 : nat_tree
  ============================
   ntsize
     match ls with
     | Nil => NNode' n (Cons tr2 Nil)
     | Cons tr trs => NNode' n (Cons (ntsplice tr tr2) trs)
     end = S (plus (ntsize tr2) (sum (map ntsize ls)))
 
     ]]
  (*
     After a few moments of squinting at this goal, it becomes apparent that we need to do a case analysis on the structure of [ls].  The rest is routine.
  *)
     このゴールを少しにらめば，[ls]の構造の場合わけが必要なことは明らかです．
     のこりはルーチンワークです．
  *)

  destruct ls; crush.

  (**
  (*
  We can go further in automating the proof by exploiting the hint mechanism.%\index{Vernacular commands!Hint Extern}%
  *)
  ヒント機構をうまく使えば先まで自動的に証明できるようになります．%\index{Vernacularこまんど@Vernacularコマンド!Hint Extern}%
  *)

  Restart.

  Hint Extern 1 (ntsize (match ?LS with Nil => _ | Cons _ _ => _ end) = _) =>
    destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.
(* end thide *)

(**
(*
We will go into great detail on hints in a later chapter, but the only important thing to note here is that we register a pattern that describes a conclusion we expect to encounter during the proof.  The pattern may contain unification variables, whose names are prefixed with question marks, and we may refer to those bound variables in a tactic that we ask to have run whenever the pattern matches.
*)
ヒントについては後の章で詳しく説明しますが，ここで注目すべき唯一重要なことは，証明の途中で遭遇することが予想される結論を記述するためのパターンを登録することです．
このパターンには単一化変数が含まれています．
変数名の先頭に疑問符が付きますのでそれと判ります．
パターンが照合されれば走るタクティック中のこれらの束縛変数を参照できるわけです．

(*
The advantage of using the hint is not very clear here, because the original proof was so short.  However, the hint has fundamentally improved the readability of our proof.  Before, the proof referred to the local variable [ls], which has an automatically generated name.  To a human reading the proof script without stepping through it interactively, it was not clear where [ls] came from.  The hint explains to the reader the process for choosing which variables to case analyze, and the hint can continue working even if the rest of the proof structure changes significantly.
*)
もとの証明が短いものであったために，ここではヒントを使う利点があま明確ではありません．
しかし，ヒントによって証明の読みやすさは根本的に改善されました．
以前の証明では自動生成されたローカル変数[ls]が参照されていました．
対話的に段階を踏むことなしに証明スクリプトを読むと，[ls]がどこから来たのか明確ではありません．
ヒントは場合分けにおいてどの変数を選択しているかの仮定を説明するもので，のこりの証明部分の構造が大幅に変更されても正しく働きます．
*)


(** * Manual Proofs About Constructors *)

(** It can be useful to understand how tactics like %\index{tactics!discriminate}%[discriminate] and %\index{tactics!injection}%[injection] work, so it is worth stepping through a manual proof of each kind.  We will start with a proof fit for [discriminate]. *)

Theorem true_neq_false : true <> false.

(* begin thide *)
(** We begin with the tactic %\index{tactics!red}%[red], which is short for "one step of reduction," to unfold the definition of logical negation. *)

  red.
(** %\vspace{-.15in}%[[
  ============================
   true = false -> False
]]

The negation is replaced with an implication of falsehood.  We use the tactic %\index{tactics!intro}%[intro H] to change the assumption of the implication into a hypothesis named [H]. *)

  intro H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   False
]]

This is the point in the proof where we apply some creativity.  We define a function whose utility will become clear soon. *)

  Definition toProp (b : bool) := if b then True else False.

(** It is worth recalling the difference between the lowercase and uppercase versions of truth and falsehood: [True] and [False] are logical propositions, while [true] and [false] are Boolean values that we can case-analyze.  We have defined [toProp] such that our conclusion of [False] is computationally equivalent to [toProp false].  Thus, the %\index{tactics!change}%[change] tactic will let us change the conclusion to [toProp false].  The general form [change e] replaces the conclusion with [e], whenever Coq's built-in computation rules suffice to establish the equivalence of [e] with the original conclusion. *)

  change (toProp false).
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp false
]]

Now the righthand side of [H]'s equality appears in the conclusion, so we can rewrite, using the notation [<-] to request to replace the righthand side of the equality with the lefthand side.%\index{tactics!rewrite}% *)

  rewrite <- H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp true
]]

We are almost done.  Just how close we are to done is revealed by computational simplification. *)

  simpl.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   True
]]
*)

  trivial.
Qed.
(* end thide *)

(** I have no trivial automated version of this proof to suggest, beyond using [discriminate] or [congruence] in the first place.

%\medskip%

We can perform a similar manual proof of injectivity of the constructor [S].  I leave a walk-through of the details to curious readers who want to run the proof script interactively. *)

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.
(* end thide *)

(** The key piece of creativity in this theorem comes in the use of the natural number predecessor function [pred].  Embodied in the implementation of [injection] is a generic recipe for writing such type-specific functions.

The examples in this section illustrate an important aspect of the design philosophy behind Coq.  We could certainly design a Gallina replacement that built in rules for constructor discrimination and injectivity, but a simpler alternative is to include a few carefully chosen rules that enable the desired reasoning patterns and many others.  A key benefit of this philosophy is that the complexity of proof checking is minimized, which bolsters our confidence that proved theorems are really true. *)

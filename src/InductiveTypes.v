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
Coqの論理の基盤はCIC（Calculus of Inductive Constructions）です。
CICは、関数型（function type）と帰納型（inductive type）という、比較的簡単な2つの機能だけで構成されていると考えられます。
そのような簡素な基盤であるCICから、事実上あらゆる数学の定理が証明可能であり、
それなりに手間をかければ、あらゆるプログラム検証を効果的に実行できるのです。
本章では、Coqにおける関数型プログラミングのために帰納と再帰を導入します。
本章の例の大部分は、Coqの標準ライブラリの機能を再現するものです。
標準ライブラリで使われている識別子を可能な場合にはそのまま採用しているので、大半の定義はデフォルトのCoq環境ですぐに使えます。

(*
The last chapter took a deep dive into some of the more advanced Coq features, to highlight the unusual approach that I advocate in this book.  However, from this point on, we will rewind and go back to basics, presenting the relevant features of Coq in a more bottom-up manner.  A useful first step is a discussion of the differences and relationships between proofs and programs in Coq.
*)
前章では、筆者が本書で伝えたい特異なアプローチに焦点をあてるべく、Coqの深淵に潜りました。
ここから先は基本に戻り、関連するCoqの機能をボトムアップで見ていくことにしましょう。
はじめの一歩として、証明とCoqプログラムの差異および関係について考えます。
*)


(**
(* * Proof Terms *)
* 証明項
*)

(** 
(*
Mainstream presentations of mathematics treat proofs as objects that exist outside of the universe of mathematical objects.  However, for a variety of reasoning tasks, it is convenient to encode proofs, traditional mathematical objects, and programs within a single formal language.  Validity checks on mathematical objects are useful in any setting, to catch typos and other uninteresting errors.  The benefits of static typing for programs are widely recognized, and Coq brings those benefits to both mathematical objects and programs via a uniform mechanism.  In fact, from this point on, we will not bother to distinguish between programs and mathematical objects.  Many mathematical formalisms are most easily encoded in terms of programs.
*)
数学では、数学的対象の世界の外側にあるものとして証明を扱うのが主流です。
(* 池渕：「証明は数学の世界の外側にある」と言われると違和感があった。多分mathematical objectは普通の数学で言う集合を指していて、集合と証明は区別される、ということを言いたいんだと思う。*)
しかし、証明、伝統的な数学的対象、そしてプログラムを単一の形式的言語により符号化すれば、さまざまな論証の作業にとって都合がよくなります。
数学の対象に対する検証は、どのような形であれ、書き間違いやつまらないミスの発見に役立ちます。
Coqでは、すでに広く認知されているプログラムへの静的型付けによる有益性を、数学の対象とプログラムに対して同じ仕組みで利用できます。
そういうわけで、これ以降は、プログラムと数学の対象とをわざわざ区別することはやめにします。
数学における形式主義のほとんどはプログラムによって簡単に符号化できるのです。

(*
Proofs are fundamentally different from programs, because any two proofs of a theorem are considered equivalent, from a formal standpoint if not from an engineering standpoint.  However, we can use the same type-checking technology to check proofs as we use to validate our programs.  This is the%\index{Curry-Howard correspondence}% _Curry-Howard correspondence_ %\cite{Curry,Howard}%, an approach for relating proofs and programs.  We represent mathematical theorems as types, such that a theorem's proofs are exactly those programs that type-check at the corresponding type.
*)
証明は、本来はプログラムとは違います。
ある定理に対する2つの証明は、工学的でなく形式的に見れば、等価なものであるとみなせるからです。
とはいえ、証明の検査には、プログラムの検証に使うのと同じ型検査の技術が使えます。
証明とプログラムは、_[Curry-Howard対応]_に%\index{Curry-Howard対応}%%\cite{Curry,Howard}%よって関連付けられるのです。
数学の定理を型として表現すると、その型を持つことを確認するプログラムそのものが、その定理の証明になります。

(*
The last chapter's example already snuck in an instance of Curry-Howard.  We used the token [->] to stand for both function types and logical implications.  One reasonable conclusion upon seeing this might be that some fancy overloading of notations is at work.  In fact, functions and implications are precisely identical according to Curry-Howard!  That is, they are just two ways of describing the same computational phenomenon.
*)
前章の例にはCurry-Howardの具体例を忍び込ませていました。
[->]という字句を、関数型と論理含意の両方を表すのに使っています。
それを見て、記法を多重定義しているのだろうと考えたかもしれません。
実際、関数と論理含意は、Curry-Howard対応によってまったく同一であるとみなせるのです！
これらは、計算における同一の現象を、2つの違う方法で表しているにすぎません。

(*
A short demonstration should explain how this can be.  The identity function over the natural numbers is certainly not a controversial program.
*)
この仕組みは簡単な例で示せます。
自然数上の恒等関数は自明なプログラムでしょう。

*)

Check (fun x : nat => x).
(** [: nat -> nat] *)

(**
(*
%\smallskip{}%Consider this alternate program, which is almost identical to the last one.
*)
%\smallskip{}%この恒等関数の代わりに次の恒等プログラムを考えてみましょう。上記の例とほどんと同じものです。
*)

Check (fun x : True => x).
(** [: True -> True] *)

(**
(* 
%\smallskip{}%The identity program is interpreted as a proof that %\index{Gallina terms!True}%[True], the always-true proposition, implies itself!  What we see is that Curry-Howard interprets implications as functions, where an input is a proposition being assumed and an output is a proposition being deduced.  This intuition is not too far from a common one for informal theorem proving, where we might already think of an implication proof as a process for transforming a hypothesis into a conclusion.
*)
%\smallskip{}%この恒等プログラムは、[True]%\index{Gallina terms!True}%、すなわち常に真であるという命題が自分自身を含意する、ということの証明であると解釈します。
含意を、Curry-Howard対応により、関数として解釈するわけです。
関数への入力は仮定された命題、関数からの出力は演繹された命題になります。
この見方は、定理を非形式的に証明するときの一般的な直観とかけ離れたものではありません。
含意を非形式的に証明するとき、仮説を結論に変換する工程であるかのように考えることもあるでしょう。

(*
There are also more primitive proof forms available.  For instance, the term %\index{Gallina terms!I}%[I] is the single proof of [True], applicable in any context.
*)
Coqにはさらに基本的な形の証明も用意されています。
たとえば、%\index{Gallina terms!I}%[I]という項は[True]の唯一の証明で、あらゆる文脈で適用可能です。
*)

Check I.
(** [: True] *)

(**
(*
%\smallskip{}%With [I], we can prove another simple propositional theorem.
*)
%\smallskip{}%[I]を使って、命題論理の別の定理を証明できます。
*)

Check (fun _ : False => I).
(** [: False -> True] *)

(**
(* %\smallskip{}%No proofs of %\index{Gallina terms!False}%[False] exist in the top-level context, but the implication-as-function analogy gives us an easy way to, for example, show that [False] implies itself.
*)
%\smallskip{}% %\index{Gallina terms!False}%[False]の証明はトップレベルの文脈には存在しません。
しかし、たとえば[False]が自分自身を含意することは、「関数としての含意」からの類推で簡単に示せます。
*)

Check (fun x : False => x).
(** [: False -> False] *)

(**
(*
%\smallskip{}%Every one of these example programs whose type looks like a logical formula is a%\index{proof term}% _proof term_.  We use that name for any Gallina term of a logical type, and we will elaborate shortly on what makes a type logical.
*)
%\smallskip{}%これらは、それぞれ型が論理式のように見えるプログラムの例になっており、いずれも%\index{しょうめいこう@証明項}% _[証明項]_と呼ばれます。
この名称は、論理的な型を持つ任意のGallinaの項を表すのに使うことにします。
どんな型が論理的であるかについては、すぐあとで詳細に述べます。

(*
In the rest of this chapter, we will introduce different ways of defining types.  Every example type can be interpreted alternatively as a type of programs or proofs.
*)
本章の残りの部分では、型を定義する方法をいくつか導入します。
例に挙げる型は、いずれもプログラムの型もしくは証明として解釈できます。

(*
One of the first types we introduce will be [bool], with constructors [true] and [false].  Newcomers to Coq often wonder about the distinction between [True] and [true] and the distinction between [False] and [false].  One glib answer is that [True] and [False] are types, but [true] and [false] are not.  A more useful answer is that Coq's metatheory guarantees that any term of type [bool] _evaluates_ to either [true] or [false].  This means that we have an _algorithm_ for answering any question phrased as an expression of type [bool].  Conversely, most propositions do not evaluate to [True] or [False]; the language of inductively defined propositions is much richer than that.  We ought to be glad that we have no algorithm for deciding our formalized version of mathematical truth, since otherwise it would be clear that we could not formalize undecidable properties, like almost any interesting property of general-purpose programs.
*)
最初に導入する型は[bool]であり、その構成子は[true]および[false]です。
Coqに不慣れのうちは、[True]と[true]あるいは[False]と[false]の違いによく戸惑います。
もっともらしく言うと、[True]と[False]は型であり、[true]と[false]は型ではありません。
もう少しきちんと言うと、[bool]型の任意の項は[true]か[false]のどちらかに_[評価]_され、そのことがCoqのメタ定理によって保証されています。
つまり、型が[bool]であるような式で表されたどんな問題に対しても、それに答える_[アルゴリズム]_があるということです。
逆に言うと、ほとんどの命題は[True]あるいは[False]には評価されません。
帰納的に定義される命題の言語には、もっと豊かな表現力があるのです。(* 意味がよくわからない -nobsun *)
数学的に形式化された真理をアルゴリズムで決定できないことは、残念なことではありません。
そのようなアルゴリズムがあれば、決定不能な性質の形式化は不可能であることが明らかになってしまい、汎用のプログラムが持つような興味深い性質のほとんどを形式化できなくなってしまうでしょう。
*)


(** 
(* * Enumerations *)
* 列挙
*)

(**
(* Coq inductive types generalize the %\index{algebraic datatypes}%algebraic datatypes found in %\index{Haskell}%Haskell and %\index{ML}%ML.  Confusingly enough, inductive types also generalize %\index{generalized algebraic datatypes}%generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic-datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.
*)
Coqの帰納型は、%\index{Haskell}%Haskellや%\index{ML}%MLにおける%\index{だいすうデータがた@代数データ型}%代数データ型を一般化したものです。
さらに、値への依存性を型に持たせることで、Coqの帰納型はGADT（一般化代数データ型）の一般化にもなっています。
混乱しやすいところですが、前章で説明した例を踏まえたうえで、帰納データ型における代数的データの基本的な使い方を丹念に見ておく価値はあります。
そのような型の値に関する証明を見ることで、HaskellやMLを普通に使っているだけでは手にできない知見が得られるからです。

(*
The singleton type [unit] is an inductive type:%\index{Gallina terms!unit}\index{Gallina terms!tt}%
*)
シングルトン型[unit]は帰納型です%\index{Gallinaこう@Gallina項!unit}\index{Gallinaこう@Gallina項!tt}%。
*)

Inductive unit : Set :=
  | tt.

(**
(* 
This vernacular command defines a new inductive type [unit] whose only value is [tt].
We can verify the types of the two identifiers we introduce: 
*)
このVernacularコマンドにより、[tt]を唯一の値として持つ新しい帰納型[unit]が定義されます。
導入した二つの識別子の型は次のようにして検証できます。
*)

Check unit.
(** [unit : Set] *)

Check tt.
(** [tt : unit] *)

(**
(*
%\smallskip{}%We can prove that [unit] is a genuine singleton type. 
*)
%\smallskip{}%[unit]が確かにシングルトン（値を一つしか持たない）型であることを証明しましょう。
*)

Theorem unit_singleton : forall x : unit, x = tt.

(**
(*
The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x].%\index{tactics!induction}%
*)
帰納型については、当たり前のこととして、その値の上で帰納法を使える点が重要です。
そして上記の定理の証明では、まさに帰納法を使います。
変数[x]に関する帰納法を進めるよう、Coqに指示します。%\index{tactics!induction}%
*)

(* begin thide *)
  induction x.

(**
(*
The goal changes to:
*)
ゴールは以下のようになります。
[[
 tt = tt
]]
*)

  (**
  (* 
  %\noindent{}%...which we can discharge trivially.
  *)
  %\noindent{}%これは自明ですね。(* うまい訳を思いつかない-nobsun *)
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
帰納法の仮説なしで帰納法による証明を書くのは、少し奇妙に思えます。
伝統的な数学における「場合分けによる証明」に対応するのは[destruct]タクティクです。%\index{tactics!destruct}%

[[
  destruct x.
]]

(*
%\noindent%...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.
*)
%\noindent %上記のように証明を始めても、同じ結果になったでしょう。
[induction]と[destruct]の二つのタクティクは、再帰のない帰納型に対しては常にまったく同じ振る舞いをします。
再帰的な型に関する証明であっても、場合分けによる証明で十分なことが少なくありません。
また、場合分けによる証明により、不必要な帰納法の仮説を増やさないで済むこともあります。

(*
What exactly _is_ the %\index{induction principles}%induction principle for [unit]?  We can ask Coq:
*)
ここで、[unit]の対する%\index{induction principles}%帰納法の原理をCoqに聞いてみましょう。
*)

Check unit_ind.
(** [unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u] *)

(**
(* 
%\smallskip{}%Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Recall from the last section that our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type %\index{Gallina terms!Prop}%[Prop], which appears in our induction principle; and the type %\index{Gallina terms!Set}%[Set], which we have seen a few times already.
*)
%\smallskip{}%ある型[T]を定義する[Inductive]コマンドによって、[T_ind]という名前がついた帰納法の原理も定義されます。
前節で述べたように、型、それに対する操作、論証のための帰納法の原理は、すべて同一の言語によって表され、同一の型システムにより記述されています。
あるプログラムが何なのか、ある証明が何なのかを知りたいときに鍵となるのは、上記の帰納法の原理に出てくる%\index{Gallinaこう@Gallina項!Prop}%[Prop]型と、すでに何度か登場している%\index{Gallinaこう@Gallina項!Set}%[Set]型とをきちんと区別することです。

(*
The convention goes like this: [Set] is the type of normal types used in programming, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.
*)
慣習によれば、[Set]はプログラミングで使われている通常の型を表す型で、そのような型の値がプログラムです。
[Prop]は論理的な命題を表す型で、そのような型の値が証明です。
したがって、帰納法の原理の型を見れば、帰納法の原理は「証明を構成するための関数」であることがわかります。

(*
Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].
*)
特に[unit_ind]では、[unit]値に対する述語[P]が限量化されています。
述語[P]が[tt]を満たすことの証明を提示できれば、[unit]型の任意の値[u]について[P]が成り立つことを証明したことになります。
さきほどの証明で述語[P]に相当するのは、[(fun u : unit => u = tt)]です。

(*
The definition of [unit] places the type in [Set].  By replacing [Set] with [Prop], [unit] with [True], and [tt] with [I], we arrive at precisely the definition of [True] that the Coq standard library employs!  The program type [unit] is the Curry-Howard equivalent of the proposition [True].  We might make the tongue-in-cheek claim that, while philosophers have expended much ink on the nature of truth, we have now determined that truth is the [unit] type of functional programming.
*)
[unit]の定義では、型を[Set]としています。
[Set]を[Prop]に置き換え、[unit]を[True]に置き換え、[tt]を[I]に置き換えると、Coqの標準ライブラリが採用している[True]の定義とぴったり一致します。
プログラムの型[unit]は、Curry-Howard対応によって述語[True]と同等です。
皮肉っぽくいえば、哲学者が真とは何かをどんなに時間をかけて論じたところで、ここでは真を関数プログラミングの[unit]型であると決めた、ということです。

%\medskip%

(*
We can define an inductive type even simpler than [unit]:%\index{Gallina terms!Empty\_set}%
*)
[unit]よりさらに単純な帰納型も定義できます。%\index{Gallinaこう@Gallina項!Empty\_set}%
*)

Inductive Empty_set : Set := .

(**
(* [Empty_set] has no elements.  We can prove fun theorems about it:
*)
[Empty_set]には要素がありません。
そんな[Empty_set]については面白い定理が証明できます。
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
[Empty_set]には要素がないので、この型の要素があるという事実は、あらゆることを含意します。
証明の中で[destruct x]ではなく[destruct 1]を使っているのは、限量化された変数のうち使用しないものが格下げされて数字で参照されるようになるからです。
（これには限量化子と含意の統一した扱いに関係した正当な理由があります。
含意とは、少なくともCoqの構成的論理（constructive logic、次章で詳しく説明します）の基盤においては証明に対する限量化にすぎず、その証明において限量化された変数が使われることはありません。
一般に、含意における仮説は、変数名ではなく数字で参照するほうが理にかなっています。
Coqは、適切な挙動を決定するにあたり、使用されない変数に対する限量化子を含意として扱います。）

(*
We can see the induction principle that made this proof so easy:
*)
さきほどの証明が簡単にできたのは、次のようにして確認できる帰納法の原理のおかげです。
*)

Check Empty_set_ind.
(** [Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e] *)

(**
(* %\smallskip{}%In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].
*)
%\smallskip{}%要するに、空集合から取ってきた値に対しては、どんな述語も自明に満たされるということです。(* 良いいいまわしを思いつかない-nobsun / "holds vacuously ..."は「自明に満たされる」で（TaPLの訳のときの"satisfied vacuously"の訳を参考にしました） -kshikano *)
さきほどの証明では、述語として[(fun _ : Empty_set => 2 + 2 = 5)]を選びました。

(*
We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: 
*)
この魔法の切り札は、実際のプログラミングで応用することもできます。
以下に、[Empty_set]の値を[unit]の値に変換する横着な方法を示します。
*)

Definition e2u (e : Empty_set) : unit := match e with end.

(**
(* We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.  It turns out that [Empty_set] is the Curry-Howard equivalent of [False].  As for why [Empty_set] starts with a capital letter and not a lowercase letter like [unit] does, we must refer the reader to the authors of the Coq standard library, to which we try to be faithful.
*)
この定義では、前章でパターンマッチに使った[match]を採用しています。
構成子を持たない型の値に対してパターンマッチをしているので、ほかの選択肢は必要ありません。
[Empty_set]はCurry-Howard対応により[False]と同等であることがわかります。
[unit]と違って[Empty_set]の先頭が大文字である理由は、Coqの標準ライブラリの作者に聞いてもらうしかありません。
本書はCoqの標準ライブラリに忠実に従っているだけです。

%\medskip%

(*
Moving up the ladder of complexity, we can define the Booleans:%\index{Gallina terms!bool}\index{Gallina terms!true}\index{Gallina terms!false}%
*)
今度は複雑なほうへ話を進めましょう。論理値は次のように定義できます。%\index{Gallinaこう@Gallina項!bool}\index{Gallinaこう@Gallina項!true}\index{Gallinaこう@Gallina項!false}%
*)

Inductive bool : Set :=
| true
| false.

(**
(* 
We can use less vacuous pattern matching to define Boolean negation.%\index{Gallina terms!negb}% 
*)
それほど自明ではないパターンマッチを使って論理否定を定義できます。%\index{Gallinaこう@Gallina項!negb}%
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

ちょうど二つの構成子を持つ任意の帰納型に対して使えるようにオーバーロードされた[if]記法%\index{Gallinaこう@Gallina項!if}%を使って、上の定義の構文糖衣を剥がすこともできます。
*)

Definition negb' (b : bool) : bool :=
  if b then false else true.

(**
(*
We might want to prove that [negb] is its own inverse operation.
*)
[negb]の逆演算が[negb]になることは証明しておきたいところです。
*)

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
(* begin thide *)
  destruct b.

  (**
  (*
  After we case-analyze on [b], we are left with one subgoal for each constructor of [bool].
  *)
  [b]に関する場合分けをすべて調べると、[bool]の構成子ごとにサブゴールが一つずつ残ります。
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
最初のサブゴールはCoqの計算規則から示せるので、簡単に片付きます。
*)

  reflexivity.

(**
(* 
Likewise for the second subgoal, so we can restart the proof and give a very compact justification.%\index{Vernacular commands}%
*)
2つめのサブゴールも同様なので、証明を始めから再開して以下の簡潔な一行で証明を終わらせられます。%\index{Vernacularこまんど@Vernacularコマンド!Restart}%
 (* いけぶち：「正当化」は日本語として不自然に感じた。うまい訳は思い付かなかったので意訳にしてみた。 *)
*)

Restart.

  destruct b; reflexivity.
Qed.
(* end thide *)

(**
(*
Another theorem about Booleans illustrates another useful tactic.%\index{tactics!discriminate}%
*)
論理値に関する別の定理を使って、便利なタクティクをもう一つ紹介しましょう。%\index{たくてぃく@タクティク!discriminate}%
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
[discriminate]タクティクを使うと、ある帰納型の二つの値は、それらが別々の構成子で形成される場合には常に等しくない、ということを証明できます。
この場合には[true]と[false]が別々の構成子です。

(*
At this point, it is probably not hard to guess what the underlying induction principle for [bool] is.
*)
ここまでくれば、[bool]に対する帰納法の原理がどのようなものか、簡単に推測できるでしょう。
*)

Check bool_ind.
(** [bool_ind : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b] *)

(**
(*
%\smallskip{}%That is, to prove that a property describes all [bool]s, prove that it describes both [true] and [false].
*)
%\smallskip{}%すなわち、すべての[bool]値についてある性質が成り立つことを証明するには、その性質が[true]と[false]の両方で成り立つことを証明すればよいということです。

(*
There is no interesting Curry-Howard analogue of [bool].  Of course, we can define such a type by replacing [Set] by [Prop] above, but the proposition we arrive at is not very useful.  It is logically equivalent to [True], but it provides two indistinguishable primitive proofs, [true] and [false].   In the rest of the chapter, we will skip commenting on Curry-Howard versions of inductive definitions where such versions are not interesting.
*)
[bool]のCurry-Howard対応版はあまり面白くありません。
もちろん、上述の定義の[Set]を[Prop]に置き換えた型を定義することは可能です。しかし、それで得られる命題にあまり使い手はありません。
これは論理的には[True]に相当しますが、それによって得られる[true]と[false]の原始的な二つの証明は区別が不可能です。(* ここは意味がよくわからない-nobsun *)
以降では、帰納的な定義のCurry-Howard対応版について、このようにあまり意味がないものについては特に言及しないことにします。
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
帰納型のもっとも単純な例として一般的なのは自然数です。文字通り、もっとも自然な例といえるでしょう。%\index{Gallinaこう@Gallina項!nat}\index{Gallinaこう@Gallina項!O}\index{Gallinaこう@Gallina項!S}%
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(**
(*
The constructor [O] is zero, and [S] is the successor function, so that [0] is syntactic sugar for [O], [1] for [S O], [2] for [S (S O)], and so on.
*)
構成子[O]はゼロ、[S]は後者関数です。したがって、[0]は[O]の構文糖衣、[1]は[S O]の構文糖衣、[2]は[S (S O)]の構文糖衣といった具合になります。

(*
Pattern matching works as we demonstrated in the last chapter:%\index{Gallina terms!pred}%
*)
前章で見たようにパターンマッチができます。
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
比較的単純な帰納型なので[destruct]による場合分けを使って定理を証明することも可能ですが、ここでは正真正銘の帰納的な定理を考えてみましょう。
話を面白くするために、まずは再帰関数が必要です。
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
[Fixpoint]は、Coqで再帰関数を定義する仕組みでしたね。
[plus]に関する定理には、帰納法を使わずに証明できるものがあります。
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
[plus]の定義を展開すると、採用される選択肢が構文だけから明らかな[match]式が得られるので、[plus]の適用はCoqの計算規則によって自動的に単純化されます。
これは引数の順序を逆にすると機能しなくなり、帰納法が必要になります。
*)

Theorem n_plus_O : forall n : nat, plus n O = n.
(* begin thide *)
  induction n.

(**
(*
Our first subgoal is [plus O O = O], which _is_ trivial by computation.
*)
最初のサブゴールは[plus O O = O]で、この計算は_[自明]_です。
*)

  reflexivity.

(**
(*
Our second subgoal requires more work and also demonstrates our first inductive hypothesis.
*)
二つめのサブゴールにはもう少し手がかかります。これは帰納法の仮説の最初の例でもあります。

[[
  n : nat
  IHn : plus n O = n
  ============================
   plus (S n) O = S n
 
]]

(*
We can start out by using computation to simplify the goal as far as we can.%\index{tactics!simpl}%
*)
このゴールを計算でできるだけ単純化することから始めましょう。%\index{たくてぃくす@タクティクス!simpl}%
*)

  simpl.

(**
(*
Now the conclusion is [S (plus n O) = S n].  Using our inductive hypothesis:
*)
これにより結論は[S (plus n O) = S n]となります。
ここで帰納法の仮説を使います。
*)

  rewrite IHn.

(**
(*
%\noindent{}%...we get a trivial conclusion [S n = S n].
*)
%\noindent{}%すると自明な結論[S n = S n]が得られます。
*)

  reflexivity.

(**
(*
Not much really went on in this proof, so the [crush] tactic from the [CpdtTactics] module can prove this theorem automatically.
*)
この証明は、それほど手がかかるものではありませんでした。
そのため、[CpdtTactics]モジュールの[crush]タクティクを使ってこの定理を自動的に証明できます。
*)

Restart.

  induction n; crush.
Qed.
(* end thide *)

(**
(*
We can check out the induction principle at work here:
*)
ここで使われる帰納法の原理は次のようにして確認できます。
*)

Check nat_ind.
(** %\vspace{-.15in}% [[
  nat_ind : forall P : nat -> Prop,
            P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  ]]

(*
Each of the two cases of our last proof came from the type of one of the arguments to [nat_ind].  We chose [P] to be [(fun n : nat => plus n O = n)].  The first proof case corresponded to [P O] and the second case to [(forall n : nat, P n -> P (S n))].  The free variable [n] and inductive hypothesis [IHn] came from the argument types given here.
*)
先ほどの証明における二つの場合分けは、それぞれ、[nat_ind]に対する引数のうちの一つが持つ型に対応しています。
[P]を[(fun n : nat => plus n O = n)]としましょう。
証明の場合分けのうち一つめは[P O]に対応し、二つめは[(forall n : nat, P n -> P (S n))]に対応します。
自由変数[n]および帰納法の仮説[IHn]は、これら引数の型に由来するのです。

(*
Since [nat] has a constructor that takes an argument, we may sometimes need to know that that constructor is injective.%\index{tactics!injection}\index{tactics!trivial}%
*)
[nat]には、引数を一つとる構成子があります。
この構成子が単射（injective）であることは確認しておきたいものです。%\index{たくてぃくす@タクティクス!injection}\index{たくてぃくす@タクティクス!trivial}%
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
[injection]タクティクは、数字で指定された前提を参照し、等号の左右にある同じ構成子で構成された項について、対応する引数間の新しい同等性を追加します。(* equalities が複数形なのはなぜ-nobsun *)
結果的に[n = m -> n = m]を証明することになるので、その名も[trivial]というタクティクで証明を完了できます。
この[trivial]タクティクは、ユーザが指定したデータベース（のちほど拡張方法を説明します）にあるさまざまな単一の証明ステップを試します。

(*
There is also a very useful tactic called %\index{tactics!congruence}%[congruence] that can prove this theorem immediately.  The [congruence] tactic generalizes [discriminate] and [injection], and it also adds reasoning about the general properties of equality, such as that a function returns equal results on equal arguments.  That is, [congruence] is a%\index{theory of equality and uninterpreted functions}% _complete decision procedure for the theory of equality and uninterpreted functions_, plus some smarts about inductive types.
*)
この定理を一発で証明できる%\index{たくてぃくす@タクティクス!congruence}%[congruence]という便利なタクティクもあります。
[congruence]タクティクは、[discriminate]および[injection]を一般化し、さらに「関数は等しい引数について等しい結果を返す」といった同等性についての一般的な性質に対する論証を追加してくれます。
すなわち、[congruence]は%\index{みかいしゃくかんすうとどういつせいのりろん@未解釈関数と同一性の理論}%、_[未解釈関数と同一性の理論に対する完全な決定手続き]_に帰納型に関するさまざまな機能を追加したタクティクだといえます。
(* the theory of equality and uninterpreted functions は何のことか？-nobsun *)
(* いけぶち：the theory of equality and uninterpreted functions は論理記号が = のみで、項が(symbolicな)関数(や定数)から成るような公理の集合のことだと思います。 *)

%\medskip%

(*
We can define a type of lists of natural numbers.
*)
自然数のリストの型は以下のように定義できます。
*)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

(**
(*
Recursive definitions over [nat_list] are straightforward extensions of what we have seen before.
*)
すでに見た例を素直に拡張することで[nat_list]上の再帰的定義が得られます。
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
やはり前と同様に、帰納的な定理の証明を効率的に自動化できます。
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
一般に、「木」（tree）の型はすべて帰納型として実装可能です。
たとえば、自然数の二分木は以下のように実装できます。
*)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

(**
(*
Here are two functions whose intuitive explanations are not so important.  The first one computes the size of a tree, and the second performs some sort of splicing of one tree into the leftmost available leaf node of another. 
*)
ここで関数を二つ用意します。
一つは木のサイズを計算する関数で、もう一つは一方の木を他方の木の最も左にある葉に接合する関数ですが、いずれも直観的な説明はあまり重要ではありません。
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
こうした証明が簡単にできるのは便利なことですが、木の帰納法の原理がどのように提示されているか確認することで、その動作も詳しく調べておいたほうがいいでしょう。
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
いつものように二つの場合分けになっており、それぞれの場合分けが[nat_btree]の構成子に対応していることがわかります。
*)

(**
(*
* Parameterized Types
*)
* パラメータ付き型
(* parameterized type の定訳は？-nobsun *)
(* いけぶち：とりあえずよく使われる「-付き」にしてみた *)
*)

(**
(*
We can also define %\index{polymorphism}%polymorphic inductive types, as with algebraic datatypes in Haskell and ML.%\index{Gallina terms!list}\index{Gallina terms!Nil}\index{Gallina terms!Cons}\index{Gallina terms!length}\index{Gallina terms!app}% 
*)
HaskellやMLにおける代数データ型と同様、多相的な帰納型も定義できます。%\index{たそうせい@多相性}%
%\index{Gallinaこう@Gallina項!list}\index{Gallinaこう@Gallina項!Nil}\index{Gallinaこう@Gallina項!Cons}\index{Gallinaこう@Gallina項!length}\index{Gallinaこう@Gallina項!app}% 
*)

(* Set Asymmetric Patterns. が必要なので、脚注をいれたほうがよさそう -kshikano *)

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
Coqには、同じパラメータを共有するさまざまな定義に対する便利な省略記法があります。これは、Coqの_[セクション]_（[Section]）という仕組みを利用したものです。
%\index{せくしょん@セクション}\index{Vernacularこんまんど@Vernacularコマンド!Section}\index{Vernacularこまんど@Vernacularコマンド!Variable}
上記のコードブロックは下記のように書いても同じです。
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
セクションで使った[Variable]は、セクションを[End]で終端したあと、定義された各識別子に対する追加の関数パラメータとして付加されます。
[Implicit Arguments]%~\index{Vernacularこまんど@Vernacularコマンド!Implicit Arguments}%コマンドを使って、[Nil]を使用したときに[T]が推論されるようにしています。
[Cons]に対しては、Coqのヒューリスティクスによって、すでに同様の方針が適用されるようになっています。
これは、本章のソースファイルの冒頭に、[Set Implicit Arguments]%~\index{Vernacularこまんど@Vernacularコマンド!Set Implicit Arguments}%コマンドがあるからです。
定義が適切に保存されたかどうかは、[Print]コマンドを使って確認します。
[Print]コマンドは、[Check]コマンドに似ていますが、シンボルの型だけではなく定義も表示します。
*)

Print list.
(** %\vspace{-.15in}% [[
  Inductive list (T : Set) : Set :=
    Nil : list T | Cons : T -> list T -> list T
]]

(*
The final definition is the same as what we wrote manually before.  The other elements of the section are altered similarly, turning out exactly as they were before, though we managed to write their definitions more succinctly.
*)
このように、[list]の最終的な定義は以前に手書きしたものと同じです。
[list]以外の定義も、セクションの中では前より少し簡潔に書けているにもかかわらず、以前の定義とぴったり同じになっていることがわかります。
*)

Check length.
(** %\vspace{-.15in}% [[
  length
     : forall T : Set, list T -> nat
]]

(*
The parameter [T] is treated as a new argument to the induction principle, too.
*)
パラメータ[T]は、帰納法の原理に対する新しい引数としても扱われます。
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
そのため、構成子[Cons]への引数として型[T]には確かに意味があるのですが、[list_ind]の型における帰納部（すなわち上記の3行め）では[T]に限量子が付いていません。
それ以外のすべての引数は明示的に限量化されているにもかかわらず、[T]は限量化されていないのです。
他の帰納的な定義におけるパラメータは、帰納法の原理で表明されているとおりに扱われます。
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
相互に参照する帰納型を以下のように定義できます。
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

大まかに見れば、いずれもこれまでの例と同じです。しかし、これまでと同じ要領で定理を証明しようとすると、様子が変わります。
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
  帰納法の仮説がないので、このゴールを証明するには別の帰納法から始めるしかありません。
  しかし、別の帰納法から始めても同じような状況になるので、何も得られないまま帰納法の無限連鎖に陥ります。
  問題なのは、Coqによる帰納法の原理[T_ind]の生成が不完全なことです。
  デフォルトでは、相互参照がない帰納法の原理しか生成されないのです。
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
この型には帰納法の仮定がどこにも含まれていません。
帰納法の仮定を手に入れるには、%\index{Vernacularこまんど@Vernacularコマンド!Scheme}%[Scheme]コマンドを使うことで、必要に応じて相互帰納法の原理を要求します。
*)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

(**
(*
This invocation of [Scheme] asks for the creation of induction principles [even_list_mut] for the type [even_list] and [odd_list_mut] for the type [odd_list].  The [Induction] keyword says we want standard induction schemes, since [Scheme] supports more exotic choices.  Finally, [Sort Prop] establishes that we really want induction schemes, not recursion schemes, which are the same according to Curry-Howard, save for the [Prop]/[Set] distinction.
*)
このように[Scheme]を呼び出すことで、型[even_list]の帰納法の原理[even_list_mut]と、型[odd_list]の帰納法の原理[odd_list_mut]を作るように指示しています。
[Induction]キーワードを指定しているのは、標準の帰納法スキームを要求するためです。[Scheme]キーワードは、かなり奇妙な選択肢にも対応しているので、この[Induction]キーワードが必要になります。
最後に[Srot Prop]コマンドを指定しているのは、いま要求しているのが帰納法のスキームであって再帰のスキームではないことを確実にするためです。
Curry-Howard対応により、帰納法のスキームと再帰のスキームは、[Prop]と[Set]の違いを除けば同じになります。
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
これが、そもそも必要としていた帰納法の原理になります。

(*
The [Scheme] command is for asking Coq to generate particular induction schemes that are mutual among a set of inductive types (possibly only one such type, in which case we get a normal induction principle).  In a sense, it generalizes the induction scheme generation that goes on automatically for each inductive definition.  Future Coq versions might make that automatic generation smarter, so that [Scheme] is needed in fewer places.  In a few sections, we will see how induction principles are derived theorems in Coq, so that there is not actually any need to build in _any_ automatic scheme generation.
*)
[Scheme]コマンドは、いくつかの帰納型の集合において相互に関連するような帰納法のスキームを具体的に生成するよう、Coqに指示するためものです（帰納型が1つだけの場合もあり、その場合には通常の帰納法の原理が得られます）。
Coqでは帰納的な定義ごとに帰納法のスキームが自動生成されますが、これはその一般化だといえるでしょう。
将来のCoqのバージョンでは、この自動生成がもっとスマートになって、[Scheme]コマンドが必要な場面が少なくなるかもしれません。
この後の節で説明するように、帰納法の原理はCoqにおいて導出される定理です。
したがって、自動的なスキーム生成を組み込む必要は、実際のところどこにもありません。

(*
There is one more wrinkle left in using the [even_list_mut] induction principle: the [induction] tactic will not apply it for us automatically.  It will be helpful to look at how to prove one of our past examples without using [induction], so that we can then generalize the technique to mutual inductive types.%\index{tactics!apply}% 
*)
帰納法の原理[even_list_mut]には、使用にあたって困ったことがもう1つあります。
[induction]タクティクによって自動的に適用されないのです。
以前の例を[induction]を使わないで証明する方法を見てみると、相互帰納型への一般化に役立つでしょう。%\index{たくてぃくす@タクティクス!apply}%
*)

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply nat_ind.
  (**
  (*
  Here we use [apply], which is one of the most essential basic tactics.  When we are trying to prove fact [P], and when [thm] is a theorem whose conclusion can be made to match [P] by proper choice of quantified variable values, the invocation [apply thm] will replace the current goal with one new goal for each premise of [thm].
  *)
  ここで使っている[apply]は、基本的なタクティクのなかでも特に本質的なものです。
  [P]を証明しようとしているとき、限量化された変数の値をうまく選ぶことで帰結を[P]にマッチするようにできる定理[thm]があれば、[apply thm]を呼び出すことで、[thm]の仮定のそれぞれに対する新たなゴールへと現在のゴールを置き換えられます。

  (*
  This use of [apply] may seem a bit _too_ magical.  To better see what is going on, we use a variant where we partially apply the theorem [nat_ind] to give an explicit value for the predicate that gives our induction hypothesis.
  *)
  このような[apply]の使い方は黒魔術に見えるかもしれません。
  背景を理解するために、帰納法の仮定を与えてくれる述語に明示的な値を渡すことで定理[nat_ind]を部分適用したものを使ってみましょう。
  *)

  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

(**
(*
From this example, we can see that [induction] is not magic.  It only does some bookkeeping for us to make it easy to apply a theorem, which we can do directly with the [apply] tactic.
*)
この例を見れば、[induction]が魔法ではないことがわかります。
[induction]は、[apply]タクティクを使って定理を直接簡単に適用できるように、帳簿のようなものを付けてくれているだけなのです。

(*
This technique generalizes to our mutual example:
この技法を相互帰納型の例に一般化しましょう。
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
必要なのは、相互帰納型のそれぞれに、対応する二つの述語を指定することだけです。
証明支援器が余分な述語を推論してくれることは一般に望めないので、この方法で相互帰納を適用するのがもっとも直接的でしょう。
*)


(**
(*
* Reflexive Types
*)
* 反射的型
*)

(**
(*
A kind of inductive type called a _reflexive type_ includes at least one constructor that takes as an argument _a function returning the same type we are defining_.  One very useful class of examples is in modeling variable binders.  Our example will be an encoding of the syntax of first-order logic.  Since the idea of syntactic encodings of logic may require a bit of acclimation, let us first consider a simpler formula type for a subset of propositional logic.  We are not yet using a reflexive type, but later we will extend the example reflexively.
*)
「定義している型と同じ型を返す関数」を引数として取る構成子を、少くとも一つ持つような帰納型のことを、_[反射的型]_と呼びます。
反射的型の実用的な例として、変数束縛のモデリングが挙げられます。
ここでは、一階述語論理の構文を符号化する例を紹介します。
論理の構文を符号化するという考え方には少しばかり慣れが必要でしょうから、より単純な、命題論理のサブセットに対する論理式型[pformula]から考えてみましょう。
まだ反射的型は使いませんが、あとでこの例を反射的型へと拡張します。
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
ここで肝心なのは、_[構文]_と_[意味]_をはっきり区別することです。
たとえば、[Truth]は構文であり、その意味は[True]です。
意味を明らかにするには、次のような再帰関数が使えます。
この関数の定義にある[/\]という中置演算子%\index{Gallinaえんざんし@Gallina演算子!/\textbackslash}%は、標準ライブラリにある型族[and]のインスタンス%\index{Gallinaこう@Gallina項!and}%に展開されます。
型族[and]は、連言の実装です。
連言の[Prop]にCurry-Howard対応するのは、関数プログラミングにおける通常のペア型です（Coqでは標準ライブラリにある型族%\index{Gallinaこう@Gallina項!prod}%[prod]に相当）。
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
ここまではウォーミングアップです。これから紹介する新しい機能である反射的型は、この命題論理の論理式型の例ではまだ使っていません。
そこで次は一階述語論理の論理式型[formula]を考えてみましょう。
[formula]を返す関数を再帰的な引数として構成子に与えられると、次のようにして[formula]を簡単に定義できることがわかります。
*)

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

(**
(*
Our kinds of formulas are equalities between naturals, conjunction, and universal quantification over natural numbers.  We avoid needing to include a notion of "variables" in our type, by using Coq functions to encode the syntax of quantification.  For instance, here is the encoding of [forall x : nat, x = x]:%\index{Vernacular commands!Example}%
*)
[formula]としてありうるのは、自然数の間の等号、連言、自然数に対する全称限量化です。(* equalityの訳語に迷う-nobsun *)
ここで、型から「変数」という概念が不要になっていることに注目してください。
限量化の構文は、Coqの関数を使って符号化します。
たとえば、[forall x : nat, x = x]は次のように符号化できます。%\index{Vernacularこまんど@Vernacularコマンド!Example}%
*)

Example forall_refl : formula := Forall (fun x => Eq x x).

(**
(*
We can write recursive functions over reflexive types quite naturally.  Here is one translating our formulas into native Coq propositions.
*)
反射的型の上の再帰関数はとても自然に書けます。
たとえば、いま定義した[formula]型の論理式をCoqの命題に翻訳する再帰関数は次のように書けます。
*)

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

(**
(* We can also encode a trivial formula transformation that swaps the order of equality and conjunction operands. *)
論理式に対する単純な変換も符号化できます。
等号と連言の順序を変更する変換の例を次に示します。
*)

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
この変換によって真が偽になることがないことを証明しておきましょう。
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
この証明の背後にある帰納法の原理は次のように確認できます。
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
[Forall]に関する場合分け（3つめの場合分け）に注目してみると、「引数である関数[f1]の任意の適用」に対して定理が成り立つことを仮定してよい、となっています。
つまり、Coqの帰納法の原理は、「帰納法に関する変数のテキスト上の見た目が常に帰納法の仮定によって短くなる」という単純な法則に従っているわけではないということです。
このような柔軟性があっても体系が不健全にならないことは、Coqのメタ定理の開発者たちが検証してくれています。

%\medskip%

(*
Up to this point, we have seen how to encode in Coq more and more of what is possible with algebraic datatypes in %\index{Haskell}%Haskell and %\index{ML}%ML.  This may have given the inaccurate impression that inductive types are a strict extension of algebraic datatypes.  In fact, Coq must rule out some types allowed by Haskell and ML, for reasons of soundness.  Reflexive types provide our first good example of such a case; only some of them are legal.
*)
ここまでは、%\index{Haskell}%Haskellや%\index{ML}%MLの代数データ型でできることの多くをCoqで符号化する方法を見てきました。
そのため、帰納型とは代数データ型の拡張であるという不正確な印象を抱かせてしまったかもしれません。
実際には、HaskellやMLの代数データ型で許されているような型であっても、Coqでは排除が必要なものがあります。
これは健全性を維持するためです。
反射的型は、そのことを説明する最初の好例です。Coqでは、ある種の反射的型だけしか許されていません。

(*
Given our last example of an inductive type, many readers are probably eager to try encoding the syntax of %\index{lambda calculus}%lambda calculus.  Indeed, the function-based representation technique that we just used, called%\index{higher-order abstract syntax}\index{HOAS|see{higher-order abstract syntax}}% _higher-order abstract syntax_ (HOAS)%~\cite{HOAS}%, is the representation of choice for lambda calculi in %\index{Twelf}%Twelf and in many applications implemented in Haskell and ML.  Let us try to import that choice to Coq:
*)
読者のなかには、さきほどの帰納型の例を見て、%\index{らむだけいさん@λ計算}%λ計算の構文をエンコードしようとする人も多いでしょう。
さきほどの例で見たような、関数による表現技法は、_[高階抽象構文]_（HOAS、higher-order abstract syntax）%\index{こうかいちゅうしょうこうぶん@高階抽象構文}\index{HOAS|see{高階抽象構文}}%と呼ばれています%~\cite{HOAS}%。HOASは、%\index{Twelf}%Twelfをはじめ、HaskellやMLで実装されたアプリケーションにおけるλ計算の表現として採用されています。
この技法をCoqでも使ってみましょう。
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
ここで抵触したのは、帰納的定義に対する_[厳密陽性要件]_（strict positivity requirement）という制限です%\index{げんみつようせいようけん@厳密陽性要件}\index{ようせいようけん@陽性要件}%。
厳密陽性要件では、定義しようとしている型が、構成子の引数の型において矢印の左側に出現してはいけないことになっています。
もし再帰的な出現があれば、一番外側の矢印の左側に再帰的な出現が明らかに必要なので、構成子の型は引数と結果の列として見ればよい、というのがポイントです。
上記の定義では、[term -> term]型という形で、いま定義しようとしている[term]型が矢印の左側に出現する引数が関与しており、これが陽性要件に違反します。
ただし、[App]の型は問題ありません。
[App]では、すべての[term]の出現が、構成子の引数か最終結果の型のいずれかだからです。

(*
Why must Coq enforce this restriction?  Imagine that our last definition had been accepted, allowing us to write this function:
*)
なぜCoqにはこのような制限があるのでしょうか。
さきほどの定義が許容されるとどうなるか想像してみましょう。
以下の関数が書けることになります。

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
Coqの意味論について非形式的に考えてみると、[uho (Abs uho)]のような適用が無限ループになってしまうことが容易に確認できます。
明示的に再帰関数として定義されていない停止しないプログラムの存在は異常ですが、停止しないことが普通にあるOCamlやHaskellでは「だからどうした」という話かもしれません。

(*
%\index{termination checking}%For Coq, however, this would be a disaster.  The possibility of writing such a function would destroy all our confidence that proving a theorem means anything.  Since Coq combines programs and proofs in one language, we would be able to prove every theorem with an infinite loop.
*)
%\index{ていしせいけんさ@停止性検査}%しかし、Coqでこれを認めるとひどいことになります。
このような関数を書けてしまうようでは、定理を証明することに意味があるという私たちの信念が台無しです。
Coqでは、プログラムと証明が単一の言語で結び付いているので、無限ループですべての定理が証明できることになってしまいます。

(*
Nonetheless, the basic insight of HOAS is a very useful one, and there are ways to realize most benefits of HOAS in Coq.  We will study a particular technique of this kind in the final chapter, on programming language syntax and semantics. 
*)
それでもHOASに関する基本的な洞察はきわめて有用であり、CoqでHOASの利点のほとんどを実現する方法もあります。
最終章では、そのような具体的な技法について、プログラミング言語の構文と意味を研究することにします。
*)

(**
(*
* An Interlude on Induction Principles
*)
* 帰納法の原理についての補足
*)

(**
(*
As we have emphasized a few times already, Coq proofs are actually programs, written in the same language we have been using in our examples all along.  We can get a first sense of what this means by taking a look at the definitions of some of the %\index{induction principles}%induction principles we have used.  A close look at the details here will help us construct induction principles manually, which we will see is necessary for some more advanced inductive definitions.
*)
なんどか強調したように、Coqの証明はこれまでの例題で使ってきた言語と同じ言語で書かれており、実のところプログラムです。
その意味をしっかりと把握できるように、これまでに使用した%\index{きのうほうのげんり@帰納法の原理}%帰納法の原理をここで確認しておきましょう。
帰納的定義の応用例では、帰納法の原理を自分の手で構成することが必要になる場合もあります。
これまでに使った帰納法の原理をここでしっかり確認しておけば、自分の手で帰納法の原理の構成が必要になるときに役立ちます。
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
上記に示した帰納法の原理は、さらに一般的な帰納法の原理である[nat_rect]を用いて定義されていることがわかります。
[nat_rect]という原理の名前に出てくる<<rect>>は、先頭の<<rec>>は「再帰（recursion）原理」であることを、末尾の<<t>>は[Type]を表しています。
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
[nat_rect]という原理によって与えられるのは、[nat -> Type]型の[P]であり、[nat -> Prop]型ではありません。
[Type]は、[Set]や[Prop]と同じく、一つの領域です。(* universe の訳語は「領域」でよいか-nobsun *)
実際には、[Set]と[Prop]の両者の上位型になっています。(* supertype の訳語は「上位型」でよいか-nobsun *)
領域が別であることにどんな意味があるのか、正確なところは後で説明します。
今のところ重要なのは、[Type]は[Set]か[Prop]のどちらにもなりうるメタ領域のようなものとして使えるということです。
[nat]用に自動生成された別の帰納法の原理の定義を表示してみれば、部分型付けの関係になっていることに伴う対称性を確認できます。
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
これは、[Prop]を[Set]に置き換えれば[nat_ind]の定義と同じです。
さらに、ほとんどの帰納型[T]に対し、[T_ind]という帰納法の原理だけでなく、[T_rec]という%\index{さいきのげんり@再帰の原理}%再帰の原理も手に入ります。
[T_rec]を使えば、[Fixpoint]を明示しなくても再帰的な定義を書けます。
たとえば、以下の二つの定義は同じです。
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
さらに不思議の国の奥へと降りていきましょう。
[nat_rect]自身はプリミティブでさえありません。
自分の手で書くこともできる関数プログラムです。
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
ここで新しく登場したのは、%\index{Gallinaこう@Gallina項!fix}%[fix]というGallinaのキーワードを使った無名再帰関数（[fix]は[fun]と同じく再帰に対応しています）と、[match]式に対する注釈です。
このような[match]を_[依存型付きパターンマッチ]_と呼びます。%\index{dependent pattern matching}%
なぜかというと、この式の_[型]_は、マッチする_[値]_に依存するからです。
のちほど、特に第II部で、もっと複雑な例が登場します。

(*
%\index{type inference}%Type inference for dependent pattern matching is undecidable, which can be proved by reduction from %\index{higher-order unification}%higher-order unification%~\cite{HOU}%.  Thus, we often find ourselves needing to annotate our programs in a way that explains dependencies to the type checker.  In the example of [nat_rect], we have an %\index{Gallina terms!as}%[as] clause, which binds a name for the discriminee; and a %\index{Gallina terms!return}%[return] clause, which gives a way to compute the [match] result type as a function of the discriminee.
*)
%\index{かたすいろん@型推論}%依存型付きパターンマッチに対する型推論は、非決定的です。
このことは、%\index{こうかいたんいつか@高階単一化}%高階単一化からの簡約により証明できます%~\cite{HOU}%。
型推論が非決定的なので、プログラムに手で注釈を付けることにより型検査器に依存関係を伝えなければならないことがよくあります。
[nat_rect]の例では、
[as]節により識別対象の名前を束縛し%\index{Gallinaこう@Gallina項!as}%、
[return]節により[match]の結果の型を計算する手段を識別対象の関数として指定しています%\index{Gallinaこう@Gallina項!return}%。

(*
To prove that [nat_rect] is nothing special, we can reimplement it manually.
*)
[nat_rect]が特別なものでないことは、手で再実装してみれば証明できます。
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
[nat_rect]の定義をさらによく理解できるように、[nat_ind]をセクションで再実装してみましょう。
*)

Section nat_ind'.
   (**
   (*
   First, we have the property of natural numbers that we aim to prove.
   *)
   まずは証明したい自然数の性質を用意します。
   *)

  Variable P : nat -> Prop.

   (**
   (*
   Then we require a proof of the [O] case, which we declare with the command %\index{Vernacular commands!Hypothesis}%[Hypothesis], which is a synonym for [Variable] that, by convention, is used for variables whose types are propositions.
   *)
   まず必要なのは[O]の場合の証明です。これは%\index{Vernacularこまんど@Vernacularコマンド!Hypothesis}%[Hypothesis]コマンドで宣言します。
   このコマンドは[Variable]のシノニムで、規約により、型が命題である変数に対して使うことになっています。
   *)

  Hypothesis O_case : P O.

   (**
   (*
   Next is a proof of the [S] case, which may assume an inductive hypothesis.
   *)
   次は[S]の場合の証明です。
   この場合には帰納法の仮説が使えるでしょう。
   *)

  Hypothesis S_case : forall n : nat, P n -> P (S n).

   (**
   (*
   Finally, we define a recursive function to tie the pieces together.
   *)
   最後に、これらのピースをつなぐ再帰関数を定義します。
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
セクションを閉じると、[nat_ind']に対する、[fun]で束縛された新しい引数として、[Variable]と[Hypothesis]が追加されます。
[Type]の代りに[Prop]を使っている点を除くと、最終的には[nat_rect]のために自動生成された定義とまったく同じものになります。

%\medskip%

(*
We can also examine the definition of [even_list_mut], which we generated with [Scheme] for a mutually recursive type.
*)
相互再帰型では[even_list_mut]という帰納法の原理を使いました。
そのときは、[Scheme]を使って[even_list_mut]を生成しました。
この原理についても定義を詳しく調べることが可能です。
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
相互再帰する[fix]では、%\index{Gallinaこう@Gallina項!with}%[with]で区切ることで別々の関数を使っています。
ちょうど、MLにおいて<<and>>で区切るのと同じ要領です。
相互再帰する関数のいずれが[fix]式の最終的な値になるべきかは、最後の%\index{Gallinaこう@Gallina項!for}%[for]節で識別されます。
この定義をテンプレートにすることで、以下のように[even_list_mut]を直接定義できます。
*)

Section even_list_mut'.
  (**
  (*
  First, we need the properties that we are proving.
  *)
  まず、これから証明する性質が必要です。
  *)

  Variable Peven : even_list -> Prop.
  Variable Podd : odd_list -> Prop.

  (**
  (*
  Next, we need proofs of the three cases.
  *)
  次に、三つの場合分けのそれぞれに対する証明が必要です。
  *)
  
  Hypothesis ENil_case : Peven ENil.
  Hypothesis ECons_case : forall (n : nat) (o : odd_list), Podd o -> Peven (ECons n o).
  Hypothesis OCons_case : forall (n : nat) (e : even_list), Peven e -> Podd (OCons n e).

  (**
  (*
  Finally, we define the recursive functions.
  *)
  最後に再帰関数を定義します。
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
反射的型についても簡単に帰納法の原理を直接実装できます。
前に見た[formula]型に対しては、上記とほとんど同じ要領で再帰的な定義が使えます。
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
帰納法の原理を実装するのは、どちらかというと退屈であり、それほど創造的ではありません。
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
すでに定義した二分木の型を拡張し、任意の数の分岐がある多分木の型を定義したいとします。
単純な定義は、以下のようにリストを使うものでしょう。
*)

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.

(**
(*
This is an example of a%\index{nested inductive type}% _nested_ inductive type definition, because we use the type we are defining as an argument to a parameterized type family.  Coq will not allow all such definitions; it effectively pretends that we are defining [nat_tree] mutually with a version of [list] specialized to [nat_tree], checking that the resulting expanded definition satisfies the usual rules.  For instance, if we replaced [list] with a type family that used its parameter as a function argument, then the definition would be rejected as violating the positivity restriction.
*)
この定義では、定義しようとする型を、パラメタ化された型族への引数として使っています。
そのため、_[ネストした]_帰納型%\index{ねすとしたきのうがた@ネストした帰納型}%の定義の例になっています。
このような定義は、一般にはCoqは許してくれません。
Coqはこの定義を、[nat_tree]を適用した[list]を使って相互参照的に[nat_tree]を定義しているとみなし、定義が展開された結果が通常の規則を満すかどうかを確認します。
(*  いけぶち：型パラメータへの代入をspecializeと言うけど、「特定化」と言って通じるのかよく分からなかったので「適用」にしてみた *)
たとえば、この定義の[list]を置き換えて、パラメータを関数引数として使うような型族にすれば、陽性要件に違反する定義であるとして拒絶されるでしょう。

(*
As we encountered with mutual inductive types, we find that the automatically generated induction principle for [nat_tree] is too weak.
*)
相互帰納型の例で見たように、[nat_tree]に対して自動生成される帰納法の原理は弱すぎるのです。
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
改良版の原理を実装してくれる[Scheme]のようなコマンドはありません。
異なる型族をネストして使う、うまい方法を見つけるには、通常は独創性が必要です。
すでに相互帰納法の原理を自分で実装する方法は説明したので、ここでそれを応用してみましょう。

(*
Many induction principles for types with nested uses of [list] could benefit from a unified predicate capturing the idea that some property holds of every element in a list.  By defining this generic predicate once, we facilitate reuse of library theorems about it.  (Here, we are actually duplicating the standard library's [Forall] predicate, with a different implementation, for didactic purposes.)
*)
ある性質がリストの各要素について満たされることを単一の述語で表せると、[list]をネストして使っている型に対する帰納法の原理で便利に使える場合がよくあります。
そうした汎用の述語は、一度だけ定義すれば、その述語に関するライブラリの定理として再利用できます
（ここでは、標準ライブラリの[Forall]という述語を説明のために改めて再実装しています）。
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
これから[True]および[/\]を自分たちで証明していきたいので、まずはそれらの定義を見返しておきましょう。
*)

Print True.
(** %\vspace{-.15in}%[[
  Inductive True : Prop :=  I : True
  ]]

(*
That is, [True] is a proposition with exactly one proof, [I], which we may always supply trivially.
*)
要するに、[True]は[I]という証明を1つだけ持つ命題です。この証明[I]は常に自明に成り立ちます。

(*
Finding the definition of [/\] takes a little more work.  Coq supports user registration of arbitrary parsing rules, and it is such a rule that is letting us write [/\] instead of an application of some inductive type family.  We can find the underlying inductive type with the %\index{Vernacular commands!Locate}%[Locate] command, whose argument may be a parsing token.%\index{Gallina terms!and}%
*)
[/\]の定義については、もう少し考えることがあります。
帰納的な型族を適用する代わりに[/\]と書けるのは、Coqでは利用者が任意の構文解析の規則を登録できるようになっており、[/\]のための規則が登録されているからです。
[/\]の背景にある帰納型を調べるには、構文解析トークンを引数に取る%\index{Vernacularこまんど@Vernacularコマンド!Locate}%[Locate]コマンドを使います。
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
[and]の定義を[Print]コマンドで表示すると、定義の下に%\index{あんもくのひきすう@暗黙の引数}%暗黙の引数（implicit argument）に関する情報も得られます（それ以外の情報も表示されますが上記では省略しています）。
暗黙の引数に関するこの情報からは、
連言肢の証明に対して構成子[conj]を呼び出すことで連言の証明が構成され、その際に連言肢の証明の型を明示的な引数として含める必要はない、ということがわかります。

%\medskip%

(*
Now we create a section for our induction principle, following the same basic plan as in the previous section of this chapter.
*)
帰納法の原理のセクションを作り、前節の例と同じ基本的な方針で進めましょう。
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
  帰納法の原理そのものを書き出すにあたり、まずは「ネストした帰納型の定義は相互帰納の定義に展開される」という直観に従ってみます。

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
  この定義は、以下のメッセージにより、Coqから拒絶されます。

<<
  Recursive call to nat_tree_ind' has principal argument equal to "tr"
  instead of rest.
>>

  (*
  There is no deep theoretical reason why this program should be rejected; Coq applies incomplete termination-checking heuristics, and it is necessary to learn a few of the most important rules.  The term "nested inductive type" hints at the solution to this particular problem.  Just as mutually inductive types require mutually recursive induction principles, nested types require nested recursion.
  *)
  このプログラムが拒絶されることに理論上の深淵な理由はありません。
  停止性判定のヒューリスティクスをCoqが不完全に適用しただけなので、特に重要な規則をいくつかCoqに学ばせる必要があります。(* ここ意味がよくわからない -kshikano *)
  この問題に対するヒントになるのは、「ネストした帰納的型」という言い方です。
  相互帰納型では、相互再帰した帰納法の原理が必要でした。ネストした型には、ネストした再帰が必要です。
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
  
  この定義では、[list_nat_tree_ind]を無名[fix]として使っており、これは再帰関数の定義の中で文字どおり_[ネスト]_しています。
  この再帰関数に、[list]をネストさせて使っていた帰納的な定義が対応します。
  *)

End nat_tree_ind'.

(**
(*
We can try our induction principle out by defining some recursive functions on [nat_tree] and proving a theorem about them.  First, we define some helper functions that operate on lists.
*)

この帰納法の原理を使ってみましょう。
[nat_tree]上の再帰関数を定義し、それらに関する定理を証明してみます。
まず、リストを操作する補助関数をいくつか定義します。
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
これで木のサイズを測る関数を定義できます。
*)

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NNode' _ trs => S (sum (map ntsize trs))
  end.

(**
(*
Notice that Coq was smart enough to expand the definition of [map] to verify that we are using proper nested recursion, even through a use of a higher-order function.
*)
高階関数を使っていますが、Coqは賢いので、ネストした再帰が適切に使われていることを検証するために[map]の定義を展開してくれます。(* この原稿をCoqにかけると、この本文がある時点では展開済みなので、原文は過去形になっているけど、読みにくいので平叙文で -kshikano *)
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
上記では、任意個の分岐を持つ木の接合（splice）を、二分木のときの[nsplice]と同様に定義しています。
この[ntsplice]についても、木のサイズとの関係について同様の定理が証明できます。
まずは加法に関する便利な補題を用意します。
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
この補題[plus_S]をヒントとして追加することで、定理の証明を開始します。
*)

Hint Rewrite plus_S.

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2)
  = plus (ntsize tr2) (ntsize tr1).
(* begin thide *)
  (**
  (*
  We know that the standard induction principle is insufficient for the task, so we need to provide a %\index{tactics!using}%[using] clause for the [induction] tactic to specify our alternate principle.
  *)
  標準の帰納法の原理では力不足なので、%\index{たくてぃっく@タクティク!using}%[induction]タクティクで[using]節を使って代替の原理を指定します。
  *)

  induction tr1 using nat_tree_ind'; crush.

  (**
  (*
  One subgoal remains: [[
  *)
  サブゴールが一つ残っています。 [[
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
     このゴールをしばらくじっと見ていると、[ls]の構造に関する場合分けが必要なことが見えてきます。
     あとはいつもと同じです。
  *)

  destruct ls; crush.

  (**
  (*
  We can go further in automating the proof by exploiting the hint mechanism.%\index{Vernacular commands!Hint Extern}%
  *)
  ヒントの仕組みをうまく使うことで、この証明をさらに自動化できます。%\index{Vernacularこまんど@Vernacularコマンド!Hint Extern}%
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
ヒントについては後の章で詳しく説明します。
ここで重要なのは、ヒントを使うことで、証明の途中で遭遇が予想される結論を記述するパターンが登録できるという点だけです。
このパターンには、単一化変数を含めてもかまいません。
その場合は、変数名の先頭に疑問符がつきます。
それらの束縛変数は、パターンにマッチしたときに実行させるタクティクの中で参照できます。

(*
The advantage of using the hint is not very clear here, because the original proof was so short.  However, the hint has fundamentally improved the readability of our proof.  Before, the proof referred to the local variable [ls], which has an automatically generated name.  To a human reading the proof script without stepping through it interactively, it was not clear where [ls] came from.  The hint explains to the reader the process for choosing which variables to case analyze, and the hint can continue working even if the rest of the proof structure changes significantly.
*)
この例では、証明がとても短いので、ヒントを使う利点はあまりありません。
それでも、ヒントによって証明の読みやすさは大きく改善しました。
ヒントを使う前は、証明でローカル変数[ls]が参照されていますが、この[ls]は自動生成された名前でした。
対話的に実行せずに証明スクリプトだけを読む人にとっては、[ls]がどこから来たのか明確ではありません。
ヒントは、証明を読む人に対し、場合分けにおいて選択する変数を説明してくれます。
なお、ヒントは、それ以外の証明の構造を大幅に変更しても正しく機能します。
*)


(**
(*
* Manual Proofs About Constructors
*)
* 構成子に関する手動の証明
*)

(**
(*
It can be useful to understand how tactics like %\index{tactics!discriminate}%[discriminate] and %\index{tactics!injection}%[injection] work, so it is worth stepping through a manual proof of each kind.  We will start with a proof fit for [discriminate].
*)
%\index{たくてぃく@タクティク!discriminate}%[discriminate]や%\index{たくてぃく@タクティク!injection}%[injection]のようなタクティクがどのように機能するかを理解するために、これらのタクティクの仕事を手で追って証明してみましょう。
まずは[discriminate]です。
*)

Theorem true_neq_false : true <> false.

(* begin thide *)
(**
(*
We begin with the tactic %\index{tactics!red}%[red], which is short for "one step of reduction," to unfold the definition of logical negation.
*)
論理否定の定義を展開するために、[red]タクティクから始めます。
このタクティクの名前は「1ステップの簡約（one step of reduction）」からきています。
*)

  red.
(** %\vspace{-.15in}%[[
  ============================
   true = false -> False
]]

(*
The negation is replaced with an implication of falsehood.  We use the tactic %\index{tactics!intro}%[intro H] to change the assumption of the implication into a hypothesis named [H].
*)
否定は、偽の含意で置き換えられます。
%\index{たくてぃくす@タクティクス!intro}%[intro H]というタクティクを使って、含意の仮定を[H]という名前の仮説にします。
*)
  
  intro H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   False
]]

(*
This is the point in the proof where we apply some creativity.  We define a function whose utility will become clear soon.
*)
ここで少し独創性が必要になります。
関数を一つ定義しましょう。
なぜこの関数を定義するかは、すぐにわかります。
*)

  Definition toProp (b : bool) := if b then True else False.

(**
(*
It is worth recalling the difference between the lowercase and uppercase versions of truth and falsehood: [True] and [False] are logical propositions, while [true] and [false] are Boolean values that we can case-analyze.  We have defined [toProp] such that our conclusion of [False] is computationally equivalent to [toProp false].  Thus, the %\index{tactics!change}%[change] tactic will let us change the conclusion to [toProp false].  The general form [change e] replaces the conclusion with [e], whenever Coq's built-in computation rules suffice to establish the equivalence of [e] with the original conclusion.
*)
先頭が小文字か大文字かで、真（true）と偽（false）に違いがあったことを思い出してください。
[True]と[False]は論理命題であり、[true]と[false]は場合分けが可能な論理値です。
[toProp]は、[False]の結論が[toProp false]と同等になるように定義しました。
したがって、%\index{たくてぃくす@タクティクス!change}%[change]タクティクにより、[False]の結論を[toProp false]に置き換え可能です。
一般に[change e]という形式は、結論が[e]と同等であることがCoqに組み込まれている計算規則により証明できるときは、常に元の結論を[e]に置き換えてくれます。
*)

  change (toProp false).
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp false
]]

(*
Now the righthand side of [H]'s equality appears in the conclusion, so we can rewrite, using the notation [<-] to request to replace the righthand side of the equality with the lefthand side.%\index{tactics!rewrite}%
*)
[H]の等式の右辺が結論に現れたので、等式の右辺を左辺に置き換えるように、[<-]記法を使って書き換えられます。
*)

  
  rewrite <- H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp true
]]

(*
We are almost done.  Just how close we are to done is revealed by computational simplification.
*)
これでほぼおしまいです。
計算で単純化すれば、ほとんど完了していることがわかります。
*)
  
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

(**
(*
I have no trivial automated version of this proof to suggest, beyond using [discriminate] or [congruence] in the first place.
*)
この証明の自動化をしてくれるのが、[discriminate]や[congruence]というわけです。

%\medskip%

(*
We can perform a similar manual proof of injectivity of the constructor [S].  I leave a walk-through of the details to curious readers who want to run the proof script interactively.
*)
構成子[S]の単射性の証明も同じように手動で実行できます。
詳細は、証明スクリプトを対話的に実行してみたい熱心な読者に残しておきます。
*)

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.
(* end thide *)

(**
(*
The key piece of creativity in this theorem comes in the use of the natural number predecessor function [pred].  Embodied in the implementation of [injection] is a generic recipe for writing such type-specific functions.
*)
この定理で鍵となるのは、自然数の前者関数[pred]の使い方です。
[injection]の実装には、このような型に固有の関数を書くときの一般的なレシピが具現化されているのです。

(*
The examples in this section illustrate an important aspect of the design philosophy behind Coq.  We could certainly design a Gallina replacement that built in rules for constructor discrimination and injectivity, but a simpler alternative is to include a few carefully chosen rules that enable the desired reasoning patterns and many others.  A key benefit of this philosophy is that the complexity of proof checking is minimized, which bolsters our confidence that proved theorems are really true.
*)
本節で紹介した例からは、Coqの背景にある設計思想の重要な側面が見えてきます。
構成子の区別と単射性に関する規則を組み込み、Gallinaの代替を設計することは可能ですが、
むしろ、必要な論証パターンなどが可能になるように選び抜いた規則を含めておくほうが選択肢として単純です。
Coqの設計思想の利点は、証明の確認にかかる複雑さが最小限に抑えられていることで、証明された定理が本当に正しいという確信を強く持てることです。
*)

(* Copyright (c) 2008-2012, 2015, Adam Chlipala
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)


(** %\chapter{いくつかの手短かな例}% *)

(**
(** I will start off by jumping right in to a fully worked set of examples, building certified compilers from increasingly complicated source languages to stack machines.  We will meet a few useful tactics and see how they can be used in manual proofs, and we will also see how easily these proofs can be automated instead.  This chapter is not meant to give full explanations of the features that are employed.  Rather, it is meant more as an advertisement of what is possible.  Later chapters will introduce all of the concepts in bottom-up fashion.  In other words, it is expected that most readers will not understand what exactly is going on here, but I hope this demo will whet your appetite for the remaining chapters!

As always, you can step through the source file <<StackMachine.v>> for this chapter interactively in Proof General.  Alternatively, to get a feel for the whole lifecycle of creating a Coq development, you can enter the pieces of source code in this chapter in a new <<.v>> file in an Emacs buffer.  If you do the latter, include these three lines at the start of the file. *)
*)
(**
まずは実際に動く例として、ソース言語からスタックマシンを生成する証明付きコンパイラの構成から始めましょう。単純なソース言語をコンパイルできる状態から始めて、少しずつ複雑なソース言語に対応できるようにしていきます。証明に関しては、便利なタクティクをいくつか紹介し、それらが手動の証明でどう使えるかを見ます。さらに、どれくらい簡単に自動化できるかも見ます。本章では利用する機能の完全な説明を与えるつもりはありません。むしろ本章の狙いは、Coqで何ができるのかを見てもらうことです。後の章ですべての概念をボトムアップに紹介していきます。言い換えれば、ほとんどの読者にとって本章の内容を完璧に理解するのは難しいかもしれません。ここで紹介するデモが残りの章への興味に繋がればそれで十分です！

本章についても、Proof Generalを使うことで、ソースファイルである<<StackMachine.v>>を対話的に1ステップずつ実行していけます。Coqによる開発の工程を肌で感じたければ、本章に出てくるソースコードをEmacsバッファ内で新規の<<.v>>ファイルに1つずつ書き込んでいってもよいでしょう。後者の方法を取るなら、ファイルの先頭に以下の三行をコピーしてください。
*)

Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* begin hide *)
(* begin thide *)
Definition bleh := app_assoc.
(* end thide *)
(* end hide *)

(**
(** In general, similar commands will be hidden in the book rendering of each chapter's source code, so you will need to insert them in from-scratch replayings of the code that is presented.  To be more specific, every chapter begins with the above three lines, with the import list tweaked as appropriate, considering which definitions the chapter uses.  The second command above affects the default behavior of definitions regarding type inference, and the third allows for more concise pattern-matching syntax in Coq versions 8.5 and higher (having no effect in earlier versions). *)
*)
(**
以降、本書では、各章のソースコード内の似通ったコマンドを省略します。省略されている部分については、前を同じものをコピー&ペーストする必要があります。具体的には、どの章も先頭には上記の三行が挿入されています。ただし、[Require Import]の後ろの部分は、章ごとに必要な定義に書き換える必要があります。二行めのコマンドは、型推論に関する定義の標準的なふるまいに影響します。三行めは、より簡潔なパターンマッチングの機能を利用できるようにするためのものです（Coqのバージョン8.5以降のコマンドであり、バージョン8.5未満に対する影響はありません）。*)


(** * 自然数の算術式 *)

(** (* We will begin with that staple of compiler textbooks, arithmetic expressions over a single type of numbers. *)
コンパイラの教科書ではおなじみの、数値型の上での算術式から始めましょう。*)

(** ** ソース言語 *)

(**
(** We begin with the syntax of the source language.%\index{Vernacular commands!Inductive}% *)
*)
(**
ソース言語のシンタックスから始めます。%\index{Vernacular commands!Inductive}% *)

Inductive binop : Set := Plus | Times.

(**
(** Our first line of Coq code should be unsurprising to ML and Haskell programmers.  We define an %\index{algebraic datatypes}%algebraic datatype [binop] to stand for the binary operators of our source language.  There are just two wrinkles compared to ML and Haskell.  First, we use the keyword [Inductive], in place of <<data>>, <<datatype>>, or <<type>>.  This is not just a trivial surface syntax difference; inductive types in Coq are much more expressive than garden variety algebraic datatypes, essentially enabling us to encode all of mathematics, though we begin humbly in this chapter.  Second, there is the %\index{Gallina terms!Set}%[: Set] fragment, which declares that we are defining a datatype that should be thought of as a constituent of programs.  Later, we will see other options for defining datatypes in the universe of proofs or in an infinite hierarchy of universes, encompassing both programs and proofs, that is useful in higher-order constructions. *)
*)
(**
はじめてのCoqコードとなるこの一行は、MLやHaskellのプログラマにとっては意外なものではないでしょう。ソース言語の二項演算子を表すために、[binop]という%\index{代数的データ型}%代数的データ型（algebraic datatype）を定義しています。MLやHaskellと異なる点は二つだけです。一つめは、Coqでは<<data>>や<<datatype>>、<<type>>の代わりに、[Inductive]を使うことです。これは単なる表面的なシンタックスの違いではありません。本章ではあまり威力を発揮しませんが、Coqの帰納的データ型（inductive data types）にはありふれた代数的データ型よりもずっと豊かな表現力があり、とくに数学のすべてを表現できます。二つめは%\index{Gallina terms!Set}%[: Set]の存在です。これは、プログラムの構成要素として考えられるべきデータ型を定義することを宣言するものです。のちほど、証明の世界のデータ型や、プログラムと証明の両方を包含する無限の階層を持った世界のデータ型（高階の構成で役立ちます）といった、他のデータ型を定義するときのキーワードも登場します。*)

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(**
(** Now we define the type of arithmetic expressions.  We write that a constant may be built from one argument, a natural number; and a binary operation may be built from a choice of operator and two operand expressions.

A note for readers following along in the PDF version: %\index{coqdoc}%coqdoc supports pretty-printing of tokens in %\LaTeX{}%#LaTeX# or HTML.  Where you see a right arrow character, the source contains the ASCII text <<->>>.  Other examples of this substitution appearing in this chapter are a double right arrow for <<=>>>, the inverted %`%#'#A' symbol for <<forall>>, and the Cartesian product %`%#'#X' for <<*>>.  When in doubt about the ASCII version of a symbol, you can consult the chapter source code.

%\medskip%

Now we are ready to say what programs in our expression language mean.  We will do this by writing an %\index{interpreters}%interpreter that can be thought of as a trivial operational or denotational semantics.  (If you are not familiar with these semantic techniques, no need to worry: we will stick to "common sense" constructions.)%\index{Vernacular commands!Definition}% *)
*)
(**
次は算術式の型の定義です。定数[Const]は一つの自然数値の引数から作られること、二項演算子[Binop]は一つの演算子と二つのオペランド式から作られることを、それぞれ書き下してあります。

ここで、本書をPDF版で読んでいる読者に注意があります。本書に出てくるCoqのソースコードは、coqdoc%\index{coqdoc}%により、%\LaTeX{}%#LaTeX#やHTML形式に変換されています。PDF上の右矢印「→」は、ソース上ではASCIIテキストの<<->>>です。ほかにも、二重の右矢印「⇒」は<<=>>>に、記号「∀」は<<forall>>に、デカルト積「×」は<<*>>に置き換えが必要です。ASCIIテキストでどう書くのかが分からなくなったら、本書のソースコードを参照してください。

%\medskip%

ソース言語を定義したところで、この言語で表現されるプログラムの意味を与えましょう。ここでは、%\index{インタプリタ}%インタプリタを書くことにより、プログラムの意味を与えます。これはごく単純な操作的意味論と表示的意味論として考えられます（これらの意味論の手法に不慣れでも心配いりません。「常識的」な構成をするという程度の話です）。%\index{Vernacular commands!Definition}% *)

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(**
(** The meaning of a binary operator is a binary function over naturals, defined with pattern-matching notation analogous to the <<case>> and <<match>> of ML and Haskell, and referring to the functions [plus] and [mult] from the Coq standard library.  The keyword [Definition] is Coq's all-purpose notation for binding a term of the programming language to a name, with some associated syntactic sugar, like the notation we see here for defining a function.  That sugar could be expanded to yield this definition:
[[
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
    | Plus => plus
    | Times => mult
  end.
]]

In this example, we could also omit all of the type annotations, arriving at:
[[
Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.
]]

Languages like Haskell and ML have a convenient%\index{principal types}\index{type inference}% _principal types_ property, which gives us strong guarantees about how effective type inference will be.  Unfortunately, Coq's type system is so expressive that any kind of "complete" type inference is impossible, and the task even seems to be hard in practice.  Nonetheless, Coq includes some very helpful heuristics, many of them copying the workings of Haskell and ML type-checkers for programs that fall in simple fragments of Coq's language.

This is as good a time as any to mention the profusion of different languages associated with Coq.  The theoretical foundation of Coq is a formal system called the%\index{Calculus of Inductive Constructions}\index{CIC|see{Calculus of Inductive Constructions}}% _Calculus of Inductive Constructions_ (CIC)%~\cite{CIC}%, which is an extension of the older%\index{Calculus of Constructions}\index{CoC|see{Calculus of Constructions}}% _Calculus of Constructions_ (CoC)%~\cite{CoC}%.  CIC is quite a spartan foundation, which is helpful for proving metatheory but not so helpful for real development.  Still, it is nice to know that it has been proved that CIC enjoys properties like%\index{strong normalization}% _strong normalization_ %\cite{CIC}%, meaning that every program (and, more importantly, every proof term) terminates; and%\index{relative consistency}% _relative consistency_ %\cite{SetsInTypes}% with systems like versions of %\index{Zermelo-Fraenkel set theory}%Zermelo-Fraenkel set theory, which roughly means that you can believe that Coq proofs mean that the corresponding propositions are "really true," if you believe in set theory.

Coq is actually based on an extension of CIC called %\index{Gallina}%Gallina.  The text after the [:=] and before the period in the last code example is a term of Gallina.  Gallina includes several useful features that must be considered as extensions to CIC.  The important metatheorems about CIC have not been extended to the full breadth of the features that go beyond the formalized language, but most Coq users do not seem to lose much sleep over this omission.

Next, there is %\index{Ltac}%Ltac, Coq's domain-specific language for writing proofs and decision procedures. We will see some basic examples of Ltac later in this chapter, and much of this book is devoted to more involved Ltac examples.

Finally, commands like [Inductive] and [Definition] are part of %\index{Vernacular commands}%the Vernacular, which includes all sorts of useful queries and requests to the Coq system.  Every Coq source file is a series of vernacular commands, where many command forms take arguments that are Gallina or Ltac programs.  (Actually, Coq source files are more like _trees_ of vernacular commands, thanks to various nested scoping constructs.)

%\medskip%

We can give a simple definition of the meaning of an expression:%\index{Vernacular commands!Fixpoint}% *)
*)
(**
二項演算子の意味は、自然数の上の二引数関数です。この関数は、MLやHaskellにおける<<match>>や<<case>>のようなパターンマッチングを使って定義し、Coqの標準ライブラリ内の関数[plus]と[mult]を参照しています。[Definition]というキーワードは、Coqの項を名前に束縛する汎用の記法です。さまざまな目的に応じた構文糖衣が用意されており、この例では関数定義のための構文糖衣を使っています。この構文糖衣を展開すると以下のようになります。
[[
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
    | Plus => plus
    | Times => mult
  end.
]]

この例では、次のように、型注釈をすべて外してもかまいません。
[[
Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.
]]

MLやHaskellのような言語には、_[主要型]_%\index{principal types}\index{type inference}%（principal type）を求められるという有用な性質があります。この性質は、型推論の効果に対し、強い保証を与えてくれるものです。残念ながら、Coqの型システムは表現力がとても豊かであるがために、あらゆる意味で「完全」な型推論は不可能であり、実際に主要型を求めることは困難にさえ思えます。とはいえCoqには、そのためのヒューリスティックな仕組みがいくつか含まれています。それらの仕組みの多くは、Coqの単純なコードに落ちるようなプログラムに対するMLやHaskellの型検査器の仕組みから移植されたものです。

いい機会なので、ここでCoqに付随する複数の言語について触れておきましょう。Coqの理論的な基礎は、_[Calculus of Inductive Constructions]_%\index{Calculs of Inductive Constructions}\index{CIC|see{Calculus of Inductive Constructions}}%（CIC）%~\cite{CIC}%と呼ばれる形式システムにあります。そのCICは、それ以前にあった_[Calculus of Constructions]_、%\index{Calculus of Constructions}\index{CoC|see{Calculus of Constructions}}%（CoC）%~\cite{CoC}%という型システムの拡張です。CICは、メタ理論の証明には有用ですが、現場の開発に使うには厳格すぎるシステムです。それでも、CICには%\index{強正規化性}%_[強正規化性]_（strong normalizaiton）や、%\index{Zermelo-Fraenkel集合論}%Zermelo-Fraenkel集合論に類似した系に対する%\index{相対無矛盾性}%_[相対無矛盾性]_（relative consistency）といった性質があると証明されていることは知っておくとよいでしょう。強正規化性とは、すべてのプログラム（さらにはすべての証明項も）が停止するという性質です。相対無矛盾性とは、簡単に言うと、Coqで書かれた証明に対応する数学的命題が「本当に正しい」ことを、集合論を信じるならば信じてよい、という性質です。

Coqは、実際には%\index{Gallina}%Gallinaと呼ばれるCICの拡張に基いています。上記のコードのうち、「[:=]」から「[.]」までの中身は、Gallinaの項です。Gallinaには、CICの拡張として考えるべき有用な特徴が含まれています。形式言語の範囲を越える全機能に至るまでCICに関する重要なメタ定理が拡張されているわけではありませんが、それを気に病んでいるCoqユーザはほとんどいません。

Coqに付随する次の言語は、証明を書いたり手続きを決定したりするためのドメイン固有言語である%\index{Ltac}%Ltacです。本章の後半では、基本的なLtacの例をいくつか紹介します。本書全体では、もっとたくさんのLtacの例を紹介していきます。

最後は、[Inductive]や[Definition]のようなコマンドを含む%\index{Vernacularコマンド}%Vernacularです。Vernacularには、Coqシステムに対するあらゆる種類の有用な要求や命令が含まれます。Coqのソースファイルは、いずれもVernacularコマンドの列であり、それらのコマンドの多くは引数としてGallinaやLtacのプログラムを取ります（ネストされたスコープを持つさまざまな構造の影響で、Coqのソースファイルは実際には列ではなく_[木]_に近い形をしています）。

%\medskip%

式の意味の簡単な定義を与えましょう。%\index{Vernacular commands!Fixpoint}% *)

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(**
(** We declare explicitly that this is a recursive definition, using the keyword [Fixpoint].  The rest should be old hat for functional programmers. *)
*)
(**
これが再帰的な定義であることを、[Fixpoint]キーワードを使って明示的に宣言しています。それ以外の部分は、関数型プログラマにとっては目新しいものではないでしょう。 *)

(**
(** It is convenient to be able to test definitions before starting to prove things about them.  We can verify that our semantics is sensible by evaluating some sample uses, using the command %\index{Vernacular commands!Eval}%[Eval].  This command takes an argument expressing a%\index{reduction strategy}% _reduction strategy_, or an "order of evaluation."  Unlike with ML, which hardcodes an _eager_ reduction strategy, or Haskell, which hardcodes a _lazy_ strategy, in Coq we are free to choose between these and many other orders of evaluation, because all Coq programs terminate.  In fact, Coq silently checked %\index{termination checking}%termination of our [Fixpoint] definition above, using a simple heuristic based on monotonically decreasing size of arguments across recursive calls.  Specifically, recursive calls must be made on arguments that were pulled out of the original recursive argument with [match] expressions.  (In Chapter 7, we will see some ways of getting around this restriction, though simply removing the restriction would leave Coq useless as a theorem proving tool, for reasons we will start to learn about in the next chapter.)

To return to our test evaluations, we run the [Eval] command using the [simpl] evaluation strategy, whose definition is best postponed until we have learned more about Coq's foundations, but which usually gets the job done. *)
*)
(**
これらの定義について何かしら証明を始める前に、定義をテストできると好都合です。これまでに定義したセマンティクスがもっともらしいことを、コマンド%\index{Vernacular commands!Eval}%[Eval]で用例をいくつか評価することにより確かめてみましょう。[Eval]コマンドは、%\index{簡約戦略}%_[簡約戦略]_（reduction strategy）もしくは_[評価順序]_（order of evaluation）と呼ばれるものを表す引数を取ります。_[先行評価]_が前提のMLや、_[遅延評価]_が前提のHaskellとは違い、Coqではさまざまな評価順序を選べます。これが可能なのは、すべてのCoqプログラムが停止するからです。実を言うと、Coqの内部では、上記の[Fixpoint]で定義した関数の%\index{termination checking}%停止性が確認されています。この確認では、再帰が呼び出されるたびに引数のサイズが単調に減少することに基づいた単純なヒューリスティクスにより、停止性を判断しています。この場合には、[match]式によって分割された元の再帰的な引数に対して再帰呼び出しが作られていなければなりません。（この制限を単純に削除すると、Coqは定理証明のための道具として役に立たないものになってしまうでしょう。その理由は次章から学びます。第7章では、[Fixpoint]の制限に対処するためのいくつかの方法を見ます。）

評価を試してみる前に、[simpl]という評価戦略を使って[Eval]コマンドを実行しましょう。[simpl]の定義はCoqの基礎をもっと学んでから示しますが、通常は[simpl]を使えばいいでしょう。 *)

Eval simpl in expDenote (Const 42).
(** [= 42 : nat] *)

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
(** [= 4 : nat] *)

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= 28 : nat] *)

(**
(** %\smallskip{}%Nothing too surprising goes on here, so we are ready to move on to the target language of our compiler. *)
*)
(**
%\smallskip{}%どれも自然な結果です。今度はコンパイラのターゲット言語を定義することにしましょう。 *)


(** ** ターゲット言語 *)

(**
(** We will compile our source programs onto a simple stack machine, whose syntax is: *)
*)
(**
前項で定義したソース言語によるプログラムを、単純なスタックマシンへとコンパイルします。コンパイラのターゲット言語は次のようなシンタックスで与えます。 *)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(**
(** An instruction either pushes a constant onto the stack or pops two arguments, applies a binary operator to them, and pushes the result onto the stack.  A program is a list of instructions, and a stack is a list of natural numbers.

We can give instructions meanings as functions from stacks to optional stacks, where running an instruction results in [None] in case of a stack underflow and results in [Some s'] when the result of execution is the new stack [s'].  %\index{Gallina operators!::}%The infix operator [::] is "list cons" from the Coq standard library.%\index{Gallina terms!option}% *)
*)
(**
[instr]は命令で、スタックの先頭に定数をプッシュする[iConst]か、引数を二つポップして二項演算子に適用したあとで結果をスタックにプッシュする[iBinon]のいずれかです。プログラム（[prog]）は命令（[instr]）のリストであり、スタック（[stack]）は自然数のリストです。

命令には、スタックからスタックのオプション型への関数として意味を与えましょう。命令を実行した結果がスタックアンダーフローに陥る場合は[None]、結果として新たなスタック[s']を得る場合は[Some s']を返すものとします。%\index{Gallina operators!::}%中置演算子「[::]」はリストのconsです。Coqの標準ライブラリで定義されています。%\index{Gallina terms!option}% *)

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

(**
(** With [instrDenote] defined, it is easy to define a function [progDenote], which iterates application of [instrDenote] through a whole program. *)
*)
(**
[instrDenote]が定義できたので、プログラム全体を通して[instrDenote]を繰り返し適用する関数[progDenote]も簡単に定義できます。 *)

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(**
(** With the two programming languages defined, we can turn to the compiler definition. *)
*)
(**
二つのプログラミング言語が定義できたところで、コンパイラの定義に移りましょう。 *)

(** ** 変換 *)

(**
(** Our compiler itself is now unsurprising.  The list concatenation operator %\index{Gallina operators!++}\coqdocnotation{%#<tt>#++#</tt>#%}% comes from the Coq standard library. *)
*)
(**
コンパイラは自然に定義できます。リストの結合には、Coqの標準ライブラリにある%\index{Gallina operators!++}\coqdocnotation{%#<tt>#++#</tt>#%}%を使います。 *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.


(** (* Before we set about proving that this compiler is correct, we can try a few test runs, using our sample programs from earlier. *)
このコンパイラが正しいことを証明する前に、先ほど実行したサンプルプログラムを試しに走らせてみましょう。 *)

Eval simpl in compile (Const 42).
(** [= iConst 42 :: nil : prog] *)

Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
(** [= iConst 2 :: iConst 2 :: iBinop Plus :: nil : prog] *)

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= iConst 7 :: iConst 2 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil : prog] *)

(** (* %\smallskip{}%We can also run our compiled programs and check that they give the right results. *)
%\smallskip{}%コンパイルされたプログラムを実行して正しい結果を返すことも確かめてみます。 *)

Eval simpl in progDenote (compile (Const 42)) nil.
(** [= Some (42 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
(** [= Some (4 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2))
  (Const 7))) nil.
(** [= Some (28 :: nil) : option stack] *)

(** (* %\smallskip{}%So far so good, but how can we be sure the compiler operates correctly for _all_ input programs? *)
%\smallskip{}%今のところうまくいっています。でも、どうすれば_[すべて]_の入力プログラムに対してコンパイラが正しく動作することを確かめられるでしょうか。 *)

(** ** 変換の正しさ *)

(**
(** We are ready to prove that our compiler is implemented correctly.  We can use a new vernacular command [Theorem] to start a correctness proof, in terms of the semantics we defined earlier:%\index{Vernacular commands!Theorem}% *)
*)
(**
コンパイラが正しく実装されたことを証明しましょう。先ほど定義したセマンティクスの観点から証明を始めるために、[Theorem]という新たなVernacularコマンドを使います。%\index{Vernacular commands!Theorem}% *)

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
(* begin thide *)

(**
(** Though a pencil-and-paper proof might clock out at this point, writing "by a routine induction on [e]," it turns out not to make sense to attack this proof directly.  We need to use the standard trick of%\index{strengthening the induction hypothesis}% _strengthening the induction hypothesis_.  We do that by proving an auxiliary lemma, using the command [Lemma] that is a synonym for [Theorem], conventionally used for less important theorems that appear in the proofs of primary theorems.%\index{Vernacular commands!Lemma}% *)
*)
(**
紙と鉛筆による証明なら、ここで「[e]に関する帰納法より」と書いて終了できるかもしれませんが、この証明に直接取り組むのは実は懸命ではありません。ここでは、基本的な手法である%\index{帰納法の仮定の強化}%_[帰納法の仮定の強化]_が必要になります。そのために[Lemma]コマンドを使って補題を示しましょう。[Lemma]コマンドは[Theorem]のシノニムで、慣習的に主定理の証明に必要となる補助的な定理に対して使います。%\index{Vernacular commands!Lemma}% *)

Abort.

Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

(**
(** After the period in the [Lemma] command, we are in%\index{interactive proof-editing mode}% _the interactive proof-editing mode_.  We find ourselves staring at this ominous screen of text:

[[
1 subgoal

 ============================
  forall (e : exp) (p : list instr) (s : stack),
   progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)

]]

Coq seems to be restating the lemma for us.  What we are seeing is a limited case of a more general protocol for describing where we are in a proof.  We are told that we have a single subgoal.  In general, during a proof, we can have many pending %\index{subgoals}%subgoals, each of which is a logical proposition to prove.  Subgoals can be proved in any order, but it usually works best to prove them in the order that Coq chooses.

Next in the output, we see our single subgoal described in full detail.  There is a double-dashed line, above which would be our free variables and %\index{hypotheses}%hypotheses, if we had any.  Below the line is the %\index{conclusion}%conclusion, which, in general, is to be proved from the hypotheses.

We manipulate the proof state by running commands called%\index{tactics}% _tactics_.  Let us start out by running one of the most important tactics:%\index{tactics!induction}%
*)
*)
(**
[Lemma]コマンドのピリオドを読み込むと、%\index{対話的証明モード}%_[対話的証明モード]_（interactive proof-editing mode）に入ります。スクリーンに何やら新しいテキストが表示されるのが見えるでしょう。

[[
1 subgoal

 ============================
  forall (e : exp) (p : list instr) (s : stack),
   progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)

]]

Coqが補題を再掲してくれたように見えます。これは、私たちが証明のどこにいるのかを示す一般的なやり方で、今はその特別な場合です。一行めの表示は、サブゴールが一つある、と読めます。一般に、証明の途中には証明すべき論理命題がいくつも出てきます。それら未証明の部分的な論理命題が、%\index{サブゴール}%サブゴールです。複数のサブゴールはどんな順番で証明してもかまいませんが、通常はCoqが提示してくれた順番で証明するのがよいでしょう。

上記の出力では、その下に一つのサブゴールの詳細が完全に示されています。二重線の上側には、自由変数や%\index{仮定}%仮定が（もしあれば）示されます。二重線の下側は%\index{結論}%結論で、一般には仮定を使って証明されるべきものが示されます。

証明の状態は、%\index{タクティク}%_[タクティク]_と呼ばれるコマンドを実行することで操作します。もっとも重要なタクティクの一つである%\index{tactics!induction}%[induction]から始めましょう。
*)

  induction e.

(**
(** We declare that this proof will proceed by induction on the structure of the expression [e].  This swaps out our initial subgoal for two new subgoals, one for each case of the inductive proof:

[[
2 subgoals

 n : nat
 ============================
 forall (s : stack) (p : list instr),
   progDenote (compile (Const n) ++ p) s =
   progDenote p (expDenote (Const n) :: s)

subgoal 2 is

  forall (s : stack) (p : list instr),
    progDenote (compile (Binop b e1 e2) ++ p) s =
    progDenote p (expDenote (Binop b e1 e2) :: s)

]]

The first and current subgoal is displayed with the double-dashed line below free variables and hypotheses, while later subgoals are only summarized with their conclusions.  We see an example of a %\index{free variable}%free variable in the first subgoal; [n] is a free variable of type [nat].  The conclusion is the original theorem statement where [e] has been replaced by [Const n].  In a similar manner, the second case has [e] replaced by a generalized invocation of the [Binop] expression constructor.  We can see that proving both cases corresponds to a standard proof by %\index{structural induction}%structural induction.

We begin the first case with another very common tactic.%\index{tactics!intros}%
*)
*)
(**
この証明を式[e]の構造に対する帰納法によって進める、と宣言しています。これにより、元のサブゴールが、帰納法による証明の場合分けに対応する二つの新しいサブゴールに変わります。

[[
2 subgoals

 n : nat
 ============================
 forall (s : stack) (p : list instr),
   progDenote (compile (Const n) ++ p) s =
   progDenote p (expDenote (Const n) :: s)

subgoal 2 is

  forall (s : stack) (p : list instr),
    progDenote (compile (Binop b e1 e2) ++ p) s =
    progDenote p (expDenote (Binop b e1 e2) :: s)

]]

一つめのサブゴール（現在のサブゴールでもあります）には、二重線とその上の自由変数や仮定が表示されますが、それ以降のサブゴールには結論だけが表示されます。一つめのサブゴールには%\index{自由変数}%自由変数がありますね。[nat]型の自由変数[n]です。このサブゴールの結論は、元の定理の主張で[e]が[Const n]に置き換えられてものです。同様に、二つめのサブゴールの[e]は、コンストラクタ[Binop]の一般的な形に置き換えられています。場合分けの両方のサブゴールの証明が、%\index{構造的帰納法}%構造的帰納法による標準的な証明に対応していることがわかります。

前に使った[induction]とはまた別の、やはりよく利用する[intros]というタクティクを使って、一つめのサブゴールを証明するところから始めましょう。%\index{tactics!intros}% *)

  intros.

(**
(** The current subgoal changes to:
[[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote (compile (Const n) ++ p) s =
 progDenote p (expDenote (Const n) :: s)

]]

We see that [intros] changes [forall]-bound variables at the beginning of a goal into free variables.

To progress further, we need to use the definitions of some of the functions appearing in the goal.  The [unfold] tactic replaces an identifier with its definition.%\index{tactics!unfold}%
*)
*)
(**
サブゴールは次のように変わります。
[[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote (compile (Const n) ++ p) s =
 progDenote p (expDenote (Const n) :: s)

]]

[intros]により、先頭にあった[forall]で束縛された変数が自由変数に変わりました。

さらに証明を進めるためには、ゴール内にあるいくつかの関数の定義を使う必要があります。[unfold]タクティクを使うと、識別子がその定義に置き換わります。%\index{tactics!unfold}%
*)

  unfold compile.
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((iConst n :: nil) ++ p) s =
 progDenote p (expDenote (Const n) :: s)

]]
*)

  unfold expDenote.
(**
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((iConst n :: nil) ++ p) s = progDenote p (n :: s)

]]

We only need to unfold the first occurrence of [progDenote] to prove the goal.  An [at] clause used with [unfold] specifies a particular occurrence of an identifier to unfold, where we count occurrences from left to right.%\index{tactics!unfold}% *)
*)
(**
[[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((iConst n :: nil) ++ p) s = progDenote p (n :: s)

]]

ゴールを証明するのに展開が必要なのは、一つめの[progDenote]だけです。[unfold]と一緒に[at]節を使うことで、展開したい特定の識別子の出現場所を指定できます。出現場所は左から右に数えます。%\index{tactics!unfold}% *)

  unfold progDenote at 1.
(**
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
  (fix progDenote (p0 : prog) (s0 : stack) {struct p0} :
    option stack :=
      match p0 with
      | nil => Some s0
      | i :: p' =>
          match instrDenote i s0 with
          | Some s' => progDenote p' s'
          | None => None (A:=stack)
          end
      end) ((iConst n :: nil) ++ p) s =
   progDenote p (n :: s)

]]

This last [unfold] has left us with an anonymous recursive definition of [progDenote] (similarly to how [fun] or "lambda" constructs in general allow anonymous non-recursive functions), which will generally happen when unfolding recursive definitions.  Note that Coq has automatically renamed the [fix] arguments [p] and [s] to [p0] and [s0], to avoid clashes with our local free variables.  There is also a subterm [None (A:=stack)], which has an annotation specifying that the type of the term ought to be [option stack].  This is phrased as an explicit instantiation of a named type parameter [A] from the definition of [option].

Fortunately, in this case, we can eliminate the complications of anonymous recursion right away, since the structure of the argument ([iConst n :: nil) ++ p] is known, allowing us to simplify the internal pattern match with the [simpl] tactic, which applies the same reduction strategy that we used earlier with [Eval] (and whose details we still postpone).%\index{tactics!simpl}%
*)
*)
(**
[[
 n : nat
 s : stack
 p : list instr
 ============================
  (fix progDenote (p0 : prog) (s0 : stack) {struct p0} :
    option stack :=
      match p0 with
      | nil => Some s0
      | i :: p' =>
          match instrDenote i s0 with
          | Some s' => progDenote p' s'
          | None => None (A:=stack)
          end
      end) ((iConst n :: nil) ++ p) s =
   progDenote p (n :: s)

]]

この[unfold]により、[progDenote]が無名の再帰関数に変わります（一般に[fun]や「lambda」で再帰しない無名関数が得られるのに似ています）。再帰的な定義を展開すると、通常はこのようなことが起こります。ここで、Coqが引数[p]と[s]を、それぞれ[p0]および[s0]へと自動的に変えたことに注意してください。これは、局所的な自由変数と名前の衝突を避けるためです。[None (A:=stack)]という部分項もありますね。この項には、この項が[option stack]型を持つということを指示する注釈が含まれています。このことを、「名前付きの型変数[A]を[option]の定義から明示的に具体化する」と表現します。

幸いなことに、今の例ではこの複雑な無名の再帰関数をすぐに取り除けます。これは、引数である[(iConst n :: nil) ++ p]の構造が、[simpl]タクティクを使って内部のパターンマッチを簡約することで明らかになるからです。[simpl]タクティクは、先ほど[Eval]で使ったのと同じ簡約戦略を適用します（詳細については今はまだ触れません）。%\index{tactics!simpl}%
*)

  simpl.
(**
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 (fix progDenote (p0 : prog) (s0 : stack) {struct p0} :
  option stack :=
    match p0 with
    | nil => Some s0
    | i :: p' =>
        match instrDenote i s0 with
        | Some s' => progDenote p' s'
        | None => None (A:=stack)
        end
    end) p (n :: s) = progDenote p (n :: s)

]]

Now we can unexpand the definition of [progDenote]:%\index{tactics!fold}%
*)
*)
(**
[[
 n : nat
 s : stack
 p : list instr
 ============================
 (fix progDenote (p0 : prog) (s0 : stack) {struct p0} :
  option stack :=
    match p0 with
    | nil => Some s0
    | i :: p' =>
        match instrDenote i s0 with
        | Some s' => progDenote p' s'
        | None => None (A:=stack)
        end
    end) p (n :: s) = progDenote p (n :: s)

]]

これで[progDenote]の定義を折り畳むことができます。%\index{tactics!fold}%
*)

  fold progDenote.
(**
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote p (n :: s) = progDenote p (n :: s)

]]

It looks like we are at the end of this case, since we have a trivial equality.  Indeed, a single tactic finishes us off:%\index{tactics!reflexivity}%
*)
*)
(**
[[
n : nat
s : stack
p : list instr
============================
progDenote p (n :: s) = progDenote p (n :: s)

]]

自明な等式になったので、このケースの証明はこれで終わりのように見えます。実際、次のタクティクを使えば証明は終わりです。%\index{tactics!reflexivity}%
*)

  reflexivity.

(**
(** On to the second inductive case:

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  ============================
   forall (s : stack) (p : list instr),
   progDenote (compile (Binop b e1 e2) ++ p) s =
   progDenote p (expDenote (Binop b e1 e2) :: s)

]]

We see our first example of %\index{hypotheses}%hypotheses above the double-dashed line.  They are the inductive hypotheses [IHe1] and [IHe2] corresponding to the subterms [e1] and [e2], respectively.

We start out the same way as before, introducing new free variables and unfolding and folding the appropriate definitions.  The seemingly frivolous [unfold]/[fold] pairs are actually accomplishing useful work, because [unfold] will sometimes perform easy simplifications. %\index{tactics!intros}\index{tactics!unfold}\index{tactics!fold}% *)
*)
(**
二つめのサブゴールに入ります。

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  ============================
   forall (s : stack) (p : list instr),
   progDenote (compile (Binop b e1 e2) ++ p) s =
   progDenote p (expDenote (Binop b e1 e2) :: s)

]]

二重線の上に%\index{仮定}%「仮定」が登場する最初の例です。部分項[e1]および[e2]に対応する帰納法の仮定は、それぞれ[IHe1]および[IHe2]です。

前回と同じように、自由変数を導入（[intro]duce）し、適切な定義を展開（[unfold]）して、折り畳み（[fold]）ます。一見すると、[unfold]して[fold]するのは無駄に見えるかもしれませんが、[unfold]が簡単な簡約を実施する場合があるので、実際には有益な仕事が成し遂げられています。%\index{tactics!intros}\index{tactics!unfold}\index{tactics!fold}% *)

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.

(**
(** Now we arrive at a point where the tactics we have seen so far are insufficient.  No further definition unfoldings get us anywhere, so we will need to try something different.

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  s : stack
  p : list instr
  ============================
   progDenote ((compile e2 ++ compile e1 ++ iBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

What we need is the associative law of list concatenation, which is available as a theorem [app_assoc_reverse] in the standard library.%\index{Vernacular commands!Check}%  (Here and elsewhere, it is possible to tell the difference between inputs and outputs to Coq by periods at the ends of the inputs.) *)
*)
(**
これは、これまでに使ったタクティクだけでは不十分な状況です。定義の展開をこれ以上しても何も得られないので、何か別のことを試す必要があります。

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  s : stack
  p : list instr
  ============================
   progDenote ((compile e2 ++ compile e1 ++ iBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

必要なのは、リストの結合に関する結合律（associative law）です。これは標準ライブラリにある[app_assoc_reverse]という定理として利用できます。%\index{Vernacular commands!Check}%（ここに限らず、説明に出てくる記述がCoqに対する入力なのか、それとも出力結果なのかは、末尾にピリオドがあるかどうかで見分けられます。）
*)

Check app_assoc_reverse.
(**
(** %\vspace{-.15in}%[[
app_assoc_reverse
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n

]]

If we did not already know the name of the theorem, we could use the %\index{Vernacular commands!SearchRewrite}%[SearchRewrite] command to find it, based on a pattern that we would like to rewrite: *)
*)
(**
%\vspace{-.15in}%[[
app_assoc_reverse
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n

]]

もし使いたい定理の名前がわからなければ、%\index{Vernacular commands!SearchRewrite}%[SearchRewrite]コマンドを使って検索できます。[SearchRewrite]には、以下のように、書き換えたいパターンを指定します。 *)

SearchRewrite ((_ ++ _) ++ _).
(**
(**%\vspace{-.15in}%[[
app_assoc_reverse:
  forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
]]
%\vspace{-.25in}%
[[
app_assoc: forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n

]]

We use [app_assoc_reverse] to perform a rewrite: %\index{tactics!rewrite}% *)
*)
(**
%\vspace{-.15in}%[[
app_assoc_reverse:
  forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
]]
%\vspace{-.25in}%
[[
app_assoc: forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n

]]

書き換えに[app_assoc_reverse]を使いましょう。 %\index{tactics!rewrite}% *)

  rewrite app_assoc_reverse.

(** (* %\noindent{}%changing the conclusion to:

[[
   progDenote (compile e2 ++ (compile e1 ++ iBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

Now we can notice that the lefthand side of the equality matches the lefthand side of the second inductive hypothesis, so we can rewrite with that hypothesis, too.%\index{tactics!rewrite}% *)
%\noindent{}%結論は以下のように変わります。

[[
   progDenote (compile e2 ++ (compile e1 ++ iBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

この等式の左辺は、二つめの帰納法の仮定に出てくる等式の左辺に一致しています。よって、その仮定も書き換えに使えます。%\index{tactics!rewrite}% *)

  rewrite IHe2.
(**
(** [[
   progDenote ((compile e1 ++ iBinop b :: nil) ++ p) (expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

The same process lets us apply the remaining hypothesis.%\index{tactics!rewrite}% *)
*)
(**
[[
   progDenote ((compile e1 ++ iBinop b :: nil) ++ p) (expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

同様にして残りの仮定も適用できます。%\index{tactics!rewrite}% *)

  rewrite app_assoc_reverse.
  rewrite IHe1.
(**
(** [[
   progDenote ((iBinop b :: nil) ++ p) (expDenote e1 :: expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

Now we can apply a similar sequence of tactics to the one that ended the proof of the first case.%\index{tactics!unfold}\index{tactics!simpl}\index{tactics!fold}\index{tactics!reflexivity}%
*)
*)
(**
[[
   progDenote ((iBinop b :: nil) ++ p) (expDenote e1 :: expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)

]]

これで、先ほど終わらせた一つめの証明と同様のタクティクを適用していくことができます。%\index{tactics!unfold}\index{tactics!simpl}\index{tactics!fold}\index{tactics!reflexivity}%
*)

  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

(** (* And the proof is completed, as indicated by the message: *)
次のようなメッセージが出て、証明完了です。 *)

(**
<<
  Proof completed.
>>
*)

(**
(** And there lies our first proof.  Already, even for simple theorems like this, the final proof script is unstructured and not very enlightening to readers.  If we extend this approach to more serious theorems, we arrive at the unreadable proof scripts that are the favorite complaints of opponents of tactic-based proving.  Fortunately, Coq has rich support for scripted automation, and we can take advantage of such a scripted tactic (defined elsewhere) to make short work of this lemma.  We abort the old proof attempt and start again.%\index{Vernacular commands!Abort}%
*)
*)
(**
これが本書の最初の証明です。このような単純な定理ですら、最終的に得られる証明のスクリプトは構造化されておらず、読み手にとってあまり教育的ではありません。もっと本格的な定理を同じ方針で証明すれば、タクティクを使った証明を批判するのに好都合な、可読性が低い証明のスクリプトになってしまいます。幸いなことに、Coqはスクリプトによる高機能な自動化に対応しています。別の場所でスクリプトとして定義した自動化のタクティクを利用することで、この補題に対する短い証明を与えることが可能です。これまでの証明を[Abort]で中止し、はじめからやり直してみましょう。%\index{Vernacular commands!Abort}%
*)

Abort.

(** %\index{tactics!induction}\index{tactics!crush}% *)

Lemma compile_correct' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

(**
(** We need only to state the basic inductive proof scheme and call a tactic that automates the tedious reasoning in between.  In contrast to the period tactic terminator from our last proof, the %\index{tactics!semicolon}%semicolon tactic separator supports structured, compositional proofs.  The tactic [t1; t2] has the effect of running [t1] and then running [t2] on each remaining subgoal.  The semicolon is one of the most fundamental building blocks of effective proof automation.  The period terminator is very useful for exploratory proving, where you need to see intermediate proof states, but final proofs of any serious complexity should have just one period, terminating a single compound tactic that probably uses semicolons.

The [crush] tactic comes from the library associated with this book and is not part of the Coq standard library.  The book's library contains a number of other tactics that are especially helpful in highly automated proofs.

The %\index{Vernacular commands!Qed}%[Qed] command checks that the proof is finished and, if so, saves it.  The tactic commands we have written above are an example of a _proof script_, or a series of Ltac programs; while [Qed] uses the result of the script to generate a _proof term_, a well-typed term of Gallina.  To believe that a theorem is true, we only need to trust that the (relatively simple) checker for proof terms is correct; the use of proof scripts is immaterial.  Part I of this book will introduce the principles behind encoding all proofs as terms of Gallina.

The proof of our main theorem is now easy.  We prove it with four period-terminated tactics, though separating them with semicolons would work as well; the version here is easier to step through.%\index{tactics!intros}% *)
*)
(**
必要なのは、まず帰納法による証明における決まり文句を書き、中間の長々しい推論を自動化するタクティクを呼ぶことだけです。前回の証明ではタクティクの末尾にピリオドを置きましたが、今回の証明ではピリオドの代わりに%\index{tactics!semicolon}%セミコロンを使います。セミコロンは二つのタクティクを切り離し、証明を構造化して組み合わせられるようにしてくれます。タクティク[t1; t2]には、[t1]を適用してから残りの各サブゴールに対して[t2]を適用する、という効果があります。セミコロンは、証明を効果的に自動化するための基本的な構成要素の一つです。ピリオドは、途中の状態を確認しながら探索的に証明をしていくときは便利に使えます。しかし、それなりに複雑な証明は、最終的にすべて、セミコロンを使って合成した一つのタクティクの末尾にピリオドが一つだけある状態にすべきです。

[crush]は、本書に付随するライブラリで用意しているタクティクであり、Coqの標準ライブラリにはありません。ほかにも本書のライブラリには証明の高度な自動化にとても役立つタクティクがいくつも含まれています。

%\index{Vernacular commands!Qed}%[Qed]コマンドは、証明が実際に完了していることを確認し、そうであればその証明を保存します。これまで書いてきたタクティクたちは_[証明スクリプト]_、別の言い方をするとLtacプログラムの列であり、正しく型付けされたGallinaの項です。証明スクリプトそのものは、定理が正しいことを信じる根拠にはなりません。定理が正しいことを信じるのに必要なのは、証明項の（比較的単純な）検査器が正しいことを信頼することだけです。本書の第1部では、あらゆる証明をGallinaの項として表現することの背景にある原理について説明します。

今、主定理は容易に証明できます。ここではピリオドで終端した四つのタクティクにより証明します。セミコロン区切りにしても同じことですが、証明を順番に進めるには、このやり方のほうが簡単だからです。%\index{tactics!intros}% *)

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.
(**
(** [[
  e : exp
  ============================
   progDenote (compile e) nil = Some (expDenote e :: nil)

]]

At this point, we want to massage the lefthand side to match the statement of [compile_correct'].  A theorem from the standard library is useful: *)
*)
(**
[[
  e : exp
  ============================
   progDenote (compile e) nil = Some (expDenote e :: nil)

]]

ここで、左辺を[compile_correct']の主張に合うように書き換えましょう。標準ライブラリの以下の定理が使えます。 *)

Check app_nil_end.
(** [[
app_nil_end
     : forall (A : Type) (l : list A), l = l ++ nil
]]
%\index{tactics!rewrite}% *)

  rewrite (app_nil_end (compile e)).

(**
(** This time, we explicitly specify the value of the variable [l] from the theorem statement, since multiple expressions of list type appear in the conclusion.  The [rewrite] tactic might choose the wrong place to rewrite if we did not specify which we want.

[[
  e : exp
  ============================
   progDenote (compile e ++ nil) nil = Some (expDenote e :: nil)

]]

Now we can apply the lemma.%\index{tactics!rewrite}% *)
*)
(**
今度は結論に複数のリストが現れているので、定理内の変数[l]の値を明示しています。[rewrite]タクティクは、書き換えたいものを明示しないと、別の場所を選んで書き換えてしまうことがあります。

[[
  e : exp
  ============================
   progDenote (compile e ++ nil) nil = Some (expDenote e :: nil)

]]

これで補題が適用できます。%\index{tactics!rewrite}% *)

  rewrite compile_correct'.
(**
(** [[
  e : exp
  ============================
   progDenote nil (expDenote e :: nil) = Some (expDenote e :: nil)

]]

We are almost done.  The lefthand and righthand sides can be seen to match by simple symbolic evaluation.  That means we are in luck, because Coq identifies any pair of terms as equal whenever they normalize to the same result by symbolic evaluation.  By the definition of [progDenote], that is the case here, but we do not need to worry about such details.  A simple invocation of %\index{tactics!reflexivity}%[reflexivity] does the normalization and checks that the two results are syntactically equal.%\index{tactics!reflexivity}% *)
*)
(**
[[
  e : exp
  ============================
   progDenote nil (expDenote e :: nil) = Some (expDenote e :: nil)

]]

これでもうほとんど終わりです。左辺と右辺は単純な記号的評価によって一致しそうに見えます。ありがたいことに、記号的評価によって同じ結果に正規化されるものは、Coqによって同じ項とみなされます。この場合に左辺と右辺が同じ項に評価されるのは[progDenote]の定義によるわけですが、そのような詳細を気にする必要はありません。%\index{tactics!reflexivity}%[reflexivity]タクティクを呼び出すだけで、正規化および左辺と右辺の構文的な等しさの確認を実施してくれます。%\index{tactics!reflexivity}% *)

  reflexivity.
Qed.
(* end thide *)

(**
(** This proof can be shortened and automated, but we leave that task as an exercise for the reader. *)
*)
(**
この証明は、もっと短く、さらに自動化できますが、これは読者への演習問題としましょう。 *)


(** * 型付き式 *)

(**
(** In this section, we will build on the initial example by adding additional expression forms that depend on static typing of terms for safety. *)
*)
(**
この節では、項が静的型付けを持つような安全な式の構造を付け足すことで、最初の例を拡充していきます。 *)

(** ** ソース言語 *)

(**
(** We define a trivial language of types to classify our expressions: *)
*)
(**
式を区別するために、自明な型の言語を定義します。 *)

Inductive type : Set := Nat | Bool.

(**
(** Like most programming languages, Coq uses case-sensitive variable names, so that our user-defined type [type] is distinct from the [Type] keyword that we have already seen appear in the statement of a polymorphic theorem (and that we will meet in more detail later), and our constructor names [Nat] and [Bool] are distinct from the types [nat] and [bool] in the standard library.

   Now we define an expanded set of binary operators. *)
*)
(**
多くのプログラミング言語と同様に、Coqでは変数名の大文字と小文字に区別があるので、ここで定義した型[type]は、先ほど多相的な定理の主張の中に登場した[Type]キーワード（詳細は後で説明します）とは区別されます。コンストラクタである[Nat]と[Bool]も、標準ライブラリ内にある型[nat]および[bool]とは異なります。

二項演算子についても拡張したものを定義しましょう。 *)

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

(**
(** The definition of [tbinop] is different from [binop] in an important way.  Where we declared that [binop] has type [Set], here we declare that [tbinop] has type [type -> type -> type -> Set].  We define [tbinop] as an _indexed type family_.  Indexed inductive types are at the heart of Coq's expressive power; almost everything else of interest is defined in terms of them.

The intuitive explanation of [tbinop] is that a [tbinop t1 t2 t] is a binary operator whose operands should have types [t1] and [t2], and whose result has type [t].  For instance, constructor [TLt] (for less-than comparison of numbers) is assigned type [tbinop Nat Nat Bool], meaning the operator's arguments are naturals and its result is Boolean.  The type of [TEq] introduces a small bit of additional complication via polymorphism: we want to allow equality comparison of any two values of any type, as long as they have the _same_ type.

ML and Haskell have indexed algebraic datatypes.  For instance, their list types are indexed by the type of data that the list carries.  However, compared to Coq, ML and Haskell 98 place two important restrictions on datatype definitions.

First, the indices of the range of each data constructor must be type variables bound at the top level of the datatype definition.  There is no way to do what we did here, where we, for instance, say that [TPlus] is a constructor building a [tbinop] whose indices are all fixed at [Nat].  %\index{generalized algebraic datatypes}\index{GADTs|see{generalized algebraic datatypes}}% _Generalized algebraic datatypes_ (GADTs)%~\cite{GADT}% are a popular feature in %\index{GHC Haskell}%GHC Haskell, OCaml 4, and other languages that removes this first restriction.

The second restriction is not lifted by GADTs.  In ML and Haskell, indices of types must be types and may not be _expressions_.  In Coq, types may be indexed by arbitrary Gallina terms.  Type indices can live in the same universe as programs, and we can compute with them just like regular programs.  Haskell supports a hobbled form of computation in type indices based on %\index{Haskell}%multi-parameter type classes, and recent extensions like type functions bring Haskell programming even closer to "real" functional programming with types, but, without dependent typing, there must always be a gap between how one programs with types and how one programs normally.
*)
*)
(**
[tbinop]の定義には、[binop]の定義とは大きく異なる点があります。[binop]は[Set]型であると宣言しましたが、[tbinop]は[type -> type -> type -> Set]型であると宣言しています。これは、_[添字付けされた型の族]_（indexed type family）として[tbinop]を定義しているということです。添字付けされた型の族は、Coqの表現力の根幹です。実際、それ以外の興味深いものは、ほとんどすべて添字付けされた型の族によって定義されます。

[tbinop]の直観的な説明は、「[tbinop t1 t2 t]は、型[t1]と[t2]のオペランドを取って型[t]の結果を返す二項演算子である」というものです。たとえばコンストラクタ[TLt]（自然数の順序$\leq$#≦#）は、引数が自然数、結果がブール値であることを意味する型[tbinop Nat Nat Bool]を持ちます。[TEq]の型は、多相性によって少し複雑になっています。具体的には、等値の比較である[TEq]では、_[同じ]_型を持つ値を任意に取れるようにしてあります。

MLやHaskellには添字付けされた代数的データ型があります。たとえば、MLやHaskellのリスト型は、リストの要素の型によって添字付けられています。ただし、MLやHaskelll 98は、Coqに比べるとデータ型の定義に関して二つの大きな制限があります。

まず、各データコンストラクタの添字が、そのデータ型の定義のトップレベルで束縛された型変数でなければいけません。
たとえば、[TPlus]はすべての添字が[Nat]に固定された[tbinop]を構成するコンストラクタですが、MLやHaskellではそのような定義をする手段はありません。
%\index{generalized algebraic datatypes}\index{GADTs|see{generalized algebraic datatypes}}%_一般化代数データ型_（Generalized algebraic datatypes、GADTs）%~\cite{GADT}%は、%\index{GHC Haskell}%GHC Haskell、OCaml 4など、この制限が取り除かれている言語で広く採用されている機能です。

二つめの制限はGADTsでは対処できません。MLやHaskellでは、型の添字は必ず型であり、[式]であってはいけません。Coqでは、型は任意のGallina項により添字付けできます。型の添字はプログラムと同じ領域に属することができ、それらは通常のプログラムと同様に計算できます。
Haskellは、%\index{Haskell}multi-parameter type classに基いた型の添字計算に制限付きで対応しています。また、型関数（type function）のような近年の拡張により、Haskellプログラミングは「本物」の型付き関数型プログラミングにだいぶ近づきました。しかし、依存型なしでは、型を使ってプログラミングすることと、普通にプログラミングすることとの間に、必ずギャップが生じます。
*)

(**
(** We can define a similar type family for typed expressions, where a term of type [texp t] can be assigned object language type [t].  (It is conventional in the world of interactive theorem proving to call the language of the proof assistant the%\index{meta language}% _meta language_ and a language being formalized the%\index{object language}% _object language_.) *)
*)
(**
型付きの式に対しても、同じように型族を定義できます。型[texp t]を持つ項には、対象言語の型[t]が割り当てられます。（対話的定理証明の分野では、慣習的に、証明支援器の言語を%\index{メタ言語}%[メタ言語]と呼び、形式化の対象になっている言語を%\index{対象言語}%[対象言語]と呼びます。）*)

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(** (* Thanks to our use of dependent types, every well-typed [texp] represents a well-typed source expression, by construction.  This turns out to be very convenient for many things we might want to do with expressions.  For instance, it is easy to adapt our interpreter approach to defining semantics.  We start by defining a function mapping the types of our object language into Coq types: *)
依存型を利用することで、すべてのwell-typedな[texp]は、その構成によりwell-typedなソース言語の式を表すことになります。式を使って何かをしたい場合、これがとても便利なことが多いのです。たとえば、インタプリタのときの手法をセマンティクスの定義にも簡単に適用できます。対象言語の型をCoqの型に移す写像の定義から始めましょう。 *)

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(**
(** It can take a few moments to come to terms with the fact that [Set], the type of types of programs, is itself a first-class type, and that we can write functions that return [Set]s.  Past that wrinkle, the definition of [typeDenote] is trivial, relying on the [nat] and [bool] types from the Coq standard library.  We can interpret binary operators by relying on standard-library equality test functions [eqb] and [beq_nat] for Booleans and naturals, respectively, along with a less-than test [leb]: *)
*)
(**
「プログラムの型」の型である[Set]は、それ自身がファーストクラスの型なので、[Set]を返す関数が書けます。この事実を受け入れるには少し時間がかかるかもしれませんね。それさえ納得できれば、[typeDenote]の定義ではCoqの標準ライブラリの型である[nat]と[bool]をそのまま使っているだけです。二項演算子の定義では、標準ライブラリの比較関数である[eqb]（ブール値間の等値性）、[beq_nat]（自然数値間の等値性）、[leb]（自然数の$\leq$#≦#）をそのまま使います。*)

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

(**
(** This function has just a few differences from the denotation functions we saw earlier.  First, [tbinop] is an indexed type, so its indices become additional arguments to [tbinopDenote].  Second, we need to perform a genuine%\index{dependent pattern matching}% _dependent pattern match_, where the necessary _type_ of each case body depends on the _value_ that has been matched.  At this early stage, we will not go into detail on the many subtle aspects of Gallina that support dependent pattern-matching, but the subject is central to Part II of the book.

The same tricks suffice to define an expression denotation function in an unsurprising way.  Note that the [type] arguments to the [TBinop] constructor must be included explicitly in pattern-matching, but here we write underscores because we do not need to refer to those arguments directly. *)
*)
(**
この関数は、前に定義した[binopDenote]関数とそれほど大きく違うわけではありません。まず、[tbinop]は添字付けされた型なので、その添字が[tbinopDenote]の追加の引数になります。
次に、場合分けの本体における_[型]_がマッチした_[値]_に依存する場合には、正真正銘の%\index{依存パターンマッチ}%_[依存パターンマッチ]_が必要です。
Gallinaには、依存パターンマッチを支援する面がたくさんありますが、ここでは詳細には踏み込みません。これは本書の第2部の中心テーマです。

同じ仕組みにより、式に対する[texpDenote]関数も自然に定義できます。
コンストラクタ[TBinop]に対する[type]型の引数を明示的にパターンマッチに含めなければなりませんが、これらの引数を直接参照する必要はないので、ここではアンダースコアを書いています。
*)

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(**
(** We can evaluate a few example programs to convince ourselves that this semantics is correct. *)
*)
(**
このセマンティクスが正しいことを確かめるために、プログラムをいくつか試しに評価してみましょう。*)

Eval simpl in texpDenote (TNConst 42).
(** [= 42 : typeDenote Nat] *)

(* begin hide *)
Eval simpl in texpDenote (TBConst false).
(* end hide *)
Eval simpl in texpDenote (TBConst true).
(** [= true : typeDenote Bool] *)

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= 28 : typeDenote Nat] *)

Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= false : typeDenote Bool] *)

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= true : typeDenote Bool] *)

(**
(** %\smallskip{}%Now we are ready to define a suitable stack machine target for compilation. *)
*)
(**
%\smallskip{}%これでコンパイルに適したスタックマシンのターゲットを定義する準備ができました。*)


(** ** ターゲット言語 *)

(**
(** In the example of the untyped language, stack machine programs could encounter stack underflows and "get stuck."  This was unfortunate, since we had to deal with this complication even though we proved that our compiler never produced underflowing programs.  We could have used dependent types to force all stack machine programs to be underflow-free.

For our new languages, besides underflow, we also have the problem of stack slots with naturals instead of bools or vice versa.  This time, we will use indexed typed families to avoid the need to reason about potential failures.

We start by defining stack types, which classify sets of possible stacks. *)
*)
(**
言語に型がなかったときは、スタックマシーンのプログラムがスタックアンダーフローを起こして動かなくなる可能性がありました。アンダーフローするプログラムをコンパイラは生成しない、と証明したのに、そのような事態への対処が必要になるというのでは、残念すぎます。
依存型を使えば、すべてのスタックマシーンのプログラムがアンダーフローを起こさないことが強制できたでしょう。

新しい言語には、アンダーフロー以外にも、ブール値ではなく自然数がスタックに入ったり、その逆の状況が起きたりするという問題があります。ここでは、起こりうる障害を推論しなくて済むように、添字付けられた型の族を使うことにします。

まずはスタック型を定義し、起こりうるスタックの状態を分類できるようにしましょう。
*)

Definition tstack := list type.

(**
(** Any stack classified by a [tstack] must have exactly as many elements, and each stack element must have the type found in the same position of the stack type.

We can define instructions in terms of stack types, where every instruction's type tells us what initial stack type it expects and what final stack type it will produce. *)
*)
(**
ある[tstack]によって分類されるスタックは、いずれも要素の数が同じでなければなりません。また、各スタックの要素の型は、スタック型における同じ位置の型でなければなりません。

スタック型を利用して命令を定義しましょう。いずれの命令も、命令が最初に期待しているスタック型と命令によって生成される最終的なスタック型とがわかるような型を持ちます。

*)

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

(** (** Stack machine programs must be a similar inductive family, since, if we again used the [list] type family, we would not be able to guarantee that intermediate stack types match within a program. *)*)
(**
スタックマシーンのプログラムも、同様な帰納的な族にしなければなりません。
もしここで前のように[list]型の族を使ったら、プログラム内部で中間的なスタック型がマッチするかどうかを保証する手立てがなくなってしまうからです。
*)

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

(**
(** Now, to define the semantics of our new target language, we need a representation for stacks at runtime.  We will again take advantage of type information to define types of value stacks that, by construction, contain the right number and types of elements. *)
*)
(**
次は、新しいターゲット言語のセマンティクスを定義するために、実行時のスタックの表現を決める必要があります。構成の仕方から要素の個数と型が正しい値について、スタックの型を定義するのにも、型の情報が役立ちます。
*)

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

(**
(** This is another [Set]-valued function.  This time it is recursive, which is perfectly valid, since [Set] is not treated specially in determining which functions may be written.  We say that the value stack of an empty stack type is any value of type [unit], which has just a single value, [tt].  A nonempty stack type leads to a value stack that is a pair, whose first element has the proper type and whose second element follows the representation for the remainder of the stack type.  We write [%]%\index{notation scopes}\coqdocvar{%#<tt>#type#</tt>#%}% as an instruction to Coq's extensible parser.  In particular, this directive applies to the whole [match] expression, which we ask to be parsed as though it were a type, so that the operator [*] is interpreted as Cartesian product instead of, say, multiplication.  (Note that this use of %\coqdocvar{%#<tt>#type#</tt>#%}% has no connection to the inductive type [type] that we have defined.)

This idea of programming with types can take a while to internalize, but it enables a very simple definition of instruction denotation.  Our definition is like what you might expect from a Lisp-like version of ML that ignored type information.  Nonetheless, the fact that [tinstrDenote] passes the type-checker guarantees that our stack machine programs can never go wrong.  We use a special form of [let] to destructure a multi-level tuple. *)
*)
(**
[Set]値の関数がまた出てきました。
今回は再帰関数です。書かれる可能性がある関数を決める際に[Set]が特別扱いされることはないので、再帰関数でも完全に妥当です。
この関数は、空のスタック型の値を表すスタックは[unit]型の任意の値である、と言っています。
[unit]は、唯一の値[tt]を持つ型です。
空でないスタック型は、ペアの値を表すスタックになります。そのペアは、一つめの要素が適切な型で、二つめの要素が残りのスタック型の表現に従うようなものです。
[%]%\index{notation scopes}\coqdocvar{%#<tt>#type#</tt>#%}%は、Coqの拡張可能なパーサへの、ある指示になります。
この場合は[match]式全体に適用される指示で、その[match]式が型としてパースされるようにし、演算子[*]が乗算ではなく直積として解釈されるようにします。
（この場合の%\coqdocvar{%#<tt>#type#</tt>#%}%は、先ほど定義した帰納的データ型[type]には関係ありません。)

型を使ったプログラミングの概念を習得するには時間がかかるかもしれませんが、おかげで命令の表示的意味論がとてもシンプルに定義できます。
ここで得られた定義は、型情報が無視されたLispふうのMLによる定義にも似ています。
にもかかわらず、[tinstrDenote]が型検査を通るという事実により、このスタックマシーンのプログラムで障害が発生することがありえないと保証されるのです。
多重タプルを分解するには特殊な形式の[let]を使います。
*)

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

(**
(** Why do we choose to use an anonymous function to bind the initial stack in every case of the [match]?  Consider this well-intentioned but invalid alternative version:
[[
Definition tinstrDenote ts ts' (i : tinstr ts ts') (s : vstack ts) : vstack ts' :=
  match i with
    | TiNConst _ n => (n, s)
    | TiBConst _ b => (b, s)
    | TiBinop _ _ _ _ b =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.
]]

The Coq type checker complains that:

<<
The term "(n, s)" has type "(nat * vstack ts)%type"
 while it is expected to have type "vstack ?119".
>>

This and other mysteries of Coq dependent typing we postpone until Part II of the book.  The upshot of our later discussion is that it is often useful to push inside of [match] branches those function parameters whose types depend on the type of the value being matched.  Our later, more complete treatment of Gallina's typing rules will explain why this helps.
*)
*)
(**
[match]の場合分けで、初期スタックの束縛に無名関数を使ったのはなぜでしょうか。次のように書くと意図がはっきりしますが、これは正しくありません。
[[
Definition tinstrDenote ts ts' (i : tinstr ts ts') (s : vstack ts) : vstack ts' :=
  match i with
    | TiNConst _ n => (n, s)
    | TiBConst _ b => (b, s)
    | TiBinop _ _ _ _ b =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.
]]

Coqの型検査器は以下のようなエラーを出力します。

<<
The term "(n, s)" has type "(nat * vstack ts)%type"
 while it is expected to have type "vstack ?119".
>>

Coqの依存型における型付けの深淵な部分については第2部で述べます。関数の引数のうち、マッチさせる値の型に依存するような型を持つものは、[match]の分岐の中に押し込めるとうまくいく場合が多い、というのが上記の議論の要点です。それでうまくいく理由は、のちほどGallinaの型付け規則についてもっときちんと扱うときに説明します。
*)

(**
(** We finish the semantics with a straightforward definition of program denotation. *)
*)
(**
最後に、プログラムの表示的意味論を直接定義します。
*)

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(**
(** The same argument-postponing trick is crucial for this definition. *)
*)
(**
この定義でも引数を[match]の中に入れるテクニックが重要です。
*)

(** ** 翻訳 *)

(**
(** To define our compilation, it is useful to have an auxiliary function for concatenating two stack machine programs. *)
*)
(**
コンパイルを定義するために、スタックマシーンの二つのプログラムを結合する補助関数を用意しましょう。
*)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

(**
(** With that function in place, the compilation is defined very similarly to how it was before, modulo the use of dependent typing. *)
*)
(**
スタックマシーンの結合処理をこの関数で置き換えれば、前とよく似た形でコンパイルの関数を定義できます（依存型を使っていることを除く）。
*)

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

(**
(** One interesting feature of the definition is the underscores appearing to the right of [=>] arrows.  Haskell and ML programmers are quite familiar with compilers that infer type parameters to polymorphic values.  In Coq, it is possible to go even further and ask the system to infer arbitrary terms, by writing underscores in place of specific values.  You may have noticed that we have been calling functions without specifying all of their arguments.  For instance, the recursive calls here to [tcompile] omit the [t] argument.  Coq's _implicit argument_ mechanism automatically inserts underscores for arguments that it will probably be able to infer.  Inference of such values is far from complete, though; generally, it only works in cases similar to those encountered with polymorphic type instantiation in Haskell and ML.

The underscores here are being filled in with stack types.  That is, the Coq type inferencer is, in a sense, inferring something about the flow of control in the translated programs.  We can take a look at exactly which values are filled in: *)
*)
(**
この定義で面白いのは、矢印[=>]の右側にアンダースコアがあることです。
型パラメータから多相的な値を推論するコンパイラは、HaskellやMLのプログラマにはお馴染みでしょう。
Coqではさらに踏み込んで、特定の値の位置にアンダースコアを書くことで、任意の項に対する値の推論をシステムに任せることが可能です。
これまでも引数をすべて与えずに関数を呼び出していたことに気付いている読者もいるかもしれません。
たとえば、[tcompile]の再帰呼び出しでは引数[t]を省略しています。
Coqには_[暗黙引数]_（implicit argument）という仕組みがあり、推論ができるかもしれない引数に対して自動でアンダースコアを挿入します。
しかし、そのような値の推論を完全にするのは、到底無理な話です。
一般には、HaskellやMLにおいて多相型の具体化ができるような場面でしか機能しません。

この場合、アンダースコアにはスタック型が入ります。
つまり、Coqの型推論器は、翻訳されたプログラムの制御フローについて何かしら推論していると言えます。
何の値が入っているかは、以下のようにして確認できます。
*)

Print tcompile.
(** %\vspace{-.15in}%[[
tcompile =
fix tcompile (t : type) (e : texp t) (ts : tstack) {struct e} :
  tprog ts (t :: ts) :=
  match e in (texp t0) return (tprog ts (t0 :: ts)) with
  | TNConst n => TCons (TiNConst ts n) (TNil (Nat :: ts))
  | TBConst b => TCons (TiBConst ts b) (TNil (Bool :: ts))
  | TBinop arg1 arg2 res b e1 e2 =>
      tconcat (tcompile arg2 e2 ts)
        (tconcat (tcompile arg1 e1 (arg2 :: ts))
           (TCons (TiBinop ts b) (TNil (res :: ts))))
  end
     : forall t : type, texp t -> forall ts : tstack, tprog ts (t :: ts)
]]
*)


(**(** We can check that the compiler generates programs that behave appropriately on our sample programs from above: *)*)
(**
このコンパイラでも、前に利用したサンプルプログラムに対して適切に動作するプログラムが生成されることを確認しましょう。
*)

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
(** [= (42, tt) : vstack (Nat :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (28, tt) : vstack (Nat :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (false, tt) : vstack (Bool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)

(**(** %\smallskip{}%The compiler seems to be working, so let us turn to proving that it _always_ works. *)*)
(** %\smallskip{}%うまくコンパイラが動いているように見えるので、これが_[常に]_正しく動くことを証明しましょう。 *)


(** ** 翻訳の正しさ *)

(** (** We can state a correctness theorem similar to the last one. *)*)
(** 正しさについての定理を前回と同様に主張します。 *)

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
(* begin hide *)
Abort.
(* end hide *)
(* begin thide *)

(**(** Again, we need to strengthen the theorem statement so that the induction will go through.  This time, to provide an excuse to demonstrate different tactics, I will develop an alternative approach to this kind of proof, stating the key lemma as: *)*)
(**
帰納法がうまくいくように、今回も定理の主張を強める必要があります。
新しいタクティクを使って見せたいので、今回は前とは違う手法で証明を開発することにします。
次の重要な補題を用意することから始めましょう。
*)

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).

(**(** While lemma [compile_correct'] quantified over a program that is the "continuation"%~\cite{continuations}% for the expression we are considering, here we avoid drawing in any extra syntactic elements.  In addition to the source expression and its type, we also quantify over an initial stack type and a stack compatible with it.  Running the compilation of the program starting from that stack, we should arrive at a stack that differs only in having the program's denotation pushed onto it.

   Let us try to prove this theorem in the same way that we settled on in the last section. *)*)
(**
[compile_correct']は、考慮している式への「継続」%~\cite{continuations}%であるようなプログラムについて量化された補題になっていますが、構文上の要素は増やさないようにしています。
ソース言語の式とその型に加えて、最初のスタック型と、そのスタック型に適合するスタックについても量化されています。
そのようなスタックからプログラムのコンパイルを始めると、その上にプログラムの表示的意味がプッシュされたスタックが得られる、という補題です。

前節と同じ方法でこの補題を証明しましょう。*)

  induction e; crush.

(**(** We are left with this unproved conclusion:

[[
tprogDenote
     (tconcat (tcompile e2 ts)
        (tconcat (tcompile e1 (arg2 :: ts))
           (TCons (TiBinop ts t) (TNil (res :: ts))))) s =
   (tbinopDenote t (texpDenote e1) (texpDenote e2), s)

]]

We need an analogue to the [app_assoc_reverse] theorem that we used to rewrite the goal in the last section.  We can abort this proof and prove such a lemma about [tconcat].
*)*)
(**
次のような未証明の結論が残りました。

[[
tprogDenote
     (tconcat (tcompile e2 ts)
        (tconcat (tcompile e1 (arg2 :: ts))
           (TCons (TiBinop ts t) (TNil (res :: ts))))) s =
   (tbinopDenote t (texpDenote e1) (texpDenote e2), s)

]]

前節でゴールを書き換えるのに使った定理[app_assoc_reverse]に類似したものが必要です。
この証明はここで中止し、[tconcat]に対するそのような補題を証明します。
*)

Abort.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

(**
(** This one goes through completely automatically.

Some code behind the scenes registers [app_assoc_reverse] for use by [crush].  We must register [tconcat_correct] similarly to get the same effect:%\index{Vernacular commands!Hint Rewrite}% *)
*)
(**
これは完全に自動で証明されます。

[app_assoc_reverse]が[crush]で利用されるのは、水面下のコードがそのように登録してくれるからです。
[tconcat_correct]についても、同じ効果を得るための登録が必要です。%\index{Vernacular  commands!Hint Rewrite}%
*)

Hint Rewrite tconcat_correct.

(**
(** Here we meet the pervasive concept of a _hint_.  Many proofs can be found through exhaustive enumerations of combinations of possible proof steps; hints provide the set of steps to consider.  The tactic [crush] is applying such brute force search for us silently, and it will consider more possibilities as we add more hints.  This particular hint asks that the lemma be used for left-to-right rewriting.

Now we are ready to return to [tcompile_correct'], proving it automatically this time. *)
*)
(**
ここで、_[ヒント]_という便利な概念を説明しましょう。
証明ステップの組み合わせを徹底的に列挙してしまうと、証明がたくさん見つかる可能性があります。
そこで、考えるべきステップの集合を指定するためにヒントを与えます。
タクティク[crush]は基本的にはしらみつぶしの探索を適用し、ヒントを与えるとその分だけ多くの可能性を考慮します。
この[Hint Rewrite tconcat_correct.]により、補題[tconcat_correct]を左から右への書き換えに使うというヒントを与えています。

それでは[tcompile_correct']に戻り、今度は自動で証明してみましょう。
*)

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

(** (** We can register this main lemma as another hint, allowing us to prove the final theorem trivially. *)*)
(**
この主補題を新しいヒントとして登録すれば、最後の定理の証明が自明になります。
*)

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.
(* end thide *)

(**
(** It is probably worth emphasizing that we are doing more than building mathematical models.  Our compilers are functional programs that can be executed efficiently.  One strategy for doing so is based on%\index{program extraction}% _program extraction_, which generates OCaml code from Coq developments.  For instance, we run a command to output the OCaml version of [tcompile]:%\index{Vernacular commands!Extraction}% *)
*)
(**
ここで強調しておきたいのは、いま私たちは数学的なモデルを構築しているだけではないということです。
開発したコンパイラは、効率的に実行できる関数型のプログラムになります。
そのための手段として、CoqコードからOCamlコードを生成する_[プログラム抽出]_%\index{program extraction}%があります。
たとえば、OCaml版の[tcompile]を出力するには次のようにコマンドを実行します。%\index{Vernacular commands!Extraction}%
*)

Extraction tcompile.

(**
(** <<
let rec tcompile t e ts =
  match e with
  | TNConst n ->
    TCons (ts, (Cons (Nat, ts)), (Cons (Nat, ts)), (TiNConst (ts, n)), (TNil
      (Cons (Nat, ts))))
  | TBConst b ->
    TCons (ts, (Cons (Bool, ts)), (Cons (Bool, ts)), (TiBConst (ts, b)),
      (TNil (Cons (Bool, ts))))
  | TBinop (t1, t2, t0, b, e1, e2) ->
    tconcat ts (Cons (t2, ts)) (Cons (t0, ts)) (tcompile t2 e2 ts)
      (tconcat (Cons (t2, ts)) (Cons (t1, (Cons (t2, ts)))) (Cons (t0, ts))
        (tcompile t1 e1 (Cons (t2, ts))) (TCons ((Cons (t1, (Cons (t2,
        ts)))), (Cons (t0, ts)), (Cons (t0, ts)), (TiBinop (t1, t2, t0, ts,
        b)), (TNil (Cons (t0, ts))))))
>>

We can compile this code with the usual OCaml compiler and obtain an executable program with halfway decent performance.

This chapter has been a whirlwind tour through two examples of the style of Coq development that I advocate.  Parts II and III of the book focus on the key elements of that style, namely dependent types and scripted proof automation, respectively.  Before we get there, we will spend some time in Part I on more standard foundational material.  Part I may still be of interest to seasoned Coq hackers, since I follow the highly automated proof style even at that early stage. *)
*)
(** <<
let rec tcompile t e ts =
  match e with
  | TNConst n ->
    TCons (ts, (Cons (Nat, ts)), (Cons (Nat, ts)), (TiNConst (ts, n)), (TNil
      (Cons (Nat, ts))))
  | TBConst b ->
    TCons (ts, (Cons (Bool, ts)), (Cons (Bool, ts)), (TiBConst (ts, b)),
      (TNil (Cons (Bool, ts))))
  | TBinop (t1, t2, t0, b, e1, e2) ->
    tconcat ts (Cons (t2, ts)) (Cons (t0, ts)) (tcompile t2 e2 ts)
      (tconcat (Cons (t2, ts)) (Cons (t1, (Cons (t2, ts)))) (Cons (t0, ts))
        (tcompile t1 e1 (Cons (t2, ts))) (TCons ((Cons (t1, (Cons (t2,
        ts)))), (Cons (t0, ts)), (Cons (t0, ts)), (TiBinop (t1, t2, t0, ts,
        b)), (TNil (Cons (t0, ts))))))
>>

このコードは通常のOCamlコンパイラでコンパイルが可能であり、そこそこ効率が良い実行可能プログラムが得られます。

本章では、筆者が提案するCoqの開発スタイルの例を二つ、駆け足で紹介してきました。
本書の第2部と第3部では、この開発スタイルを支える依存型およびスクリプトによる証明の自動化にそれぞれ焦点を当てます。
その前に、第1部では、より標準的な基礎となる題材について説明します。
早い段階から強力に自動化するスタイルで証明していくので、経験抱負なCoqハッカーにとっても第1部の解説は興味深いものになるでしょう。
*)

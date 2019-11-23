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

Definition bad : unit := tt.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)


(**
(if
       (string= default-directory "/Users/ksk/project/cpdt-japanese/src/")
       (setq coq-prog-name
	     (ocaml-dir "bin/coqtop"))) (** %\chapter{Infinite Data and Proofs}% *)
*)
(** %\chapter{無限の大きさをもつデータと証明}% *)

(**
(**
In lazy functional programming languages like %\index{Haskell}%Haskell, infinite data structures are everywhere%~\cite{whyfp}%.  Infinite lists and more exotic datatypes provide convenient abstractions for communication between parts of a program.  Achieving similar convenience without infinite lazy structures would, in many cases, require acrobatic inversions of control flow. 

%\index{laziness}%Laziness is easy to implement in Haskell, where all the definitions in a program may be thought of as mutually recursive.  In such an unconstrained setting, it is easy to implement an infinite loop when you really meant to build an infinite list, where any finite prefix of the list should be forceable in finite time.  Haskell programmers learn how to avoid such slip-ups.  In Coq, such a laissez-faire policy is not good enough.

We spent some time in the last chapter discussing the %\index{Curry-Howard correspondence}%Curry-Howard isomorphism, where proofs are identified with functional programs.  In such a setting, infinite loops, intended or otherwise, are disastrous.  If Coq allowed the full breadth of definitions that Haskell did, we could code up an infinite loop and use it to prove any proposition vacuously.  That is, the addition of general recursion would make CIC _inconsistent_.  For an arbitrary proposition [P], we could write:
[[
Fixpoint bad (u : unit) : P := bad u.
]]

This would leave us with [bad tt] as a proof of [P].

There are also algorithmic considerations that make universal termination very desirable.  We have seen how tactics like [reflexivity] compare terms up to equivalence under computational rules.  Calls to recursive, pattern-matching functions are simplified automatically, with no need for explicit proof steps.  It would be very hard to hold onto that kind of benefit if it became possible to write non-terminating programs; we would be running smack into the halting problem.

One solution is to use types to contain the possibility of non-termination.  For instance, we can create a "non-termination monad," inside which we must write all of our general-recursive programs; several such approaches are surveyed in Chapter 7.  This is a heavyweight solution, and so we would like to avoid it whenever possible.

Luckily, Coq has special support for a class of lazy data structures that happens to contain most examples found in Haskell.  That mechanism,%\index{co-inductive types}% _co-inductive types_, is the subject of this chapter. *)
*)

(**
%\index{Haskell}%Haskellのような遅延評価を行う関数型プログラミング言語では，
無限の大きさをもつデータ構造があらゆるところで扱われています%~\cite{whyfp}%．
無限リストなどの特殊なデータ構造は，
プログラム内でのデータのやり取りを抽象的に捉えるためには便利なものです．
遅延評価を伴う無限のデータ構造を使わずに同じような利便性を得るためには，
制御フローを元にしてプログラムを記述するという巧妙な反転の仕組みが必要となるでしょう．

Hakellにおいて%\index{遅延評価}%遅延評価を行うプログラムを実装するのは
簡単です．
これは，プログラム内のすべての定義が相互再帰によって与えられていると考えることができるためです．
このように自由な関数定義が許されている設定では，
本当に無限の大きさをもつリストを作るの際には無限ループになる式を書くだけですが，
そのリストの先頭の有限個の要素だけが必要なら有限の時間で結果を得られるように注意する必要があります．
Haskellプログラマはそういった点に気をつけながらプログラムを書く方法を学習します．
Coqでは，関数やデータを定義する際にはこのような自由放任主義が通用しません．

前の章でカリーハワード同型について時間をかけて説明してきたように，
証明は関数型プログラムと見なすことができます．
この考えのもとでは，無限ループは，
それが意図的であってもそうでなくても，ひどい結果をもたらします．
もしCoqがHaskellのような定義の柔軟さを許すならば，
無限にループするプログラムを記述することができてしまい，
それによって任意の命題が証明できることになるでしょう．
つまり，CICに一般再帰を追加すると「矛盾」が生じてしまうのです．
たとえば，任意の命題 [P] に対して，
次の再帰関数が定義できたとしましょう：
[[
Fixpoint bad (u : unit) : P := bad u.
]]

この関数を使えば [P] 型をもつ式 [bad tt] を作ることができるので，
命題 [P] が証明できてしまいます．

あらゆる入力に対する停止性が強く望まれるようなアルゴリズム的な配慮もあります．
これまで，[reflexivity] のようなタクティックがどのようにして項同士を比較し，
計算規則のもとで等価性を判定するかを見てきました．
明示的な証明ステップを経るまでもなく，
再帰的でパターンマッチを利用した関数の呼び出しは自動的に簡約されます．
そういった利点を維持しながら，停止しないプログラムも書けるようにするのは簡単ではありません．
そこにはチューリング機械の停止性問題が立ちはだかることでしょう．

1つの解決方法は，停止しない可能性があることを表すような型を使うことです．
たとえば，「非停止モナド」を作ってその内側に一般再帰のプログラムを閉じ込めることも考えられます．この手法のいくつかは7章で解説しますが，非常に煩雑な方法なのでできれば避けたいところです．

幸運なことにCoqには遅延データ構造のクラスが特別に用意されていて，
Haskellで使われている多くの例はこのクラスに含まれています．
これが%\index{余帰納型}%余帰納型と呼ばれる仕組みであり，本章の主題です．
*)

(**
(** * Computing with Infinite Data *)
*)
(** * 無限の大きさをもつデータを使った計算 *)

(**
(** Let us begin with the most basic type of infinite data, _streams_, or lazy lists.%\index{Vernacular commands!CoInductive}% *)
*)
(**
まずは最も基本的な無限データである「ストリーム」(遅延リスト) を考えましょう．%\index{Vernacular commands!CoInductive}%
*)

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

(* begin hide *)
(* begin thide *)
CoInductive evilStream := Nil.
(* end thide *)
(* end hide *)

(**
(** The definition is surprisingly simple.  Starting from the definition of [list], we just need to change the keyword [Inductive] to [CoInductive].  We could have left a [Nil] constructor in our definition, but we will leave it out to force all of our streams to be infinite.

   How do we write down a stream constant?  Obviously, simple application of constructors is not good enough, since we could only denote finite objects that way.  Rather, whereas recursive definitions were necessary to _use_ values of recursive inductive types effectively, here we find that we need%\index{co-recursive definitions}% _co-recursive definitions_ to _build_ values of co-inductive types effectively.

   We can define a stream consisting only of zeroes.%\index{Vernacular commands!CoFixpoint}% *)
*)
(**
この定義は驚くほど単純です．
[list]の定義の[Inductive]というキーワードを[CoInductive]に変えただけです．
[Nil]構成子を定義に残すこともできましたが，
無限の大きさをもつストリームしか表現できないようにするために外すことにします．

ストリーム型の値を書き下すにはどうすればよいでしょう？
単純に構成子を適用していくだけでは有限の大きさのデータしか表現できないということは明らかです．
(* より正確に言えば，*)
再帰的な帰納型の値を有限時間で「消費」するために
再帰的な定義を使うのと同じように，
余帰納型の値を有限時間で「生産」するためには，
%\index{余再帰的定義}%余再帰的定義が必要になるということです．

0しか含まないようなストリームは次のように定義できます．%\index{Vernacular commands!CoFixpoint}% 

*)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(* EX: Define a stream that alternates between [true] and [false]. *)
(* begin thide *)

(**
(** We can also define a stream that alternates between [true] and [false]. *)
*)
(** [true]と[false]が交互に現れるストリームは次のように定義できます． *)

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.
(* end thide *)

(**
(** Co-inductive values are fair game as arguments to recursive functions, and we can use that fact to write a function to take a finite approximation of a stream. *)
*)
(** 
余帰納的な値を再帰的関数の引数として与えることにより，
ストリームに対する有限の近似を求める関数を定義することができます．
*)

(* EX: Define a function to calculate a finite approximation of a stream, to a particular length. *)
(* begin thide *)

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.
(** %\vspace{-.15in}% [[
     = 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: nil
     : list nat
     ]]
     *)

Eval simpl in approx trues_falses 10.
(** %\vspace{-.15in}% [[
     = true
       :: false
          :: true
             :: false
                :: true :: false :: true :: false :: true :: false :: nil
     : list bool
      ]]
*)

(* end thide *)

(* begin hide *)
(* begin thide *)
Definition looper := 0.
(* end thide *)
(* end hide *)

(**
(** So far, it looks like co-inductive types might be a magic bullet, allowing us to import all of the Haskeller's usual tricks.  However, there are important restrictions that are dual to the restrictions on the use of inductive types.  Fixpoints _consume_ values of inductive types, with restrictions on which _arguments_ may be passed in recursive calls.  Dually, co-fixpoints _produce_ values of co-inductive types, with restrictions on what may be done with the _results_ of co-recursive calls.

The restriction for co-inductive types shows up as the%\index{guardedness condition}% _guardedness condition_.  First, consider this stream definition, which would be legal in Haskell.
[[
CoFixpoint looper : stream nat := looper.
]]

<<
Error:
Recursive definition of looper is ill-formed.
In environment
looper : stream nat

unguarded recursive call in "looper"
>>

The rule we have run afoul of here is that _every co-recursive call must be guarded by a constructor_; that is, every co-recursive call must be a direct argument to a constructor of the co-inductive type we are generating.  It is a good thing that this rule is enforced.  If the definition of [looper] were accepted, our [approx] function would run forever when passed [looper], and we would have fallen into inconsistency.

Some familiar functions are easy to write in co-recursive fashion. *)
*)
(**
これまでの説明では，
余帰納型はまるで魔法の仕組みのようであり，
Haskellユーザが使っていたすべての技法がCoqでも使えると感じてしまうでしょう．
しかしながら，帰納型を利用するときの制約と双対となる重要な制約があります．
[Fixpoint]によって定義される関数が帰納型の値を「消費」するとき，
再帰呼び出しの際に渡される「引数」に制約があります．
これとは双対的に，
[CoFixpoint]によって定義される関数が余帰納型の値を「生産」するとき，
余再帰呼び出しの「結果」の使われ方に制約があるのです．

この余帰納型に対する制約は%\index{ガード条件}%「ガード条件」として現れます．
まず，Haskellでは問題なく記述できる次の定義を考えましょう．

[[
CoFixpoint looper : stream nat := looper.
]]

<<
Error:
Recursive definition of looper is ill-formed.
In environment
looper : stream nat

unguarded recursive call in "looper"
>>

ここで違反している規則は「すべての余再帰呼び出しは構成子によってガードされていなければならない」というものです．
つまり，すべての余再帰呼び出しは，作りたい余帰納型の構成子の直接的な引数になっていなければなりません．
この規則を強要するのはよいことです．
もし，この[looper]の定義が許されるとすると，
[approx]関数の引数として[looper]を渡すことで無限に実行されてしまい，
矛盾に陥ってしまうでしょう．

お馴染みの関数を余再帰的に書くことも簡単です．
*)

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

(* begin hide *)
(* begin thide *)
Definition filter := 0.
(* end thide *)
(* end hide *)

(**
(** This code is a literal copy of that for the list [map] function, with the [nil] case removed and [Fixpoint] changed to [CoFixpoint].  Many other standard functions on lazy data structures can be implemented just as easily.  Some, like [filter], cannot be implemented.  Since the predicate passed to [filter] may reject every element of the stream, we cannot satisfy the guardedness condition.

   The implications of the condition can be subtle.  To illustrate how, we start off with another co-recursive function definition that _is_ legal.  The function [interleave] takes two streams and produces a new stream that alternates between their elements. *)
*)
(** 
このコードはリストに対する[map]関数をほぼそのまま写したもので，
[nil]の場合を削除して[Fixpoint]を[CoFixpoint]に変えただけです．
ストリームを扱う他の多くの標準的な関数も簡単に定義できます．
一方，[filter]のように定義できない関数もあります．
[filter]関数に渡される述語がストリームのすべての要素をふるい落としてしまう可能性もあるので，
ガード条件が満たされません．

この条件の扱いには慎重さを必要とすることがあります．
それを確認するために，まずは「合法」とされる別の余再帰関数の定義を見てみましょう．
次の[interleave]関数は2つのストリームを入力として，
それらの要素を交互に並べた1つのストリームを返す関数です．
*)

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(**
(** Now say we want to write a weird stuttering version of [map] that repeats elements in a particular way, based on interleaving. *)
*)
(**
ここで，ちょっと変わった[map]関数を考えてみましょう．
[interleave]関数を使って
特定の方法で要素を繰り返しながらストリームを生成する関数です．
*)

Section map'.
  Variables A B : Type.
  Variable f : A -> B.
 
(* begin thide *)
(**
  (** %\vspace{-.15in}%[[
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
    ]]
    %\vspace{-.15in}%We get another error message about an unguarded recursive call. *)
*)
  (** %\vspace{-.15in}%[[
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
    ]]
    %\vspace{-.15in}%これを入力すると，再帰呼出しがガード条件に違反していることを指摘するエラーメッセージが表示されます． *)

End map'.

(** 
(** What is going wrong here?  Imagine that, instead of [interleave], we had called some other, less well-behaved function on streams.  Here is one simpler example demonstrating the essential pitfall.  We start by defining a standard function for taking the tail of a stream.  Since streams are infinite, this operation is total. *)
*)
(**
どこが間違っていたのでしょう？
仮に，[interleave]関数の代わりに
ストリーム上の別の不適切な関数が呼ばれていた場合を考えてみましょう．
このような関数呼出しが本質的な危険となるということを説明するために，
更に簡単な例を用意しました．
まずはストリームに対する標準的な関数である[tail]関数を定義します．
リストと違ってストリームの長さは常に無限であるため，
この関数は全域関数です．
*)

Definition tl A (s : stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

(**
(** Coq rejects the following definition that uses [tl].
[[
CoFixpoint bad : stream nat := tl (Cons 0 bad).
]]

Imagine that Coq had accepted our definition, and consider how we might evaluate [approx bad 1].  We would be trying to calculate the first element in the stream [bad].  However, it is not hard to see that the definition of [bad] "begs the question": unfolding the definition of [tl], we see that we essentially say "define [bad] to equal itself"!  Of course such an equation admits no single well-defined solution, which does not fit well with the determinism of Gallina reduction.

Coq's complete rule for co-recursive definitions includes not just the basic guardedness condition, but also a requirement about where co-recursive calls may occur.  In particular, a co-recursive call must be a direct argument to a constructor, _nested only inside of other constructor calls or [fun] or [match] expressions_.  In the definition of [bad], we erroneously nested the co-recursive call inside a call to [tl], and we nested inside a call to [interleave] in the definition of [map'].

Coq helps the user out a little by performing the guardedness check after using computation to simplify terms.  For instance, any co-recursive function definition can be expanded by inserting extra calls to an identity function, and this change preserves guardedness.  However, in other cases computational simplification can reveal why definitions are dangerous.  Consider what happens when we inline the definition of [tl] in [bad]:
[[
CoFixpoint bad : stream nat := bad.
]]
This is the same looping definition we rejected earlier.  A similar inlining process reveals an alternate view on our failed definition of [map']:
[[
CoFixpoint map' (s : stream A) : stream B :=
  match s with
    | Cons h t => Cons (f h) (Cons (f h) (interleave (map' t) (map' t)))
  end.
]]
Clearly in this case the [map'] calls are not immediate arguments to constructors, so we violate the guardedness condition. *)
*)
(**
この[tl]関数を使って次のようなストリームを定義しようとしても，
Coqは受け入れてくれません．
[[
CoFixpoint bad : stream nat := tl (Cons 0 bad).
]]

仮にCoqがこの定義を受け入れたとして，
[approx bad 1]という式を評価しようとした場合を考えましょう．
この式は，[bad]ストリームの最初の要素を取り出そうとしています．
しかしながら，この[bad]の定義が問題を引き起こすことは容易に想像できます．
[tl]関数の定義を展開すると，
[bad]が結局[bad]自身と等しくなるように定義されていることがわかります．
もちろん，
[bad]が[bad]と等しいというだけの定義では唯一の値を特定することはできないので，
Gallina簡約の決定性に反する結果となります．

Coqにおける余再帰定義の完全な規則には，
基本的なガード条件だけではなく，
余再帰呼出しがどこに現れるべきかという制約もあります．
具体的には，
余再帰呼出しは構成子の直接の引数でなければならず，
その外側には「別の構成子」「[fun]」「[match]式」以外が現れてはいけません．
先ほどの[bad]の定義では，余再帰呼出しの外側に[tl]の関数呼出しがあり，
[map']の定義では，
余再帰呼出しの外側に[interleave]の関数呼出しがあるため，
どちらもエラーになります．

Coqには，構文的な制約を緩和するために，
項を簡約してからガード条件を検査するという手法を採用しています．
たとえば，余再帰的定義の外側で恒等関数が呼び出されていたとしてもガード条件には影響しません．
しかしながら，
それ以外の場合には項の簡約によってなぜ定義に問題があるのかがよくわかります．
先ほどの[bad]の例において[tl]の定義をインライン展開してみましょう．

[[
CoFixpoint bad : stream nat := bad.
]]
これは以前の[looper]の例と同じで適切な定義ではありません．
エラーになってしまった[map']の定義においても同様にインライン展開すると
次のようになります．
[[
CoFixpoint map' (s : stream A) : stream B :=
  match s with
    | Cons h t => Cons (f h) (Cons (f h) (interleave (map' t) (map' t)))
  end.
]]
この場合は明らかに[map']関数の呼出しが構成子の直接の引数になっていないため，
ガード条件に違反していることがわかります．
*)
(* end thide *)

(**
(** A more interesting question is why that condition is the right one.  We can make an intuitive argument that the original [map'] definition is perfectly reasonable and denotes a well-understood transformation on streams, such that every output would behave properly with [approx].  The guardedness condition is an example of a syntactic check for%\index{productivity}% _productivity_ of co-recursive definitions.  A productive definition can be thought of as one whose outputs can be forced in finite time to any finite approximation level, as with [approx].  If we replaced the guardedness condition with more involved checks, we might be able to detect and allow a broader range of productive definitions.  However, mistakes in these checks could cause inconsistency, and programmers would need to understand the new, more complex checks.  Coq's design strikes a balance between consistency and simplicity with its choice of guard condition, though we can imagine other worthwhile balances being struck, too. *)
*)
(**
興味深いのはなぜこの条件が正しいのかということです．
直観的には最初に示した[map']関数の定義はとても自然で，
ストリーム上の変換としても理解しやすいものですし，
[approx]に渡しても適切に実行されそうに見えるでしょう．
Coqにおけるガード条件は，
余再帰的定義の「生産的であるか」%\index{productivity}%を構文的に検査しているだけです．
生産的な定義とは，[approx]のような関数を使ったどんな有限の近似においても
有限の時間で出力が得られるものであると考えてかまいません．
ガード条件にもっと複雑な検査を追加すれば，
より広い範囲の生産的な定義を扱うこともできるかもしれません．
しかしながら，
そのような検査でのエラーは一貫性のないものになるかもしれませんし，
プログラマがその新しい複雑な検査を理解する必要が出てきてしまいます．
現在のCoqの設計では，
一貫性とわかりやすさのバランスを重視してガード条件を定めていますし，
他にも抑えておきたい重要なバランスもあるでしょう．
*)

(**
(** * Infinite Proofs *)
*)
(** * 無限の大きさをもつ証明 *)

(**
(** Let us say we want to give two different definitions of a stream of all ones, and then we want to prove that they are equivalent. *)
*)
(**
すべての要素が1であるストリームを異なる二つの方法で定義してみましょう．
あとでこれらが等しいことを証明します．
*)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

(**
(** The obvious statement of the equality is this: *)
*)
(** 単純に考えればこれらが等しいことを示す言明は次の通りです．*)

Theorem ones_eq : ones = ones'.

(* begin hide *)
(* begin thide *)
Definition foo := @eq.
(* end thide *)
(* end hide *)

(**
  (** However, faced with the initial subgoal, it is not at all clear how this theorem can be proved.  In fact, it is unprovable.  The [eq] predicate that we use is fundamentally limited to equalities that can be demonstrated by finite, syntactic arguments.  To prove this equivalence, we will need to introduce a new relation. *)
*)
  (**
しかしながら，
最初のゴールを見ても
この定理をどう証明すればいいのか全くわかりません．
実際，この言明は証明できません．
ここで使われている[eq]という述語は基本的に，
有限回の構文的な比較によって証明できるような等価性に限定されています．
ストリームのような値の等価性を示すには，新たな関係を導入する必要があるのです．
*)
(* begin thide *)

Abort.

(**
(** Co-inductive datatypes make sense by analogy from Haskell.  What we need now is a _co-inductive proposition_.  That is, we want to define a proposition whose proofs may be infinite, subject to the guardedness condition.  The idea of infinite proofs does not show up in usual mathematics, but it can be very useful (unsurprisingly) for reasoning about infinite data structures.  Besides examples from Haskell, infinite data and proofs will also turn out to be useful for modelling inherently infinite mathematical objects, like program executions.

We are ready for our first %\index{co-inductive predicates}%co-inductive predicate. *)
*)
(**
余帰納的データ型はHaskellとの対比によって理解できます．
いま必要なのは「余帰納的命題」です．
つまり，
ガード条件に従って構成された無限の大きさになりうる証明をもつような命題を
定義する必要があるのです．
この考え方は通常の数学で出てくることはありませんが，
無限の大きさをもつ構造を考えるためには（当然ながら）とても有用です．
Haskellの例の他にも，無限の大きさをもつデータや証明は，
プログラム実行などの
本質的に無限の大きさをもつ数学的対象を扱う際にもにも有用であることがわかるでしょう．

%\index{余帰納的述語}%余帰納的述語の最初の例がこちらです．
*)

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

(**
(** We say that two streams are equal if and only if they have the same heads and their tails are equal.  We use the normal finite-syntactic equality for the heads, and we refer to our new equality recursively for the tails.

We can try restating the theorem with [stream_eq]. *)
*)
(**
二つのストリームが等しいということを，
先頭が同じで残りのストリームが等しいと定義します．
先頭は通常の有限回の構文的な比較による等価性を使い，
残りのストリームは新たに定義している等価性を再帰的に使います．

それでは，
当初の目標だった等式について
[stream_eq]を使った定理とし，
改めて証明してみましょう．
*)

Theorem ones_eq : stream_eq ones ones'.
(**
  (** Coq does not support tactical co-inductive proofs as well as it supports tactical inductive proofs.  The usual starting point is the [cofix] tactic, which asks to structure this proof as a co-fixpoint. *)
*)
  (**
帰納的証明のときとは異なり，
Coqには余帰納的証明を直接支援するタクティックが提供されていません．
通常最初に使うタクティックは[cofix]で，
このタクティックは余不動点として証明を構成するためのものです．
*)

  cofix ones_eq.
(** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones ones'
 
   ]]

   なんだか思った以上に簡単に証明ができそうですね！
*)

  assumption.
(*
  (** <<
Proof completed.
>>

  Unfortunately, we are due for some disappointment in our victory lap.
  [[
Qed.
]]

<<
Error:
Recursive definition of ones_eq is ill-formed.

In environment
ones_eq : stream_eq ones ones'

unguarded recursive call in "ones_eq"
>>

Via the Curry-Howard correspondence, the same guardedness condition applies to our co-inductive proofs as to our co-inductive data structures.  We should be grateful that this proof is rejected, because, if it were not, the same proof structure could be used to prove any co-inductive theorem vacuously, by direct appeal to itself!

Thinking about how Coq would generate a proof term from the proof script above, we see that the problem is that we are violating the guardedness condition.  During our proofs, Coq can help us check whether we have yet gone wrong in this way.  We can run the command [Guarded] in any context to see if it is possible to finish the proof in a way that will yield a properly guarded proof term.%\index{Vernacular commands!Guarded}%
     [[
Guarded.
]]

     Running [Guarded] here gives us the same error message that we got when we tried to run [Qed].  In larger proofs, [Guarded] can be helpful in detecting problems _before_ we think we are ready to run [Qed].
     
     We need to start the co-induction by applying [stream_eq]'s constructor.  To do that, we need to know that both arguments to the predicate are [Cons]es.  Informally, this is trivial, but [simpl] is not able to help us. *)
*)
  (** <<
Proof completed.
>>

  残念なことに，証明終了のウイニングランでは失望が待っています．
  [[
Qed.
]]

<<
Error:
Recursive definition of ones_eq is ill-formed.

In environment
ones_eq : stream_eq ones ones'

unguarded recursive call in "ones_eq"
>>

カリー・ハワード同型対応を考慮すれば，余帰納的データ構造に対するガード条件は余帰納的証明にも適用されるはずです．
上記の証明が受け入れられないのはむしろ歓迎すべきことです．
なぜなら，仮にこの証明が通ってしまうとしたら，
同じような証明手順によってあらゆる余帰納的な定理が証明できてしまうからです．

この証明手順からどのように証明項が生成されるかを考えてみれば，
ガード条件に違反しようとしていることが問題であることがわかります．
Coqでは，証明の途中に，ガード条件に反するようなおかしな証明をしていないかどうか検査する機能が提供されています．
[[Guarded]]コマンドを使うことで，
適切にガードされた証明項を作るように証明を終えることができるかどうかを
いつでも確認することができます%\index{Vernacular commands!Guarded}%．

     [[
Guarded.
]]

ここで [Guarded] を使うと [Qed] で証明を終えようとしたときと同じエラーメッセージが得られます． もっと大きな証明をするときには [Guarded] コマンドは有用で，
[Qed] で証明が終えられる状態であるかを考える前に問題を検出できます．

この証明では，まず [stream_eq] 構成子の規則を適用することによって余帰納的証明を始める必要があります．そのためには，[stream_eq]の2つの引数が[Cons]の形であること知っておかないといけません．それは直感的には当たり前のことですが，[simpl]タクティクは何の役にも立ちません．
*)

  Undo.
  simpl.
(*
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones ones'
 
   ]]

   It turns out that we are best served by proving an auxiliary lemma. *)
*)
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones ones'
 
   ]]

   これを解決するために，あらかじめ補題を1つ証明しておくのが最善の方法であることがわかります．
*)

Abort.

(*
(** First, we need to define a function that seems pointless at first glance. *)
*)
(**
まず，一見何の意味もない関数の定義が必要です．
*)

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

(*
(** Next, we need to prove a theorem that seems equally pointless. *)
*)
(** 
次に，同じくらい意味のなさそうな定理を証明する必要があります．
*)

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

(*
(** But, miraculously, this theorem turns out to be just what we needed. *)
*)
(**
しかしながら，奇跡的なことに，この定理が紛れもなく求めていたものであることがわかります．
*)

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.

(*
  (** We can use the theorem to rewrite the two streams. *)
*)
  (**
この定理を使うことで2つのストリームを書き換えることができます．
*)

  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
(*
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (frob ones) (frob ones')
 
   ]]

   Now [simpl] is able to reduce the streams. *)
*)
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (frob ones) (frob ones')
 
   ]]

   今なら [simpl] を使って2つのストリームの式を簡約することができます．
*)

  simpl.
(*
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (Cons 1 ones)
     (Cons 1
        ((cofix map (s : stream nat) : stream nat :=
            match s with
            | Cons h t => Cons (S h) (map t)
            end) zeroes))
 
            ]]

  Note the [cofix] notation for anonymous co-recursion, which is analogous to the [fix] notation we have already seen for recursion.  Since we have exposed the [Cons] structure of each stream, we can apply the constructor of [stream_eq]. *)
*)
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (Cons 1 ones)
     (Cons 1
        ((cofix map (s : stream nat) : stream nat :=
            match s with
            | Cons h t => Cons (S h) (map t)
            end) zeroes))
 
            ]]

  この[cofix]記法は無名余再帰を表していますが，すでに見た再帰を表すための[fix]記法とよく似ています． 今それぞれのストリーム式が [Cons] の形になったので，[stream_eq] 構成子の規則を適用することができます．*)

  constructor.
(*
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones
     ((cofix map (s : stream nat) : stream nat :=
         match s with
         | Cons h t => Cons (S h) (map t)
         end) zeroes)
 
         ]]

  Now, modulo unfolding of the definition of [map], we have matched our assumption. *)
*)
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones
     ((cofix map (s : stream nat) : stream nat :=
         match s with
         | Cons h t => Cons (S h) (map t)
         end) zeroes)
 
         ]]

  ここで，[map]の定義が展開されているかいないかを無視すれば，この帰結は仮定と一致します．
*)

  assumption.
Qed.

(*
(** Why did this silly-looking trick help?  The answer has to do with the constraints placed on Coq's evaluation rules by the need for termination.  The [cofix]-related restriction that foiled our first attempt at using [simpl] is dual to a restriction for [fix].  In particular, an application of an anonymous [fix] only reduces when the top-level structure of the recursive argument is known.  Otherwise, we would be unfolding the recursive definition ad infinitum.

   Fixpoints only reduce when enough is known about the _definitions_ of their arguments.  Dually, co-fixpoints only reduce when enough is known about _how their results will be used_.  In particular, a [cofix] is only expanded when it is the discriminee of a [match].  Rewriting with our superficially silly lemma wrapped new [match]es around the two [cofix]es, triggering reduction.

   If [cofix]es reduced haphazardly, it would be easy to run into infinite loops in evaluation, since we are, after all, building infinite objects.

   One common source of difficulty with co-inductive proofs is bad interaction with standard Coq automation machinery.  If we try to prove [ones_eq'] with automation, like we have in previous inductive proofs, we get an invalid proof. *)
*)
(** 
こんな無意味に見える小技が役に立つのはなぜでしょうか．
その答えは，停止性のためにCoqの評価規則に課された制約と関係しています．
上の例で最初に[simpl]タクティクが働かなかったときの[cofix]の制約は，
[fix]に対する制約と双対の関係になっています．
[fix]で表される無名関数の適用が評価されるのは，
再帰呼び出しの引数の最も外側の構成子がわかったときだけです．
そうしないと再帰的な定義が無限に展開されてしまいます．

[fix]による不動点は「引数の定義」が必要なだけわかったときだけ評価されます．
それとは双対に，
[cofix]による余不動点は「結果がどう使われるか」が必要なだけわかったときだけ評価されます．
[cofix]で表される無名関数が展開されるのは，[match]式の引数として与えられたときだけです．
先ほどの表面的で自明な補題を使って新たな[match]式で2つの[cofix]式を包むことにより，簡約を進めることができます．

最終的に無限の大きさをもつ対象を構成しようとしているので，
もし[cofix]式が行き当たりばったりに簡約されるとしたら，
すぐに無限ループに陥ってしまうことでしょう．

余帰納的証明の難しさの原因としてよく挙げられるのは，
標準のCoqの自動証明機構と相性が悪いという点です．
これまでの帰納的定理の証明と同じような自動証明を[ones'_eq]に対して試みると，
ガードされていない不適切な証明が得られてしまいます．
*)

Theorem ones_eq' : stream_eq ones ones'.
  cofix one_eq'; crush.
  (** %\vspace{-.25in}%[[
  Guarded.
  ]]
  %\vspace{-.25in}%
  *)
Abort.

(*
(** The standard [auto] machinery sees that our goal matches an assumption and so applies that assumption, even though this violates guardedness.  A correct proof strategy for a theorem like this usually starts by [destruct]ing some parameter and running a custom tactic to figure out the first proof rule to apply for each case.  Alternatively, there are tricks that can be played with "hiding" the co-inductive hypothesis.

   %\medskip%

   Must we always be cautious with automation in proofs by co-induction?  Induction seems to have dual versions of the same pitfalls inherent in it, and yet we avoid those pitfalls by encapsulating safe Curry-Howard recursion schemes inside named induction principles.  It turns out that we can usually do the same with%\index{co-induction principles}% _co-induction principles_.  Let us take that tack here, so that we can arrive at an [induction x; crush]-style proof for [ones_eq'].

   An induction principle is parameterized over a predicate characterizing what we mean to prove, _as a function of the inductive fact that we already know_.  Dually, a co-induction principle ought to be parameterized over a predicate characterizing what we mean to prove, _as a function of the arguments to the co-inductive predicate that we are trying to prove_.

   To state a useful principle for [stream_eq], it will be useful first to define the stream head function. *)
*)
(** 
標準的な[auto]タクティクは，帰結に一致する仮定があれば，ガード条件に違反するかどうかに関係なく，その仮定を適用してしまいます．
このような定理を証明する正しい戦略は，まず引数のどれかを[destruct]して場合分けを行い，それぞれの場合について最初に適用できる規則を知るための適切なタクティクを使うことです．あるいは，余帰納的仮定を「隠す」ことで自動証明を進めるという方法もいくつかあります．

   %\medskip%

余帰納法で証明する場合には常に自動証明に注意を払わなければならないのでしょうか．
帰納法でも双対になる同じような罠が存在すると思われますが，
いわゆる帰納法の原理の中に安全なカリー・ハワード再帰スキームを内包することで，その罠を避けています．大抵の場合は「余帰納法の原理」%\index{余帰納法の原理}%を用いて同じことができることがわかります．それでは，[ones_eq']に対して[induction x; crush]形式で証明する方法を考えてみましょう．

帰納的原理は，証明すべき命題を表す述語をパラメータ化した
「すでにわかっている帰納的事実を受け取る関数」として与えられます．
それとは双対に，
余帰納的原理は，
証明すべき命題を表す述語をパラメータ化した
「証明しようとしている余帰納的述語の引数を受け取る関数」として与えられるべきです．

[stream_eq]に対する証明に有用な原理を示すために，ストリームの先頭を取り出す関数を用意しておくと便利です．
*)

Definition hd A (s : stream A) : A :=
  match s with
    | Cons x _ => x
  end.

(*
(** Now we enter a section for the co-induction principle, based on %\index{Park's principle}%Park's principle as introduced in a tutorial by Gim%\'%enez%~\cite{IT}%. *)
*)
(**
いよいよ余帰納法の原理を示す[Section]に入ります．
これは，Gim%\'%enezによるチュートリアル%~\cite{IT}%で紹介されている%\index{Parkの原理}%Parkの原理を基にしています．
*)

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

(*
  (** This relation generalizes the theorem we want to prove, defining a set of pairs of streams that we must eventually prove contains the particular pair we care about. *)
*)
  (**
この関係 [R] は証明したい定理を一般化したものを表し，
注目している特定のストリーム対が最終的に含まれるように対の集合を定義していきます．
*)

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

(*
  (** Two hypotheses characterize what makes a good choice of [R]: it enforces equality of stream heads, and it is %``%#<i>#hereditary#</i>#%''% in the sense that an [R] stream pair passes on "[R]-ness" to its tails.  An established technical term for such a relation is%\index{bisimulation}% _bisimulation_. *)
*)
  (** 
この2つの仮定は関係[R]が適切に定義されていることを表します．
1つめの仮定では，ストリームの先頭が互いに等しいことを強制し，
2つめの仮定では，ストリーム同士の[R]という関係が後続のストリームに%``%#<i>#遺伝#</i>#%''%することを表しています．
専門用語では，このような関係は%\index{bisimulation}%「双模倣」と呼ばれます．
*)

(*
  (** Now it is straightforward to prove the principle, which says that any stream pair in [R] is equal.  The reader may wish to step through the proof script to see what is going on. *)
*)
  (** 
余帰納法の原理を示すのは簡単です．
その原理の主張は，[R] で関係付けられるストリーム対は必ず [stream_eq] の意味で等しい，というものです．
この証明スクリプトを順に追いながら何が起こっているかを見てみましょう．
*)

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix stream_eq_coind; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

(*
(** To see why this proof is guarded, we can print it and verify that the one co-recursive call is an immediate argument to a constructor. *)
*)
(**
この証明がガード条件を満たしていることは，
その証明項を表示し，
余再帰呼出しが構成子の直接の引数になっていることを確認すればわかります．
*)

Print stream_eq_coind.

(*
(** We omit the output and proceed to proving [ones_eq''] again.  The only bit of ingenuity is in choosing [R], and in this case the most restrictive predicate works. *)
*)
(**
出力は省略することとして，先ほどの定理を [ones_eq''] として証明してみましょう．
適切な [R] を選ぶのにちょっとした工夫が必要ですが，
この場合はもっとも制限された述語を選べばうまく証明ができます．
*)

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.

(*
(** Note that this proof achieves the proper reduction behavior via [hd] and [tl], rather than [frob] as in the last proof.  All three functions pattern match on their arguments, catalyzing computation steps.

   Compared to the inductive proofs that we are used to, it still seems unsatisfactory that we had to write out a choice of [R] in the last proof.  An alternate is to capture a common pattern of co-recursion in a more specialized co-induction principle.  For the current example, that pattern is: prove [stream_eq s1 s2] where [s1] and [s2] are defined as their own tails. *)
*)
(**
この証明では，以前の証明で使った[frob]の代わりに[hd]と[tl]を通じて適切な簡約を実現しています．これらの3つの関数は，いずれも引数に対してパターンマッチすることにより，計算を進める触媒の役割を果たしています．

これまでの帰納法による証明と比べると，この余帰納法による証明では関係[R]をわざわざ書き下さなければならず，依然として不満があるかもしれません．
そこで，別の手段として，
余帰納法の原理の特別な場合として余再帰に共通するパターンを見つけることを考えます．
今の例では，そのパターンは「自分自身が後続することで定義されているような[s1]と[s2]に対して[stream_eq s1 s2]を証明する」というものです．
*)

Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd : hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.

(*
  (** The proof of the principle includes a choice of [R], so that we no longer need to make such choices thereafter. *)
*)
  (**
この帰納法の原理では，関係[R]を特別な場合に限定しているため，
使う際にはその関係を指定する必要がありません．
*)

  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2)); crush.
  Qed.
End stream_eq_loop.

Theorem ones_eq''' : stream_eq ones ones'.
  apply stream_eq_loop; crush.
Qed.
(* end thide *)

(*
(** Let us put [stream_eq_coind] through its paces a bit more, considering two different ways to compute infinite streams of all factorial values.  First, we import the [fact] factorial function from the standard library. *)
*)
(**
[stream_eq_coind]より一歩先に進んだ余帰納法の原理を理解するために，
自然数の階乗を無限に並べたストリーム(階乗ストリーム)を計算する2つの方法を考えましょう．
まず，階乗を計算する関数[fact]を標準ライブラリから読み込みます．
*)

Require Import Arith.
Print fact.
(** %\vspace{-.15in}%[[
fact = 
fix fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n0 => S n0 * fact n0
  end
     : nat -> nat
]]
*)

(*
(** The simplest way to compute the factorial stream involves calling [fact] afresh at each position. *)
*)
(**
階乗ストリームを計算するもっとも単純な方法は，
要素ごとに[fact]関数を呼ぶことです．
*)

CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

(*
(** A more clever, optimized method maintains an accumulator of the previous factorial, so that each new entry can be computed with a single multiplication. *)
*)
(**
最適化されたより賢い方法は，
直前の階乗の値を記憶しつつ，要素ごとに1度の掛け算だけで計算する方法です．
*)

CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

(*
(** We can verify that the streams are equal up to particular finite bounds. *)
*)
(**
2つのストリームが有限個までは等しいことを確認してみましょう．
*)

Eval simpl in approx fact_iter 5.
(** %\vspace{-.15in}%[[
     = 1 :: 2 :: 6 :: 24 :: 120 :: nil
     : list nat
]]
*)
Eval simpl in approx fact_slow 5.
(*
(** %\vspace{-.15in}%[[
     = 1 :: 2 :: 6 :: 24 :: 120 :: nil
     : list nat
]]

Now, to prove that the two versions are equivalent, it is helpful to prove (and add as a proof hint) a quick lemma about the computational behavior of [fact].  (I intentionally skip explaining its proof at this point.) *)
*)
(** %\vspace{-.15in}%[[
     = 1 :: 2 :: 6 :: 24 :: 120 :: nil
     : list nat
]]

2つのストリームが完全に等しいことを証明するために，
[fact]関数による計算についての簡単な補題を証明してヒントとして追加します．
(ここでは敢えて証明の解説はしません．)
*)

(* begin thide *)
Lemma fact_def : forall x n,
  fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
  simpl; intros; f_equal; ring.
Qed.

Hint Resolve fact_def.

(*
(** With the hint added, it is easy to prove an auxiliary lemma relating [fact_iter'] and [fact_slow'].  The key bit of ingenuity is introduction of an existential quantifier for the shared parameter [n]. *)
*)
(**
このヒントを加えると，
[fact_iter']と[fact_slow']を関連づける補題の証明がしやすくなります．
存在量化子で導入された共通の変数[n]を使うのがミソです．
*)

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intro; apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n)
    /\ s2 = fact_slow' n)); crush; eauto.
Qed.

(*
(** The final theorem is a direct corollary of [fact_eq']. *)
*)
(**
最終的な定理は[fact_eq']の系として簡単に得られます．
*)

Theorem fact_eq : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

(*
(** As in the case of [ones_eq'], we may be unsatisfied that we needed to write down a choice of [R] that seems to duplicate information already present in a lemma statement.  We can facilitate a simpler proof by defining a co-induction principle specialized to goals that begin with single universal quantifiers, and the strategy can be extended in a straightforward way to principles for other counts of quantifiers.  (Our [stream_eq_loop] principle is effectively the instantiation of this technique to zero quantifiers.) *)
*)
(**
[ones_eq']の場合には，
すでに補題の記述にあるものをわざわざ改めて[R]として書き下さなければならないことが不満だったかもしれません．
一般的な場合でより簡潔に証明できるように，
一つの全称量化子で始まる帰結に特化した余帰納法の原理を定義してみましょう．
この原理から複数個の量化子を含む余帰納法の原理へ拡張することも簡単です．
(先ほどの[stream_eq_loop]という余帰納法の原理は，量化子が0個の特殊な場合においてこの手法を適用したものです．)
*)


Section stream_eq_onequant.
  Variables A B : Type.
(*
  (** We have the types [A], the domain of the one quantifier; and [B], the type of data found in the streams. *)
*)
  (**
量化子で束縛される変数の型を[A]，ストリームの要素の型を[B]とします．
*)

  Variables f g : A -> stream B.
(*
  (** The two streams we compare must be of the forms [f x] and [g x], for some shared [x].  Note that this falls out naturally when [x] is a shared universally quantified variable in a lemma statement. *)
*)
  (**
比較しようとしている2つのストリームは，変数[x]を共有して[f x]や[g x]という形で表されるはずです．拡張された余帰納法の原理を使う補題では，この変数[x]が全称量化子として現れることになります．
*)

  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.
(*
  (** These conditions are inspired by the bisimulation requirements, with a more general version of the [R] choice we made for [fact_eq'] inlined into the hypotheses of [stream_eq_coind]. *)
*)
  (**
これらの条件は双模倣の定義に触発されたもので，[fact_eq']を証明するために使った[R]を一般化し，[stream_eq_coind]の仮定の部分に展開することで得られます．
*)

  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
    intro; apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x)); crush; eauto.
  Qed.
End stream_eq_onequant.

Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  apply stream_eq_onequant; crush; eauto.
Qed.

(*
(** We have arrived at one of our customary automated proofs, thanks to the new principle. *)
*)
(** 
新しい余帰納法の原理のおかげで，これまで行ってきたような通常の自動証明にたどり着きました．
*)
(* end thide *)


(** * Simple Modeling of Non-Terminating Programs *)

(*
(** We close the chapter with a quick motivating example for more complex uses of co-inductive types.  We will define a co-inductive semantics for a simple imperative programming language and use that semantics to prove the correctness of a trivial optimization that removes spurious additions by 0.  We follow the technique of%\index{co-inductive big-step operational semantics}% _co-inductive big-step operational semantics_ %\cite{BigStep}%.

   We define a suggestive synonym for [nat], as we will consider programs over infinitely many variables, represented as [nat]s. *)
*)
(** 
最後に，役に立ちそうな例を通じて余帰納的型の複雑な使い方を紹介します．
ここでは，単純な手続き型プログラミング言語の余帰納的意味論を定義し，
その意味論の下で，
0を加算するという無駄な処理を取り除く自明な最適化の正当性を証明してみましょう．
%\index{余帰納的ビッグステップ操作的意味論}% 「余帰納的ビッグステップ操作的意味論」 %\cite{BigStep}% に従って進めていきます．

まず，この言語におけるプログラムでは，無限個の変数を扱えるようにする必要があるので，それを[nat]のわかりやすい別名として用意します．
*)

Definition var := nat.

(**
次に，変数から値への写像の型[vars]を定義します．
ある変数から値への対応を写像に上書きする関数[set]を定義するには，
自然数同士を比較する標準ライブラリ関数[beg_nat]を使います．
*)

Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

(*
(** We define a simple arithmetic expression language with variables, and we give it a semantics via an interpreter. *)
*)
(**
変数を含む算術式を表す言語を定義して，インタプリタ関数によってその意味論を与えます．
*)

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => vs v
    | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.

(*
(** Finally, we define a language of commands.  It includes variable assignment, sequencing, and a <<while>> form that repeats as long as its test expression evaluates to a nonzero value. *)
*)
(** 
最後に，命令言語を定義します．
命令の構文として，変数への代入，命令の連結，
条件式が0でない値をもつ限り繰り返す<<while>>文があります．
*)

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

(*
(** We could define an inductive relation to characterize the results of command evaluation.  However, such a relation would not capture _nonterminating_ executions.  With a co-inductive relation, we can capture both cases.  The parameters of the relation are an initial state, a command, and a final state.  A program that does not terminate in a particular initial state is related to _any_ final state.  For more realistic languages than this one, it is often possible for programs to _crash_, in which case a semantics would generally relate their executions to no final states; so relating safely non-terminating programs to all final states provides a crucial distinction. *)
*)
(**
命令に対する実行結果を帰納的関係によって特徴づけることもできるかもしれません．
しかしながら，そのように定義された関係では「停止しない実行」を表現することはできません．
余帰納的関係を使えば，停止する場合もしない場合も両方表現することができます．
その関係は，初期状態と命令と最終状態の三項関係によって与えられます．
ある初期状態から停止しないプログラムは「あらゆる」最終状態に関係づけられるように定義します．
この言語より現実的な言語では，プログラムが予期せず停止することもよくあるでしょう．
一般的に，そういったプログラムについてはどんな最終状態にも関係づけられないように意味論を定義します．
予期しない停止と明確に区別するためには，安全で停止しないプログラムにすべての最終状態を関連づけることはとても重要なことです．
*)

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  -> evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  -> evalCmd vs1 c vs2
  -> evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3.

(*
(** Having learned our lesson in the last section, before proceeding, we build a co-induction principle for [evalCmd]. *)
*)
(**
先に進む前に，前節で学習したように [evalCmd] に対する余帰納法の原理を準備します．
*)

Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

(*
  (** The proof is routine.  We make use of a form of %\index{tactics!destruct}%[destruct] that takes an%\index{intro pattern}% _intro pattern_ in an [as] clause.  These patterns control how deeply we break apart the components of an inductive value, and we refer the reader to the Coq manual for more details. *)
*)
  (** 
証明は簡単です．
[as]句として%\index{イントロパターン}%イントロパターンを用いた[destruct]タクティクを利用します．
このパターンを使うと帰納的な値を深いところまで分解することができます．
詳しくはCoqのマニュアルをご覧ください．
*)

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix evalCmd_coind; intros; destruct c.
    rewrite (AssignCase H); constructor.
    destruct (SeqCase H) as [? [? ?]]; econstructor; eauto.
    destruct (WhileCase H) as [[? ?] | [? [? [? ?]]]]; subst; econstructor; eauto.
  Qed.
End evalCmd_coind.

(*
(** Now that we have a co-induction principle, we should use it to prove something!  Our example is a trivial program optimizer that finds places to replace [0 + e] with [e]. *)
*)
(**
余帰納法の原理を得たからには，これを使って何か証明したいですよね！
今回は例として[0 + e]を見つけて[e]に置き換える自明なプログラム最適化器を考えます．
*)

Fixpoint optExp (e : exp) : exp :=
  match e with
    | Plus (Const 0) e => optExp e
    | Plus e1 e2 => Plus (optExp e1) (optExp e2)
    | _ => e
  end.

Fixpoint optCmd (c : cmd) : cmd :=
  match c with
    | Assign v e => Assign v (optExp e)
    | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
    | While e c => While (optExp e) (optCmd c)
  end.

(*
(** Before proving correctness of [optCmd], we prove a lemma about [optExp].  This is where we have to do the most work, choosing pattern match opportunities automatically. *)
*)
(** 
[optCmd]関数の正当性を証明する前に，[optExp]に関する補題を証明しましょう．
この部分はパターンマッチを自動的に選ぶというすべきことが最も多いところです．
*)

(* begin thide *)
Lemma optExp_correct : forall vs e, evalExp vs (optExp e) = evalExp vs e.
  induction e; crush;
    repeat (match goal with
              | [ |- context[match ?E with Const _ => _ | _ => _ end] ] => destruct E
              | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
            end; crush).
Qed.

Hint Rewrite optExp_correct.

(*
(** The final theorem is easy to establish, using our co-induction principle and a bit of Ltac smarts that we leave unexplained for now.  Curious readers can consult the Coq manual, or wait for the later chapters of this book about proof automation.  At a high level, we show inclusions between behaviors, going in both directions between original and optimized programs. *)
*)
(**
最後の定理は簡単に証明できますが，余帰納法の原理に加えてこれまで説明してこなかったLtacによる賢い方法を使います．興味があればCoqのマニュアルを調べてもよいですし，この本の後ろの方の自動証明に関する章まで待ってもよいでしょう．
ざっくり言えば，元のプログラムと最適化されたプログラムの振舞いについて互いの包含関係を証明しています．
*)

Ltac finisher := match goal with
                   | [ H : evalCmd _ _ _ |- _ ] => ((inversion H; [])
                     || (inversion H; [|])); subst
                 end; crush; eauto 10.

Lemma optCmd_correct1 : forall vs1 c vs2, evalCmd vs1 c vs2
  -> evalCmd vs1 (optCmd c) vs2.
  intros; apply (evalCmd_coind (fun vs1 c' vs2 => exists c, evalCmd vs1 c vs2
    /\ c' = optCmd c)); eauto; crush;
    match goal with
      | [ H : _ = optCmd ?E |- _ ] => destruct E; simpl in *; discriminate
        || injection H; intros; subst
    end; finisher.
Qed.

Lemma optCmd_correct2 : forall vs1 c vs2, evalCmd vs1 (optCmd c) vs2
  -> evalCmd vs1 c vs2.
  intros; apply (evalCmd_coind (fun vs1 c vs2 => evalCmd vs1 (optCmd c) vs2));
    crush; finisher.
Qed.

Theorem optCmd_correct : forall vs1 c vs2, evalCmd vs1 (optCmd c) vs2
  <-> evalCmd vs1 c vs2.
  intuition; apply optCmd_correct1 || apply optCmd_correct2; assumption.
Qed.
(* end thide *)

(*
(** In this form, the theorem tells us that the optimizer preserves observable behavior of both terminating and nonterminating programs, but we did not have to do more work than for the case of terminating programs alone.  We merely took the natural inductive definition for terminating executions, made it co-inductive, and applied the appropriate co-induction principle.  Curious readers might experiment with adding command constructs like <<if>>; the same proof script should continue working, after the co-induction principle is extended to the new evaluation rules. *)
*)
(**
こうして，停止するプログラムでも停止しないプログラムでも最適化によって振舞いが変わらないことを示す定理が得られましたが，
停止するプログラムだけを考える場合と比較しても証明すべきことは多くなかったでしょう．
今回やったことは，
停止するプログラムに対する自然な帰納的定義を採用してそれを余帰納的にし，
適切な余帰納法の原理を適用しただけです．
興味があれば<<if>>のような命令構成子も追加して証明してみてください．
余帰納法の原理を新しい評価規則にも対応させれば，
同じ証明スクリプトが使えるはずです．
*)

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

Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(*
(** %\chapter{Proof by Reflection}% *)
 *)
(** %\chapter{リフレクションによる証明}% *)

(**
(* The last chapter highlighted a very heuristic approach to proving.  In this chapter, we will study an alternative technique,%\index{proof by reflection}% _proof by reflection_ %\cite{reflection}%.  We will write, in Gallina, decision procedures with proofs of correctness, and we will appeal to these procedures in writing very short proofs.  Such a proof is checked by running the decision procedure.  The term _reflection_ applies because we will need to translate Gallina propositions into values of inductive types representing syntax, so that Gallina programs may analyze them, and translating such a term back to the original form is called _reflecting_ it. *)

最後の章では、証明に対する非常にヒューリスティックなアプローチが強調されていました。
この章では、代替の技術、
%\index{proof by reflection}%_proof by reflection_ ＿リフレクションによる証明＿
%\cite{reflection}% を検討します。
Gallinaによって、決定手続き(decision procedures、決定するための手続き)
を正しさの証明とともに書いて、
これらの手続きが非常に短い証明で書けることを示します(appeal)。
項の _reflection_ ＿リフレクション＿ は、
Gallinaの命題を構文が表す帰納型の値に変換する必要があるために、適用されます。
それで、Gallinaプログラムがそれらを解析し、
そのような項を元の形式に戻すことを ＿リフレクトする＿ (_reflecting_ it) と呼びます。
 *)

(*
(** * Proving Evenness *)
 *)
(** * 偶数であることの証明 *)

(**
(* Proving that particular natural number constants are even is certainly something we would rather have happen automatically.  The Ltac-programming techniques that we learned in the last chapter make it easy to implement such a procedure. *)

特定の自然数の定数が偶数であることを証明することは、確かに自動的にできることです。
前章で学習したLtacプログラミング手法は、このような手順を簡単に実装できます。
 *)

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

(* begin thide *)
Ltac prove_even := repeat constructor.
(* end thide *)

Theorem even_256 : isEven 256.
  prove_even.
Qed.

Print even_256.
(** %\vspace{-.15in}% [[
even_256 = 
Even_SS
  (Even_SS
     (Even_SS
        (Even_SS
    ]]

(*
    %\noindent%...and so on.  This procedure always works (at least on machines with infinite resources), but it has a serious drawback, which we see when we print the proof it generates that 256 is even.  The final proof term has length super-linear in the input value.  Coq's implicit arguments mechanism is hiding the values given for parameter [n] of [Even_SS], which is why the proof term only appears linear here.  Also, proof terms are represented internally as syntax trees, with opportunity for sharing of node representations, but in this chapter we will measure proof term size as simple textual length or as the number of nodes in the term's syntax tree, two measures that are approximately equivalent.  Sometimes apparently large proof terms have enough internal sharing that they take up less memory than we expect, but one avoids having to reason about such sharing by ensuring that the size of a sharing-free version of a term is low enough.
*)

    %\noindent%
...等々。
この手順は常に（少なくとも無限のリソースを持つマシンでは）機能しますが、
重大な欠点があります。これは、256が偶数であるという証明を印刷(print)するときに表示されます。
最終的な証明項は、入力値に対して長さが超線形(super-linear)です。
Coqの暗黙的な引数の仕組みは、[Even_SS]のパラメータ[n]に与えられた値を隠しているので、
ここでは証明項はここでは線形にしか見えません。
(* suhara:
以下を実行すると納得できる：
Unset Printing Notations.
Set Printing Implicit.
Print even_256.
Set Printing Notations.
Unset Printing Implicit.
*)
また、証明項は内部的に構文木として表現され、ノード表現を共有する機会がありますが、
この章では、ほぼ同等の2つの尺度、証明文の長さを簡単なテキストの長さとして、
または、用語の構文木のノード数として測定します。
時には明らかに大きな証明項でも、内部では十分な共有を持っているため、
予想以上のメモリを消費することはありませんが、
共有のない(sharing-free)バージョンのサイズが十分に小さいことを保証することによって、
そのような共有を推論する必要はありません。

(*
    Superlinear evenness proof terms seem like a shame, since we could write a trivial and trustworthy program to verify evenness of constants.  The proof checker could simply call our program where needed.
*)

定数の偶数性を検証するための自明で信頼できるプログラムを書くことができるので、
超線形(Superlinear)な偶数性の証明項は残念なものに見えます。
証明チェッカーは、必要に応じて私たちのプログラムを単に呼び出すことができます。

(*
    It is also unfortunate not to have static typing guarantees that our tactic always behaves appropriately.  Other invocations of similar tactics might fail with dynamic type errors, and we would not know about the bugs behind these errors until we happened to attempt to prove complex enough goals.
*)

静的な型付けが、私たちのタクティクが常に適切に動作することを保証しないことも残念です。
同様の手法の他の呼び出しは、動的な型エラーで失敗する可能性があり、
十分に複雑なゴールを証明しようとするまで、
これらのエラーの背後にあるバグについてはわかりません。

(*
    The techniques of proof by reflection address both complaints.  We will be able to write proofs like in the example above with constant size overhead beyond the size of the input, and we will do it with verified decision procedures written in Gallina.
*)

リフレクションによる証明の手法は、両方の不満に対処します。
入力のサイズを超えて一定のサイズ(constant size)のオーバーヘッドを
持つ上記の例のような証明を書くことができ、
私たちはGallinaで書かれた検証された決定手続き(decision procedures)でそれを行います。

(*
    For this example, we begin by using a type from the [MoreSpecif] module (included in the book source) to write a certified evenness checker. *)

この例では、[MoreSpecif] モジュール（この本のソースに含まれています）の型を使用して、
認証された偶数性のチェッカーを作成します。
 *)

(* begin hide *)
(* begin thide *)
Definition paartial := partial.
(* end thide *)
(* end hide *)

(* suhara: src/MoreSpecif.v の partial 型 *)
Print partial.

(** %\vspace{-.15in}% [[
Inductive partial (P : Prop) : Set :=  Proved : P -> [P] | Uncertain : [P]
    ]]

(*
    A [partial P] value is an optional proof of [P]. The notation [[P]] stands for [partial P]. *)

[partial P] の値は、[P]のオプショナルな証明です。 表記[[P]]は[partial P]の略です。
 *)

(* suhara: 「オプション型」「オプショナルな型」に対応する「オプショナルな証明」
命題 [P]に対して、[t : P] であるとき、
それを [[]] で囲んだ、[[P]] には要素 [Proved t] と、[Uncertain P] がある。
なお、[Proved t] は [@Proved P t] の略である。

Check [True].
Check Proved I : [True].
Check @Proved True I : [True].
Check Uncertain True : [True].

Check [False].
Check @Proved False _.                      (* 存在しない値 *)
Check Uncertain False : [False].

Compute Proved Even_O : [isEven 0].             (* Yes *)
Compute @Proved (isEven 0) Even_O : [isEven 0]. (* Yes *)
Compute Uncertain (isEven 1) : [isEven 1].      (* No *)
*)

Local Open Scope partial_scope.

(**
(* We bring into scope some notations for the [partial] type.  These overlap with some of the notations we have seen previously for specification types, so they were placed in a separate scope that needs separate opening. *)

私たちは[partial]型の表記をいくつか取り上げます。
これらは、以前に、型の記述(specification types)で見た表記法の
いくつかと重複しているため、別々に開くことが必要な別のスコープに配置されました。

(* suhara: 「specification types」 は、Subset.v で初出する。 *)
 *)

(* begin thide *)
Definition check_even : forall n : nat, [isEven n].
  Hint Constructors isEven.

  refine (fix F (n : nat) : [isEven n] :=
    match n with
      | 0 => Yes
      | 1 => No
      | S (S n') => Reduce (F n')
    end); auto.
Defined.

(**
(* The function [check_even] may be viewed as a _verified decision procedure_, because its type guarantees that it never returns %\coqdocnotation{%#<tt>#Yes#</tt>#%}% for inputs that are not even.

関数[check_even]は、その型が偶数でない入力に対して
%\coqdocnotation{%#<tt>#Yes#</tt>#%}%
を返さないことを保証するので、
_verified decision procedure_ ＿検証された決定手続き＿
とみなすことができるでしょう。

 (* suhara: Reduce は、src/MoreSpecif.v で Notation として定義される。
Notation "'Reduce' x" := if x then Yes else No. *)
*)

(*
   Now we can use dependent pattern-matching to write a function that performs a surprising feat.  When given a [partial P], this function [partialOut] returns a proof of [P] if the [partial] value contains a proof, and it returns a (useless) proof of [True] otherwise.  From the standpoint of ML and Haskell programming, it seems impossible to write such a type, but it is trivial with a [return] annotation. *)

これで、依存パターンマッチング(dependent pattern-matching)を使用して、
驚くべきことを行う関数を書くことができます。
[partialPut]が与えられている場合、[partialOut]は[partial]値に証明が含まれていれば[P]の証明を返し、
それ以外の場合は [True] の（使用しないuseless)の証明を返します。
MLとHaskellのプログラミングの観点からは、このような型を
書くことは不可能ですが、[return]アノテーションを使用すれば自明です。
 *)

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                    | Proved _ => P
                    | Uncertain => True
                  end) with
    | Proved pf => pf
    | Uncertain => I
  end.

(* suhara:
Compute partialOut (@Proved True I).        (* I : True、 P=True 本来の証明 *)
Compute partialOut (Uncertain False).       (* I : True、 partialOut の機能 *)

Compute partialOut (@Proved (isEven 0) Even_O). (* Even_0 *)
Compute partialOut (Uncertain (isEven 1)).      (* I *)
 *)

(**
(* It may seem strange to define a function like this.  However, it turns out to be very useful in writing a reflective version of our earlier [prove_even] tactic: *)

このような関数を定義するのは奇妙に思えるかもしれませんが、
以前の[prove_even]タクティクのリフレクティブのバージョンを書くのに非常に便利です：*）
*)

Ltac prove_even_reflective :=
  match goal with
    | [ |- isEven ?N] => exact (partialOut (check_even N))
  end.
(* end thide *)

(**
(* We identify which natural number we are considering, and we "prove" its evenness by pulling the proof out of the appropriate [check_even] call.  Recall that the %\index{tactics!exact}%[exact] tactic proves a proposition [P] when given a proof term of precisely type [P]. *)

どの自然数を考えているのかを決め、適切な[check_even]の呼び出しから証明を引き出すことによって、
その偶数性を「証明」します。
正確に型 [P] の証明項が与えられたとき、
%\index{tactics!exact}%[exact] タクティクは、
命題 [P] を証明します。
 *)

Theorem even_256' : isEven 256.
  prove_even_reflective.
Qed.

Print even_256'.
(** %\vspace{-.15in}% [[
even_256' = partialOut (check_even 256)
     : isEven 256
    ]]

(*
    We can see a constant wrapper around the object of the proof.  For any even number, this form of proof will suffice.  The size of the proof term is now linear in the number being checked, containing two repetitions of the unary form of that number, one of which is hidden above within the implicit argument to [partialOut].
*)

私たちは、証明のゴールの周りに一定のラッパーを見ることができます。
偶数の場合は、この形式の証明で十分です。
証明項のサイズは、チェックされている数では線形で、

(* suhara: 実際には check_even の refine の末尾再帰だけ *)

その数の単項式の2つの繰り返しが含まれています。
そのうちのひとつは[partialOut]の暗黙の引数の上に隠されています。

(* suhara:
Set Printing Implicit.
Print even_256'.
even_256' = @partialOut (isEven 256) (check_even 256)
 *)

(*
    What happens if we try the tactic with an odd number? *)

奇数でこのタクティクを試してみたらどうなりますか？
*)

Theorem even_255 : isEven 255.
  (** %\vspace{-.275in}%[[
  prove_even_reflective.
]]

<<
User error: No matching clauses for match goal
>>

(*
  Thankfully, the tactic fails.  To see more precisely what goes wrong, we can run manually the body of the [match].
*)
ありがたいことに、タクティクは失敗します。
間違ったことをより正確に見るために、[match]の本体を手動で実行することができます。

  %\vspace{-.15in}%[[
  exact (partialOut (check_even 255)).
]]

<<
  Error: The term "partialOut (check_even 255)" has type
 "match check_even 255 with
  | Yes => isEven 255
  | No => True
  end" while it is expected to have type "isEven 255"
>>

(*
  As usual, the type checker performs no reductions to simplify error messages.  If we reduced the first term ourselves, we would see that [check_even 255] reduces to a %\coqdocnotation{%#<tt>#No#</tt>#%}%, so that the first term is equivalent to [True], which certainly does not unify with [isEven 255]. *)

いつものように、型チェッカーはエラーメッセージを単純化するために
リダクション(式の簡約)を実行しません。
最初の項を自分自身で簡約した場合、[check_even 255]は
%\coqdocnotation{%#<tt>#No#</tt>#%}%に簡約され、
最初の項
(* suhara: の partialOut の結果は I でその型 *)
は[True]と等しく、
(* suhara: exact の引数は I となり、Iの型[True]は、 *)
[isEven 255]とユニファイしないのは確かです。

(* suhara: 補足説明

(1) partialOut (check_even 255)) を手動で評価する。
@partialOut (isEven 255) (check_even 255) なので、

(1.1) partialOut の return のなかのmatchは、

match check_even 255 with
| Yes => isEven 255
| No => True
end

となる。check_even 255 は No なので、return のmatchは True になる。

(1.2) partialOut の本文のmatch
match (x) with
| Proved pf => pf
| Uncertain => I
end
で、x は [isEven 255] の値なので、Uncertain である。本体のmatchは I になる。

(1.1)と(1.2)から、partialOut (check_even 255) は I : True を返す。

(2) 最初の証明にもどって、

exact partialOut (check_even 255)) は exact I になる。

Theorem even_255 : isEven 255.
exact I.

I の型 isEven 255 ではないので、
exact I は、定理の証明になっておらず、エラーである。
   *)
*)
  
Abort.

(**
(* Our tactic [prove_even_reflective] is reflective because it performs a proof search process (a trivial one, in this case) wholly within Gallina, where the only use of Ltac is to translate a goal into an appropriate use of [check_even]. *)

タクティク[prove_even_reflective]は、リフレクティブです。
なぜなら、Gallina内の証明検索のプロセス（この場合は自明なもの）を実行するために、
Ltacの唯一の使用は目標を[check_even]の適切な使用に変換するためです。
*)

(*
(** * Reifying the Syntax of a Trivial Tautology Language *)
 *)
(** * 自明なトートロジーの言語の文法の具象化(reifying) *)
(* suhara: 具象化 https://ja.wikipedia.org/wiki/%E7%89%A9%E8%B1%A1%E5%8C%96 *)

(**
(* We might also like to have reflective proofs of trivial tautologies like this one: *)

このような自明なトートロジーのリフレクティブな証明をしたいかもしれません：
*)

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
  (* suhara: crush でも証明できる。結果は同じである。 *)
  tauto.
Qed.

(* begin hide *)
(* begin thide *)
Definition tg := (and_ind, or_introl).
(* end thide *)
(* end hide *)

Print true_galore.
(** %\vspace{-.15in}% [[
true_galore = 
fun H : True /\ True =>
and_ind (fun _ _ : True => or_introl (True /\ (True -> True)) I) H
     : True /\ True -> True \/ True /\ (True -> True)
    ]]

(*
    As we might expect, the proof that [tauto] builds contains explicit applications of natural deduction rules.  For large formulas, this can add a linear amount of proof size overhead, beyond the size of the input.
*)

予想されるように、[tauto] が作る証拠は、
自然演繹規則の明示的な応用が含まれています。
大きな式の場合、これは、入力のサイズを超える、
証明のサイズの線形量のオーバーヘッドを追加する可能性があります。

(*
   To write a reflective procedure for this class of goals, we will need to get into the actual "reflection" part of "proof by reflection."  It is impossible to case-analyze a [Prop] in any way in Gallina.  We must%\index{reification}% _reify_ [Prop] into some type that we _can_ analyze.  This inductive type is a good candidate: *)

このクラスのゴールに対してリフレクティブな手順を書くには、
「リフレクティブによる証明」の実際の「リフレクティブ」な部分に入る必要があります。
Gallinaのいかなるところでも、[Prop] を条件分析(case-analyze)することは不可能です。
[Prop] を %\index{reification}% _reify_ ＿具象化＿ して、解析できる型にする必要があります。
この帰納型は良い候補です：
 *)

(* begin thide *)
Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

(**
(* We write a recursive function to _reflect_ this syntax back to [Prop].  Such functions are also called%\index{interpretation function}% _interpretation functions_, and we have used them in previous examples to give semantics to small programming languages. *)

この構文を _reflect_ ＿リフレクト＿ して [Prop]に戻すための再帰関数を書きます。
このような関数は
%\index{interpretation function}% _interpretation functions_ ＿翻訳関数＿
とも呼ばれ、前の例で、小さなプログラミング言語に意味論を与えるために使用しています。
(* suhara: あとで denotation function とも呼ばれる。 *)
 *)

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

(**
(* It is easy to prove that every formula in the range of [tautDenote] is true. *)

[tautDenote]の範囲のすべての式が真であることを証明するのは簡単です。
*)

Theorem tautTrue : forall t, tautDenote t.
  induction t; crush.
Qed.

(**
(* To use [tautTrue] to prove particular formulas, we need to implement the syntax reification process.  A recursive Ltac function does the job. *)

特定の式を証明するために[tautTrue]を使用するには、
その構文を具象化する手順(reification process)を実装する必要があります。
再帰的なLtac関数がその仕事をします。
 *)

Ltac tautReify P :=
  match P with
    | True => TautTrue
    | ?P1 /\ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautImp t1 t2)
  end.

(**
(* With [tautReify] available, it is easy to finish our reflective tactic.  We look at the goal formula, reify it, and apply [tautTrue] to the reified formula. *)

[tautReify]が利用可能なので、
リフレクティブなタクティクを終わらせるのは簡単です。
ゴールの式を見て、それを具象化(reify)し、その具象化した式に[tautTrue]を適用します。
 *)

Ltac obvious :=
  match goal with
    | [ |- ?P ] =>
      let t := tautReify P in
        exact (tautTrue t)
  end.

(**
(* We can verify that [obvious] solves our original example, with a proof term that does not mention details of the proof. *)

証明項の詳細は言及せずに、
[obvious] がもとの例を解くことを証明することができます。
*)
(* end thide *)

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
(* suhara:
  intros.
  let p := tautReify (True \/ True /\ (True -> True)) in pose p as t.
  Check tautTrue t : tautDenote t.
  exact (tautTrue t).
  Restart.
*)
  obvious.
Qed.

Print true_galore'.
(** %\vspace{-.15in}% [[
true_galore' = 
tautTrue
  (TautImp (TautAnd TautTrue TautTrue)
     (TautOr TautTrue (TautAnd TautTrue (TautImp TautTrue TautTrue))))
     : True /\ True -> True \/ True /\ (True -> True)
    ]]

(*
    It is worth considering how the reflective tactic improves on a pure-Ltac implementation.  The formula reification process is just as ad-hoc as before, so we gain little there.  In general, proofs will be more complicated than formula translation, and the "generic proof rule" that we apply here _is_ on much better formal footing than a recursive Ltac function.  The dependent type of the proof guarantees that it "works" on any input formula.  This benefit is in addition to the proof-size improvement that we have already seen.
*)

純粋なLtacによる実装で、リフレクティブなタクティクがどのように改善するかを考える価値があります。
式の具象化の手順は以前と同じようにアドホックなので、
そこではほとんど利益を得ることはできません。
一般に、証明は数式の変換よりも複雑になります。
ここで適用する「一般的な証明の規則 (generic proof rule)」は、
再帰的なLtac関数よりもはるかに優れた正式な基礎に当てはまります。
依存型の証明は、どの入力式でも「機能する」ことを保証します。
この利点は、すでに見てきた、証明のサイズの改善に加えられます。

(*
    It may also be worth pointing out that our previous example of evenness testing used a function [partialOut] for sound handling of input goals that the verified decision procedure fails to prove.  Here, we prove that our procedure [tautTrue] (recall that an inductive proof may be viewed as a recursive procedure) is able to prove any goal representable in [taut], so no extra step is necessary. *)

以前の例の偶数性のテストでは、
検証された決定手続きが証明できない入力ゴールを
健全に処理する(sound handling)ために関数[partialOut]を使用していたことを指摘する価値があります。
ここで、手続き [tautTrue] 
（帰納的証明は再帰的手続きと見なすことができることを思い出してください）
は、[taut]で表現できるどんなゴールをも証明できるので、余分なステップは必要ありません。

 *)
(*
(** * A Monoid Expression Simplifier *)
 *)
(** * モノイド式の簡略化 *)

(**
(* Proof by reflection does not require encoding of all of the syntax in a goal.  We can insert "variables" in our syntax types to allow injection of arbitrary pieces, even if we cannot apply specialized reasoning to them.  In this section, we explore that possibility by writing a tactic for normalizing monoid equations. *)

リフレクションによる証明では、ゴールの中のすべての構文をエンコードする必要はありません。
特殊な推論を適用できない場合でも、任意の断片が注入(injection)を許すために、
構文の型に「変数」を挿入することができます。
その可能性を、モノイドの等式(monoid equations)を正規化するための
タクティクを書くことによって探求します。
 *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A -> A.

  Infix "+" := f.

  Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
  Hypothesis identl : forall a, e + a = a.
  Hypothesis identr : forall a, a + e = a.

  (**
(* We add variables and hypotheses characterizing an arbitrary instance of the algebraic structure of monoids.  We have an associative binary operator and an identity element for it.
*)

モノイドの代数構造の任意のインスタンスを特徴付ける変数と仮説を追加します。
結合法則を満たす(associative)2項演算子とそれに対する単位元があります。

(*
     It is easy to define an expression tree type for monoid expressions.  A [Var] constructor is a "catch-all" case for subexpressions that we cannot model.  These subexpressions could be actual Gallina variables, or they could just use functions that our tactic is unable to understand. *)

モノイドの式についての木の型の式を定義するのは簡単です。
[Var]コンストラクタは、私たちがモデル化できない部分式の「キャッチ・オール」ケースです。
これらの部分式は、実際のGallina変数であるべきで、また、
私たちのタクティクが理解できない関数を使うことができます。
   *)
  
(* begin thide *)
  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  (**
(* Next, we write an interpretation function. *)

次に、翻訳関数(interpretation function)を書きます。
   *)
  
  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => e
      | Var v => v
      | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  (**
(* We will normalize expressions by flattening them into lists, via associativity, so it is helpful to have a denotation function for lists of monoid values. *)

結合法則を使って(via associativity)式をリストにフラット化(flattening)することで式を
正規化するので、モノイドの値のリストのための表示関数(denotation function)があると便利です。
   *)
  
  Fixpoint mldenote (ls : list A) : A :=
    match ls with
      | nil => e
      | x :: ls' => x + mldenote ls'
    end.

  (** 
(* The flattening function itself is easy to implement. *)

フラット化関数は、それ自体、実装するのに簡単です。
*)

  Fixpoint flatten (me : mexp) : list A :=
    match me with
      | Ident => nil
      | Var x => x :: nil
      | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  (**
  (* This function has a straightforward correctness proof in terms of our [denote] functions. *)
この関数は、私たちの [表示(denote)] 関数に関して簡単な正当性証明を持っています。
*)

  Lemma flatten_correct' : forall ml2 ml1,
    mldenote ml1 + mldenote ml2 = mldenote (ml1 ++ ml2).
    induction ml1; crush.
  Qed.

  Theorem flatten_correct : forall me, mdenote me = mldenote (flatten me).
    Hint Resolve flatten_correct'.
    
    induction me; crush.
  Qed.

  (**
  (* Now it is easy to prove a theorem that will be the main tool behind our simplification tactic. *)

簡約化タクティクの主な道具となる定理を証明するのは簡単です。
*)

  Theorem monoid_reflect : forall me1 me2,
    mldenote (flatten me1) = mldenote (flatten me2)
    -> mdenote me1 = mdenote me2.
    intros; repeat rewrite flatten_correct; assumption.
  Qed.

  (**
  (* We implement reification into the [mexp] type. *)

[mexp] 型への具象化を実装します。
   *)
  
  Ltac reify me :=
    match me with
      | e => Ident
      | ?me1 + ?me2 =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

  (**
(* The final [monoid] tactic works on goals that equate two monoid terms.  We reify each and change the goal to refer to the reified versions, finishing off by applying [monoid_reflect] and simplifying uses of [mldenote].  Recall that the %\index{tactics!change}%[change] tactic replaces a conclusion formula with another that is definitionally equal to it. *)

最終的な[monoid]タクティクは、モノイドの項のふたつからなる等式のゴールに作用します。
それぞれを具象化(reify)し、[monoid_reflect]を適用し、[mldenote]使って簡単化することで、
ゴールが具現化したバージョンを参照するように変更します。
%\index {tactics!change}%[change] タクティクは、
結論の式を定義として等しいものに置き換えることを思い出してください。
   *)
  
  Ltac monoid :=
    match goal with
      | [ |- ?me1 = ?me2 ] =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          change (mdenote r1 = mdenote r2);
            apply monoid_reflect; simpl
    end.

  (**
(* We can make short work of theorems like this one: *)

このような定理の短い作業をすることができます：
*)

(* end thide *)

  Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
    intros; monoid.
    (** [[
  ============================
   a + (b + (c + (d + e))) = a + (b + (c + (d + e)))
 
        ]]

(*
        Our tactic has canonicalized both sides of the equality, such that we can finish the proof by reflexivity. *)

monoidタクティクは、等式の両辺を正準化(canonicalized)しているので、
反射性(reflexivity)によって証明を完成させることができます。
*)
    reflexivity.
  Qed.

  (**
(* It is interesting to look at the form of the proof. *)

証明の形式(the form)を見るのは面白いです。
*)

  Print t1.
  (** %\vspace{-.15in}% [[
t1 = 
fun a b c d : A =>
monoid_reflect (Op (Op (Op (Var a) (Var b)) (Var c)) (Var d))
  (Op (Op (Var a) (Op (Var b) (Var c))) (Var d))
  (eq_refl (a + (b + (c + (d + e)))))
     : forall a b c d : A, a + b + c + d = a + (b + c) + d
      ]]

(*
      The proof term contains only restatements of the equality operands in reified form, followed by a use of reflexivity on the shared canonical form. *)

証明項は、具現化された形式の等式のオペランドの再記述だけを含み、
共有された(shared)正準形(canonical form)への反射性の使用が続きます。
   *)
  
End monoid.

(**
(* Extensions of this basic approach are used in the implementations of the %\index{tactics!ring}%[ring] and %\index{tactics!field}%[field] tactics that come packaged with Coq. *)

この基本的なアプローチの拡張は、Coqでパッケージ化された、
%\index{tactics!ring}%[ring] と %\index{tactics!field}%[field] タクティク
の実装で使われています。
*)

(*
(** * A Smarter Tautology Solver *)
*)
(** * 賢いトートロジー・ソルバー *)

(**
(* Now we are ready to revisit our earlier tautology solver example.  We want to broaden the scope of the tactic to include formulas whose truth is not syntactically apparent.  We will want to allow injection of arbitrary formulas, like we allowed arbitrary monoid expressions in the last example.  Since we are working in a richer theory, it is important to be able to use equalities between different injected formulas.  For instance, we cannot prove [P -> P] by translating the formula into a value like [Imp (Var P) (Var P)], because a Gallina function has no way of comparing the two [P]s for equality.
*)

これで、以前のトートロジー・ソルバーの例を再検討する準備が整いました。 
私たちは、真理が構文的に明らかでない式を含むようにタクティクの範囲を広げたいと考えています。
最後の例で任意のモノイド式を許可したのと同じように、
任意の式の注入(injection)を許可したいと思うでしょう。
私たちはより豊かな理論で作業しているので、
注入された異なる式の間で等値を使用できることが重要です。
例えば、Gallina関数は、ふたつの[P]が等しいかどうかを比較する方法がないため、
式を[Imp (Var P) (Var P)]のような値に変換することによって[P -> P]を証明することはできません。

(* suhara: 「注入」 に単射(injection)の意味はあるか？
後で [Prop]から[Formula]への injection という。 *)

(*
   To arrive at a nice implementation satisfying these criteria, we introduce the %\index{tactics!quote}%[quote] tactic and its associated library. *)

これらの基準を満たす素晴らしい実装に到達するために、
%\index{tactics!quote}%[quote]
タクティクとそれに関連するライブラリを紹介します。 
 *)

Require Import Quote.

(* begin thide *)
Inductive formula : Set :=
| Atomic : index -> formula                 (* suhara: 原始論理式 *)
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.
(* end thide *)

(**
(* The type %\index{Gallina terms!index}%[index] comes from the [Quote] library and represents a countable variable type.  The rest of [formula]'s definition should be old hat by now.

%\index{Gallina terms!index}%[index] 型は、[Quote]ライブラリからのものであり、
可算の変数の型を表します。
残りの[formula]の定義は、今のところ以前のまま(old hat)でなければなりません。
*)

(*   The [quote] tactic will implement injection from [Prop] into [formula] for us, but it is not quite as smart as we might like.  In particular, it wants to treat function types specially, so it gets confused if function types are part of the structure we want to encode syntactically.  To trick [quote] into not noticing our uses of function types to express logical implication, we will need to declare a wrapper definition for implication, as we did in the last chapter. *)

[quote] タクティクは[Prop]から[Formula]への単射(injection)を実装しますが、
望むほどスマートではありません。 
特に、関数型を特別に扱いたいので、
関数型が構文的に符号化したい構造体の一部であれば混乱(confused)します。
論理的な意味を表現するために関数型を使用することに気づかないように
[quote]することをトリックするには、
最後の章で行ったように、含意のラッパー定義を宣言する必要があります。
 *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).

(**
(* Now we can define our denotation function. *)

ここでは、表示関数(denotation function)を定義することができます。
 (* suhara: 翻訳関数 interpretation function とも呼ばれる。 see. tautDenote *)
*)

Definition asgn := varmap Prop.             (* suhara: varmap は plugins/quote/Quote.v *)

(* begin thide *)
Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => varmap_find False v atomics
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 --> formulaDenote atomics f2
  end.
(* end thide *)

(**
(* The %\index{Gallina terms!varmap}%[varmap] type family implements maps from [index] values.  In this case, we define an assignment as a map from variables to [Prop]s.  Our interpretation function [formulaDenote] works with an assignment, and we use the [varmap_find] function to consult the assignment in the [Atomic] case.  The first argument to [varmap_find] is a default value, in case the variable is not found. *)

%\index{Gallina terms!varmap}%[varmap] のファミリーは、
[index] の値から map を実装します。
この場合、変数から [Prop] への map として代入を定義します。
翻訳関数(interpretation function) [formulaDenote]は代入として動作し、
[varmap_find]関数を使って[Atomic]の場合の代入を調べます。
[varmap_find]の最初の引数は、変数が見つからない場合のデフォルト値です。
 *)

(* suhara: [varmap] ファミリーの使用例。

Print index.
(*
Inductive index : Set :=
| Left_idx : index -> index
| Right_idx : index -> index
| End_idx : index
 *)

Print varmap.
(*
Inductive varmap (A : Type) : Type :=
| Empty_vm : varmap A
| Node_vm : A -> varmap A -> varmap A -> varmap A
 *)

Variable ap0 : Prop.
Variable ap1 : Prop.
Variable ap2 : Prop.
Definition av0 :=           End_idx : index.
Definition av1 := Left_idx  End_idx : index.
Definition av2 := Right_idx End_idx : index.
Definition av3 := Right_idx (Right_idx End_idx) : index.
Definition aas := (Node_vm ap0              (* End_idx *)
                          (Node_vm ap1      (* Left_idx End_idx *)
                                   (Empty_vm Prop)
                                   (Empty_vm Prop))
                          (Node_vm ap2      (* Right_idx End_idx *)
                                   (Empty_vm Prop)
                                   (Empty_vm Prop)))
                 : asgn.
Compute varmap_find False av0 aas.            (* ap0 *)
Compute varmap_find False av1 aas.            (* ap1 *)
Compute varmap_find False av2 aas.            (* ap2 *)
Compute varmap_find False av3 aas.            (* False *)

asgn は、変数とその値の対応（代入）である。あとで出てくる
環境を示す変数のリスト(set index)とは異なる。
*)


Section my_tauto.
  Variable atomics : asgn.

  Definition holds (v : index) := varmap_find False v atomics.

  (**
(* We define some shorthand for a particular variable being true, and now we are ready to define some helpful functions based on the [ListSet] module of the standard library, which (unsurprisingly) presents a view of lists as sets. *)

特定の変数が真であるためにいくつかの省略形を定義し、
標準ライブラリの[ListSet]モジュールに基づいて、
（驚くことではありませんが）リストを集合として見ることを提供する、
便利な関数を定義する準備が整いました。
   *)
  
  Require Import ListSet.                   (* suhara: set_add の定義 *)

  Definition index_eq : forall x y : index, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition add (s : set index) (v : index) := set_add index_eq v s.
  (* suhara: 環境sに、変数vを追加する。 *)

  Definition In_dec : forall v (s : set index), {In v s} + {~ In v s}.
    Local Open Scope specif_scope.

    intro; refine (fix F (s : set index) : {In v s} + {~ In v s} :=
      match s with
        | nil => No
        | v' :: s' => index_eq v' v || F s'
      end); crush.
  Defined.

  (**
(* We define what it means for all members of an index set to represent true propositions, and we prove some lemmas about this notion. *)

index の集合のすべてのメンバーに対して真となる命題を表わすもの
(* suhara: この場合はallTrue *)を定義し、
この表記についてのいくつかの補題を証明します。
*)

  Fixpoint allTrue (s : set index) : Prop :=
    match s with
      | nil => True
      | v :: s' => holds v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> holds v
    -> allTrue (add s v).
    induction s; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> varmap_find False v atomics.
    induction s; crush.
  Qed.

  Hint Resolve allTrue_add allTrue_In.

  Local Open Scope partial_scope.

  (**
(* Now we can write a function [forward] that implements deconstruction of hypotheses, expanding a compound formula into a set of sets of atomic formulas covering all possible cases introduced with use of [Or].  To handle consideration of multiple cases, the function takes in a continuation argument, which will be called once for each case.
*)

ここで、仮説の分解(deconstruction)を実装する関数 [forward] を書くことができ、
複合式を、[Or]を使って導入された可能性のあるすべての場合(case)をカバーする
一連のアトミックな論理式の集合に
展開することができます。

(* suhara:
どこに展開されるのかよくわからない。

atomic formula と言っているけれど、
Or で並べられた論理式なので、原始論理式ではなく「節」と呼ぶべきであろう。
formula型で導入された Atomic とは異なる。
*)

複数のケースの考慮を処理するために、この関数は継続引数(continuation argument
(* suhara: 継続渡しの引数 *))を取ります。
これはそれぞれのケースに対して1回呼び出されます。

(*
     The [forward] function has a dependent type, in the style of Chapter 6, guaranteeing correctness.  The arguments to [forward] are a goal formula [f], a set [known] of atomic formulas that we may assume are true, a hypothesis formula [hyp], and a success continuation [cont] that we call when we have extended [known] to hold new truths implied by [hyp]. *)

[forward]関数は、第6章のスタイルで依存性の型を持ち、正確さを保証します。
[forward]のへの引数は、ゴールの式[f]、
真であると仮定してもよい原子式の集合[known]、
仮定の式[hyp]、
および、[hyp]によって含意される新しい真実を保持するために
[known] を拡張するときに呼び出す次への継続(success continuation) [cont] です。
   *)
  
  Definition forward : forall (f : formula) (known : set index) (hyp : formula)
    (cont : forall known', [allTrue known' -> formulaDenote atomics f]),
    [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f].
    refine (fix F (f : formula) (known : set index) (hyp : formula)
      (cont : forall known', [allTrue known' -> formulaDenote atomics f])
      : [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f] :=
      match hyp with
        | Atomic v => Reduce (cont (add known v))
        | Truth => Reduce (cont known)
        | Falsehood => Yes
        | And h1 h2 =>
          Reduce (F (Imp h2 f) known h1 (fun known' =>
            Reduce (F f known' h2 cont)))
        | Or h1 h2 => F f known h1 cont && F f known h2 cont
        | Imp _ _ => Reduce (cont known)
      end); crush.
  Defined.

  (**
(* A [backward] function implements analysis of the final goal.  It calls [forward] to handle implications. *)

[backward]関数は、最終のゴールの分析を実装します。
含意を扱うために[forward]を呼び出します。
   *)
  
(* begin thide *)
  Definition backward : forall (known : set index) (f : formula),
    [allTrue known -> formulaDenote atomics f].
    refine (fix F (known : set index) (f : formula)
      : [allTrue known -> formulaDenote atomics f] :=
      match f with
        | Atomic v => Reduce (In_dec v known)
        | Truth => Yes
        | Falsehood => No
        | And f1 f2 => F known f1 && F known f2
        | Or f1 f2 => F known f1 || F known f2
        | Imp f1 f2 => forward f2 known f1 (fun known' => F known' f2)
      end); crush; eauto.
  Defined.
(* end thide *)

  (**
(* A simple wrapper around [backward] gives us the usual type of a partial decision procedure. *)

[backward]の周りの単純なラッパーは、部分的な決定のための手続きの通常のタイプを与えます。
(* suhara: partial は部分関数だが、decision は決定性ではないと思う *)
   *)
  
  Definition my_tauto : forall f : formula, [formulaDenote atomics f].
(* begin thide *)
    intro; refine (Reduce (backward nil f)); crush.
  Defined.
(* end thide *)
End my_tauto.

(**
(* Our final tactic implementation is now fairly straightforward.  First, we [intro] all quantifiers that do not bind [Prop]s.  Then we call the [quote] tactic, which implements the reification for us.  Finally, we are able to construct an exact proof via [partialOut] and the [my_tauto] Gallina function. *)

最終的なタクティクの実装はかなり簡単です。
まず、[Prop] の束縛しないすべての量化子を [intro] します。
次に、具象化を実装する[quote]タクティクを呼び出します。 
最後に、[partialOut]と[my_tauto] のGallina関数を使用して正確な証明を構築します。

 (* suhara: exact の中のmy_tautoは、関数呼び出し。 *)
 *)

Ltac my_tauto :=
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1      (* suhara: 2階論理は扱わない？ *)
               | _ => intro
             end
         end;
  quote formulaDenote;
  match goal with
    | [ |- formulaDenote ?m ?f ] => exact (partialOut (my_tauto m f))
  end.
(* end thide *)

(**
(* A few examples demonstrate how the tactic works. *)

いくつかの例は、タクティクがどのように機能するかを示しています。
*)


Theorem mt1 : True.
  my_tauto.
Qed.

Print mt1.
(** %\vspace{-.15in}% [[
mt1 = partialOut (my_tauto (Empty_vm Prop) Truth)
     : True
    ]]

(*
    We see [my_tauto] applied with an empty [varmap], since every subformula is handled by [formulaDenote]. *)

すべての部分式は[formulaDenote]によって処理されるため、
[my_tauto]に空の[varmap] (* suhara: (Empty_vm Prop) *) が適用されていることがわかります。
 *)

(* suhara:
Compute my_tauto (Empty_vm Prop) Truth.     (* YES *)
*)

Theorem mt2 : forall x y : nat, x = y --> x = y.
  my_tauto.
Qed.

(* suhara: nvm はなんのためにあるのか？ *)
(* begin hide *)
(* begin thide *)
Definition nvm := (Node_vm, Empty_vm, End_idx, Left_idx, Right_idx).
(* end thide *)
(* end hide *)

Print mt2.
(** %\vspace{-.15in}% [[
mt2 = 
fun x y : nat =>
partialOut
  (my_tauto (Node_vm (x = y) (Empty_vm Prop) (Empty_vm Prop))
     (Imp (Atomic End_idx) (Atomic End_idx)))
     : forall x y : nat, x = y --> x = y
    ]]

(*
    Crucially, both instances of [x = y] are represented with the same index, [End_idx].  The value of this index only needs to appear once in the [varmap], whose form reveals that [varmap]s are represented as binary trees, where [index] values denote paths from tree roots to leaves. *)

重要なことに、[x = y]の両方のインスタンスは同じインデックス[End_idx]で表されます。
このインデックスの値は[varmap]に1回だけ現れなければならず、
[varmap]は、
[index] の値が木の根から葉までのパスを示す、
二進木(binary trees) として表現されます。
 *)
(*
Variables x y : nat.
Compute (my_tauto (Node_vm (x = y) (Empty_vm Prop) (Empty_vm Prop))
                  (Imp (Atomic End_idx) (Atomic End_idx))). (* YES *)
 *)

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  --> y > z /\ (x < y \/ x < S y).
  my_tauto.
Qed.

Print mt3.
(** %\vspace{-.15in}% [[
fun x y z : nat =>
partialOut
  (my_tauto
     (Node_vm (x < S y) (Node_vm (x < y) (Empty_vm Prop) (Empty_vm Prop))
        (Node_vm (y > z) (Empty_vm Prop) (Empty_vm Prop)))
     (Imp
        (Or (And (Atomic (Left_idx End_idx)) (Atomic (Right_idx End_idx)))
           (And (Atomic (Right_idx End_idx)) (Atomic End_idx)))
        (And (Atomic (Right_idx End_idx))
           (Or (Atomic (Left_idx End_idx)) (Atomic End_idx)))))
     : forall x y z : nat,
       x < y /\ y > z \/ y > z /\ x < S y --> y > z /\ (x < y \/ x < S y)
    ]]

(*
    Our goal contained three distinct atomic formulas, and we see that a three-element [varmap] is generated.
*)

ゴールにはみっつの異なる原子式が含まれていて、
3要素の「varmap」が生成されていることがわかります。

(*
    It can be interesting to observe differences between the level of repetition in proof terms generated by [my_tauto] and [tauto] for especially trivial theorems. *)

特に自明な定理のために[my_tauto]と[tauto]によって生成される証明項の反復の
レベルの違いを観察することは面白いかもしれません。
 *)

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False --> False.
  my_tauto.
Qed.

Print mt4.
(** %\vspace{-.15in}% [[
mt4 = 
partialOut
  (my_tauto (Empty_vm Prop)
     (Imp
        (And Truth
           (And Truth
              (And Truth (And Truth (And Truth (And Truth Falsehood))))))
        Falsehood))
     : True /\ True /\ True /\ True /\ True /\ True /\ False --> False
    ]]
    *)

Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
  tauto.
Qed.

(* suhara: これも必要か？ *)
(* begin hide *)
(* begin thide *)
Definition fi := False_ind.
(* end thide *)
(* end hide *)

Print mt4'.
(** %\vspace{-.15in}% [[
mt4' = 
fun H : True /\ True /\ True /\ True /\ True /\ True /\ False =>
and_ind
  (fun (_ : True) (H1 : True /\ True /\ True /\ True /\ True /\ False) =>
   and_ind
     (fun (_ : True) (H3 : True /\ True /\ True /\ True /\ False) =>
      and_ind
        (fun (_ : True) (H5 : True /\ True /\ True /\ False) =>
         and_ind
           (fun (_ : True) (H7 : True /\ True /\ False) =>
            and_ind
              (fun (_ : True) (H9 : True /\ False) =>
               and_ind (fun (_ : True) (H11 : False) => False_ind False H11)
                 H9) H7) H5) H3) H1) H
     : True /\ True /\ True /\ True /\ True /\ True /\ False -> False
    ]]

(*
The traditional [tauto] tactic introduces a quadratic blow-up in the size of the proof term, whereas proofs produced by [my_tauto] always have linear size. *)

伝統的な[tauto]タクティクは、
証明項のサイズの2次(quadratic)的な「爆発(blow-up)」を導入するのに対し、(* suhara: O(n2) *)
[my_tauto]によって生成される証明は常に線形の大きさを持ちます。(* suhara: O(n) *)
 *)

(*
(** ** Manual Reification of Terms with Variables *)
 *)
(** ** 変数を持つ項の手動の具象化 *)

(* begin thide *)
(**
(* The action of the [quote] tactic above may seem like magic.  Somehow it performs equality comparison between subterms of arbitrary types, so that these subterms may be represented with the same reified variable.  While [quote] is implemented in OCaml, we can code the reification process completely in Ltac, as well.  To make our job simpler, we will represent variables as [nat]s, indexing into a simple list of variable values that may be referenced.
*)

上記の[quote] タクティクの動作は手品のように見えます。
どういうわけか、それは任意の型の副項(subterms)どうしが等しいかどうかの比較(equality comparison)
を実行するので、これらの副項は同じ具象化された(reified)変数でされるでしょう。
[quote]はOCamlで実装されていますが、具象化のプロセス(reification process)
をLtacで完全にコードすることができます。
仕事をより簡単にするために、変数を[nat]として表現し、
参照される変数の値からなる単純なリストにインデックスを付けます。
(* suhara: 変数を表現する[nat]のインデックスでリストを参照することで、値を得る。
これに対して、[varmap]ファミリは、二分木を使っていた。 *)

(*
   Step one of the process is to crawl over a term, building a duplicate-free list of all values that appear in positions we will encode as variables.  A useful helper function adds an element to a list, preventing duplicates.  Note how we use Ltac pattern matching to implement an equality test on Gallina terms; this is simple syntactic equality, not even the richer definitional equality.  We also represent lists as nested tuples, to allow different list elements to have different Gallina types. *)

プロセスの最初のステップは、項をクロールし、
エンコードする位置に表示されるすべての値の重複のないリストを変数として構築することです。
便利な補助関数(helper function)は、重複を防止ながら、要素をリストに追加ます。
Ltacのパターンマッチングを使用してGallina項についての等値のテスト
(equality test)を実装する方法に注意してください。
これは単純な文法的な等値(syntactic equality)であり、
より豊かな定義による等値(definitional equality)ではありません。
また、異なるリストの要素が異なるGallinaに型を持つことを可能にするために、
ネストされたタプルとしてリストを表現します。
*)

Ltac inList x xs :=
  match xs with
    | tt => false
    | (x, _) => true
    | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
    match b with
      | true => xs
      | false => constr:((x, xs))
    end.

(**
(* Now we can write our recursive function to calculate the list of variable values we will want to use to represent a term. *)

ここで、項を表すために使用する変数値のリストを計算する再帰関数を書くことができます。
 *)

Ltac allVars xs e :=
  match e with
    | True => xs
    | False => xs
    | ?e1 /\ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 \/ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 -> ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | _ => addToList e xs
  end.

(**
(* We will also need a way to map a value to its position in a list. *)

値をリストの内の位置にマップする方法も必要です。
 *)

Ltac lookup x xs :=
  match xs with
    | (x, _) => O
    | (_, ?xs') =>
      let n := lookup x xs' in
        constr:(S n)
  end.

(**
(* The next building block is a procedure for reifying a term, given a list of all allowed variable values.  We are free to make this procedure partial, where tactic failure may be triggered upon attempting to reify a term containing subterms not included in the list of variables.  The type of the output term is a copy of [formula] where [index] is replaced by [nat], in the type of the constructor for atomic formulas. *)


次の構成要素(building block)は、許可されたすべての変数値のリストを指定して、
項を具象化する手順です。
変数のリストに含まれていない副項(subterm)を含む項の具象化を試みると、
タクティクの失敗が引き起こされる可能性があるため、
この手続きは部分的(partial)になります(free to make this procedure partial)。
出力項の型は、[index]が[nat]に置き換えられた[formula]のコピーで、
アトミックな式のコンストラクタの型です。
 *)

Inductive formula' : Set :=
| Atomic' : nat -> formula'
| Truth' : formula'
| Falsehood' : formula'
| And' : formula' -> formula' -> formula'
| Or' : formula' -> formula' -> formula'
| Imp' : formula' -> formula' -> formula'.

(**
(* Note that, when we write our own Ltac procedure, we can work directly with the normal [->] operator, rather than needing to introduce a wrapper for it. *)

私たち自身のLtac手続きを書くときは、ラッパーを導入する必要はなく、
通常の[->]演算子で直接作業することができます。
(* suhara: quote のためには --> が必要だったが、ここでは不要である *)
 *)

Ltac reifyTerm xs e :=
  match e with
    | True => Truth'
    | False => Falsehood'
    | ?e1 /\ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(And' p1 p2)
    | ?e1 \/ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Or' p1 p2)
    | ?e1 -> ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Imp' p1 p2)
    | _ =>
      let n := lookup e xs in
        constr:(Atomic' n)
  end.

(**
(* Finally, we bring all the pieces together. *)

最後に、すべての作品をまとめています。
*)
Ltac reify :=
  match goal with
    | [ |- ?G ] => let xs := allVars tt G in
      let p := reifyTerm xs G in
        pose p
  end.

(**
(* A quick test verifies that we are doing reification correctly. *)

クイックテストは、私たちが正しく具象化(reification)を行っていることを検証します。
*)
  
Theorem mt3' : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  -> y > z /\ (x < y \/ x < S y).
  do 3 intro; reify.

(**
(* Our simple tactic adds the translated term as a new variable:
*)

私たちの簡単なタクティクは、変換された項を新しい変数として追加します：

[[
f := Imp'
         (Or' (And' (Atomic' 2) (Atomic' 1)) (And' (Atomic' 1) (Atomic' 0)))
         (And' (Atomic' 1) (Or' (Atomic' 2) (Atomic' 0))) : formula'
]]
*)
Abort.

(**
(* More work would be needed to complete the reflective tactic, as we must connect our new syntax type with the real meanings of formulas, but the details are the same as in our prior implementation with [quote]. *)

新しい構文型と式の実際の意味を結びつけなければならないので、
リフレクティブなタクティクを完成させるためにはもっと多くの作業が必要ですが、
詳細は以前の[quote]による実装と同じです。
*)

(* end thide *)

(* suhara: quote をみなおす。

Theorem mt3'' : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  --> y > z /\ (x < y \/ x < S y).
  intros.
  quote formulaDenote.
(* ここまででは、my_tauto, backward, forward は不要である。 *)
(* 奇妙なのは、formulaDenote が、formulaからPropの関数であるのに、
   ここでは、Prop から formula へ変換していることである。 *)
Abort.

Coq manual から：
10.3  quote
The tactic quote allows using Barendregt's so-called 2-level approach
without writing any ML code. Suppose you have a language L of
'abstract terms' and a type A of 'concrete terms' and a function f : L-> A.
If L is a simple inductive datatype and f a simple fixpoint,
quote f will replace the head of current goal by a convertible term of
the form (f t). L must have a constructor of type: A -> L.

抽象的な項Lから具体的な項A への関数 f : L->A があり、
Lが帰納型で、fが再帰関数なら、quote f は、現在のゴールを(f t)から変換する。
Lは、A->L型のコンストラクタが必要である。
つまり、formulaDenote : formula -> Prop に対して、
quote formulaDenote は、ゴールに対して、Prop -> formula を実行する。

これに対して、reify は ゴールに対して、直接、Prop -> formula をおこなうタクティクである。
*)

(*
(** * Building a Reification Tactic that Recurses Under Binders *)
 *)
(** * 束縛のもとで再帰する具象化タクティクを作る *)

(**
(* All of our examples so far have stayed away from reifying the syntax of terms that use such features as quantifiers and [fun] function abstractions.  Such cases are complicated by the fact that different subterms may be allowed to reference different sets of free variables.  Some cleverness is needed to clear this hurdle, but a few simple patterns will suffice.  Consider this example of a simple dependently typed term language, where a function abstraction body is represented conveniently with a Coq function. *)

これまでのすべての例では、量化子や、[fun]による関数抽象などの項の構文を具現化する形式
から離れていました。
そのような場合は、
異なる副項が自由変数の異なる集合を参照することを許されるという事実によって複雑になります。
このようなハードルを解消するためにはいくつかの巧妙さが必要ですが、
すこしの単純なパターンで十分です。
関数抽象の本体が便利にCoqの関数で表されている単純な依存型の言語の例を考えてみましょう。
 *)

Inductive type : Type :=
| Nat : type
| NatFunc : type -> type.

Inductive term : type -> Type :=
| Const : nat -> term Nat
| Plus : term Nat -> term Nat -> term Nat
| Abs : forall t, (nat -> term t) -> term (NatFunc t).

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | NatFunc t => nat -> typeDenote t
  end.

Fixpoint termDenote t (e : term t) : typeDenote t :=
  match e with
    | Const n => n
    | Plus e1 e2 => termDenote e1 + termDenote e2
    | Abs _ e1 => fun x => termDenote (e1 x)
  end.

(**
(* Here is a %\%naive%{}% first attempt at a reification tactic. *)

ここでは、具象化のタクティクで素朴(%\%naive%{}%)な最初の試みがあります。
*)

(* begin hide *)
Definition red_herring := O.
(* end hide *)
Ltac refl' e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(Plus r1 r2)

    | fun x : nat => ?E1 =>
      let r1 := refl' E1 in
        constr:(Abs (fun x => r1 x))

    | _ => constr:(Const e)
  end.

(**
(* Recall that a regular Ltac pattern variable [?X] only matches terms that _do not mention new variables introduced within the pattern_.  In our %\%naive%{}% implementation, the case for matching function abstractions matches the function body in a way that prevents it from mentioning the function argument!  Our code above plays fast and loose with the function body in a way that leads to independent problems, but we could change the code so that it indeed handles function abstractions that ignore their arguments.

正規のLtacのパターン変数[?X]は、
＿パターン内に導入された新しい変数について言及していない項＿
にのみマッチすることを想起してください。

(* suhara: fun x => ?E1 と fun a => F a はマッチしない。E1 = F a にならない。
ここでいう新しく導入された変数とは、a にあたる *)

素朴(%\%naive%{}%)な実装では、
関数の引数に言及することを妨げる方法です！
上記のコードは、独立した問題を引き起こすような方法で、
関数本体を高速かつ緩やかに実行しますが、コードを変更して、
引数を無視する関数抽象を実際に処理できるようにします。
*)

(*
   To handle functions in general, we will use the pattern variable form [@?X], which allows [X] to mention newly introduced variables that are declared explicitly.  A use of [@?X] must be followed by a list of the local variables that may be mentioned.  The variable [X] then comes to stand for a Gallina function over the values of those variables.  For instance: *)

関数を一般的に扱うために、パターンの変数の形式 [@?X]を使用して、
明示的に宣言された新しく導入された変数について[X]が言及するようにします。
[@?X]の使用のあとには、言及する可能性のあるローカル変数のリストを続ける必要があります。 

(* suhara: fun x => @?E1 x と fun a => F a はマッチする。E1 = F になる。 *)

変数[X]は、それらの変数の値に渡ってGallina関数を表します。 例えば：
 *)

Reset refl'.
(* begin hide *)
Reset red_herring.
Definition red_herring := O.
(* end hide *)
Ltac refl' e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(Plus r1 r2)

    | fun x : nat => @?E1 x =>              (* suhara: @をつける。 *)
      let r1 := refl' E1 in
        constr:(Abs r1)

    | _ => constr:(Const e)
  end.

(**
(* Now, in the abstraction case, we bind [E1] as a function from an [x] value to the value of the abstraction body.  Unfortunately, our recursive call there is not destined for success.  It will match the same abstraction pattern and trigger another recursive call, and so on through infinite recursion.  One last refactoring yields a working procedure.  The key idea is to consider every input to [refl'] as _a function over the values of variables introduced during recursion_. *)

抽象化の場合[E1]を、[x]の値から抽象化した本体の値への関数に、束縛します。
残念ながら、再帰呼び出しは成功すると決まったわけではありません。

同じ抽象パターンに一致し、別の再帰呼び出しを実行するなど、無限再帰を使用します。
最後の具象化によって作業手順が得られます。
重要なアイデアは、[refl']へのすべての入力を
＿再帰中に導入された変数の値に対する関数＿ として考えることです。

 *)

Reset refl'.
(* begin hide *)
Reset red_herring.
(* end hide *)
Ltac refl' e :=
  match eval simpl in e with
    | fun x : ?T => @?E1 x + @?E2 x =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(fun x => Plus (r1 x) (r2 x)) (* suhara: 返値を関数にする。 *)

    | fun (x : ?T) (y : nat) => @?E1 x y =>
      let r1 := refl' (fun p : T * nat => E1 (fst p) (snd p)) in
        constr:(fun u => Abs (fun v => r1 (u, v))) (* suhara: 返値を関数にする。 *)

    | _ => constr:(fun x => Const (e x)) (* suhara: 返値を関数にする。 *)
  end.

(**
(* Note how now even the addition case works in terms of functions, with [@?X] patterns.  The abstraction case introduces a new variable by extending the type used to represent the free variables.  In particular, the argument to [refl'] used type [T] to represent all free variables.  We extend the type to [T * nat] for the type representing free variable values within the abstraction body.  A bit of bookkeeping with pairs and their projections produces an appropriate version of the abstraction body to pass in a recursive call.  To ensure that all this repackaging of terms does not interfere with pattern matching, we add an extra [simpl] reduction on the function argument, in the first line of the body of [refl'].
*)


[@?X]のパターンでは、関数の形で加算の場合でもどのように動作するのか注意してください。
抽象化の場合、自由変数を表すために使用される型を拡張することによって新しい変数が導入されます。
すべての自由変数を表すために[T]型を使用しました。
抽象化の本体内の自由変数値を表す型の型を[T * nat]に拡張します。
ペアとその射影(projection)による
少しのブックキーピング(a bit of bookkeeping)は、
再帰呼び出しで渡す抽象本体の適切なバージョンを生成します。
このような項の再パッケージングがすべてパターンマッチングを妨げないようにするために、
[refl']の本体の最初の行に関数引数を追加します。

(*
   Now one more tactic provides an example of how to apply reification.  Let us consider goals that are equalities between terms that can be reified.  We want to change such goals into equalities between appropriate calls to [termDenote]. *)

今やもうひとつのタクティクが、具象化を適用する方法の例を提供します。
具象化できる項どうしの等式であるゴールを考えてみましょう。
このようなゴールを[termDenote]への適切な呼び出しの間で等式に変更したいと考えています。
 *)

Ltac refl :=
  match goal with
    | [ |- ?E1 = ?E2 ] =>
      let E1' := refl' (fun _ : unit => E1) in
      let E2' := refl' (fun _ : unit => E2) in
        change (termDenote (E1' tt) = termDenote (E2' tt));
          cbv beta iota delta [fst snd]
  end.

Goal (fun (x y : nat) => x + y + 13) = (fun (_ z : nat) => z).
  refl.
(** %\vspace{-.15in}%[[
  ============================
   termDenote
     (Abs
        (fun y : nat =>
         Abs (fun y0 : nat => Plus (Plus (Const y) (Const y0)) (Const 13)))) =
   termDenote (Abs (fun _ : nat => Abs (fun y0 : nat => Const y0)))
]]
*)

Abort.

(**
(* Our encoding here uses Coq functions to represent binding within the terms we reify, which makes it difficult to implement certain functions over reified terms.  An alternative would be to represent variables with numbers.  This can be done by writing a slightly smarter reification function that identifies variable references by detecting when term arguments are just compositions of [fst] and [snd]; from the order of the compositions we may read off the variable number.  We leave the details as an exercise (though not a trivial one!) for the reader. *)

ここでのエンコーディングは、Coqの関数を使用して、妥当な条件で束縛を表現しているため、
特定の関数機能を実現するのが難しくなります。

また、変数を数値で表現する方法もあります。
これは、項の引数が[fst]と[snd]の合成だけであることを検出することによって、
変数参照を識別する若干スマートな具象化関数を書くことによって行うことができます。
構成の順序から、変数の数値を読み取ることができます。
読者のために詳細を練習問題（しかし、自明なものではありません！）として残しています。
 *)

(* END *)

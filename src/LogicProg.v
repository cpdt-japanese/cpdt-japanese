(* Copyright (c) 2011-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)

Require Import List Omega.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(**
(* %\part{Proof Engineering}

   \chapter{Proof Search by Logic Programming}% *)

   %\part{証明工学}

   \chapter{論理プログラミングによる証明探索}% *)

(**
(* The Curry-Howard correspondence tells us that proving is "just" programming, but the pragmatics of the two activities are very different.  Generally we care about properties of a program besides its type, but the same is not true about proofs.  Any proof of a theorem will do just as well.  As a result, automated proof search is conceptually simpler than automated programming.

   The paradigm of %\index{logic programming}%logic programming%~\cite{LogicProgramming}%, as embodied in languages like %\index{Prolog}%Prolog%~\cite{Prolog}%, is a good match for proof search in higher-order logic.  This chapter introduces the details, attempting to avoid any dependence on past logic programming experience. *)

カリー・ハワード対応は、証明をすることが「まさしく」プログラミングであることを示しますが、
このふたつの活動の実際はとても異なります。
私たちは、一般に、プログラムの型のみならず属性について注意を払いますが、
証明についてはそうではありません。定理のどんな証明でも同様です。
結果として、自動化された証明探索は自動化されたプログラミングよりも概念的に簡単です。

%\index{Prolog}%Prolog%~\cite{Prolog}% などの言語に組み入れられた
論理プログラミング %\index{logic programming}%logic programming%~\cite{LogicProgramming}% の
パラダイムは高階論理の証明探索にとてもよく適合します。
この章では、過去の論理プログラミングの経験がなくてもよいように、詳細を紹介します。
 *)

(*
(** * Introducing Logic Programming *)
 *)
(** * 論理プログラミング入門 *)

(**
(* Recall the definition of addition from the standard library. *)

標準ライブラリから加算の定義を思いだしましょう。
 *)

Print plus.
(** %\vspace{-.15in}%[[
plus = 
fix plus (n m : nat) : nat := match n with
                              | 0 => m
                              | S p => S (plus p m)
                              end

]]

(* This is a recursive definition, in the style of functional programming.  We might also follow the style of logic programming, which corresponds to the inductive relations we have defined in previous chapters. *)

これは関数プログラミングのスタイルにおける再帰的な定義です。
また、前の章で定義した帰納的関係に対応する論理プログラミングのスタイルにも従います。
 *)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(**
(* Intuitively, a fact [plusR n m r] only holds when [plus n m = r].  It is not hard to prove this correspondence formally. *)

直観的にいうと、事実 [plusR n m r] は、[plus n m = r] であるときだけ成り立ちます。
この対応を形式的に証明することは難しくありません。
*)

(* begin thide *)
Hint Constructors plusR.
(* end thide *)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
(* begin thide *)
  induction n; crush.
Qed.
(* end thide *)

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
(* begin thide *)
  induction 1; crush.
Qed.
(* end thide *)

(**
(* With the functional definition of [plus], simple equalities about arithmetic follow by computation. *)

[plus] の関数定義では、算術についての簡単な等式は計算に従います。
*)

Example four_plus_three : 4 + 3 = 7.
(* begin thide *)
  reflexivity.
Qed.
(* end thide *)

(* begin hide *)
(* begin thide *)
Definition er := @eq_refl.
(* end thide *)
(* end hide *)

Print four_plus_three.
(** %\vspace{-.15in}%[[
four_plus_three = eq_refl
]]

(* With the relational definition, the same equalities take more steps to prove, but the process is completely mechanical.  For example, consider this simple-minded manual proof search strategy.  The steps with error messages shown afterward will be omitted from the final script.
*)

関係の定義では、同じ等式は証明するのにより多くのステップをとりますが、
そのプロセスは完全に機械的です。
例えば、simple-minded な手動の証明探索の戦略を考えよう。
後でエラーメッセージの表示された手順は、最終的なスクリプトから省略されます。
*)

Example four_plus_three' : plusR 4 3 7.
(* begin thide *)
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?24 ?24" with "plusR 4 3 7".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?25 ?25" with "plusR 3 3 6".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?26 ?26" with "plusR 2 3 5".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?27 ?27" with "plusR 1 3 4".
>> *)
  apply PlusS.
  apply PlusO.

(**
(* At this point the proof is completed.  It is no doubt clear that a simple procedure could find all proofs of this kind for us.  We are just exploring all possible proof trees, built from the two candidate steps [apply PlusO] and [apply PlusS].  The built-in tactic %\index{tactics!auto}%[auto] follows exactly this strategy, since above we used %\index{Vernacular commands!Hint Constructors}%[Hint Constructors] to register the two candidate proof steps as hints. *)

この時点で証明が完了します。
単純な手続きが、この種類の全ての証明を見つけられることは、明かに間違いありません。
ふたつの候補となるステップ [apply PlusO] と [apply PlusS] からなる可能な証明木のすべてを探検しただけです。
先に %\index{Vernacular commands!Hint Constructors}%[Hint Constructors] を
ふたつの候補となる 証明のステップ のヒントとして登録するのに使ったので、
組み込みタクティク %\index{tactics!auto}%[auto] は、この戦略に従います。
 *)
  
Restart.
  auto.
Qed.
(* end thide *)

Print four_plus_three'.
(** %\vspace{-.15in}%[[
four_plus_three' = PlusS (PlusS (PlusS (PlusS (PlusO 3))))
]]
*)

(**
(* Let us try the same approach on a slightly more complex goal. *)
すこし複雑なゴールについて同じアプローチを試してみましょう。
*)

Example five_plus_three : plusR 5 3 8.
(* begin thide *)
  auto.

(**
(* This time, [auto] is not enough to make any progress.  Since even a single candidate step may lead to an infinite space of possible proof trees, [auto] is parameterized on the maximum depth of trees to consider.  The default depth is 5, and it turns out that we need depth 6 to prove the goal. *)

この場合は、[auto] は進捗をするのに十分ではありません。

単一の候補のステップは、可能な証明木の無限のスペースに導くかもしれないので、
[auto] は考慮するべき最大の木の深さをパラメータとして与えられるようになっています。
ディフォルトの深さは 5 で、ゴールを証明するために深さ 6 が必要ならそのように設定します。
 *)
  
  auto 6.

(**
(* Sometimes it is useful to see a description of the proof tree that [auto] finds, with the %\index{tactics!info}%[info] tactical.  (This tactical is not available in Coq 8.4 as of this writing, but I hope it reappears soon.  The special case %\index{tactics!info\_auto}%[info_auto] tactic is provided as a chatty replacement for [auto].) *)

しばしば、%\index{tactics!info}%[info] タクティカルは、
[auto] が見つける証明木の記述を見るのに便利です。
 (このタクティカルは、これを書いている Coq 8.4 では使用できませんが、
すぐに再登場することを期待しています。
特別な場合の %\index{tactics!info\_auto}%[info_auto] タクティクは、
[auto] の饒舌な置き換えとして提供されます。)
 *)
  
Restart.
  info auto 6.
(** %\vspace{-.15in}%[[
 == apply PlusS; apply PlusS; apply PlusS; apply PlusS; 
    apply PlusS; apply PlusO.
]]
*)
Qed.
(* end thide *)

(**
(* The two key components of logic programming are%\index{backtracking}% _backtracking_ and%\index{unification}% _unification_.  To see these techniques in action, consider this further silly example.  Here our candidate proof steps will be reflexivity and quantifier instantiation. *)

論理プログラミングのふたつのキーとなるコンポーネントは、
%\index{backtracking}% _backtracking_ バックトラッキングと
%\index{unification}% _unification_ ユニフィケーションです。

これらの技法を実際に見るために、さらに単純(silly)な例を考えます。
ここでは、候補となる証明のステップが反射的で、量化子を具体化します。
(quantifier instantiation)
*)
  
Example seven_minus_three : exists x, x + 3 = 7.
(* begin thide *)
(**
(* For explanatory purposes, let us simulate a user with minimal understanding of arithmetic.  We start by choosing an instantiation for the quantifier.  Recall that [ex_intro] is the constructor for existentially quantified formulas. *)

説明のために、計算について最小限の理解をもったユーザーを考えましょう。
量化子を具体化することを選ぶことによって始めます。
[ex_intro] は、存在量化された式のためのコンストラクタであることを思い出しましょう。
*)

  apply ex_intro with 0.
(** %\vspace{-.2in}%[[
  reflexivity.
]]
%\vspace{-.2in}%
<<
  Error: Impossible to unify "7" with "0 + 3".
>>

(* This seems to be a dead end.  Let us _backtrack_ to the point where we ran [apply] and make a better alternate choice. *)

これは、デッドエンドのように見えます。
[apply] を実行した箇所に _backtrack_ バックトラックして、よりよい別の選択をします。
*)

Restart.
  apply ex_intro with 4.
  reflexivity.
Qed.
(* end thide *)

(**
(* The above was a fairly tame example of backtracking.  In general, any node in an under-construction proof tree may be the destination of backtracking an arbitrarily large number of times, as different candidate proof steps are found not to lead to full proof trees, within the depth bound passed to [auto].

   Next we demonstrate unification, which will be easier when we switch to the relational formulation of addition. *)

これは、かなり退屈なバックトラッキングの例です。
一般に、[auto] に渡された深さの上限までなら、
証明木を導くために、異なった証明のステップの候補が見つからない場合は、
証明の途中の(under-construction)の証明木のどんなノードでも、
任意の回数のバックトラッキングの行き先になるでしょう。

次に、加算についての関係式(formulation)を切り替えるとき、
それを簡単にするユニフィケーションの実演をします。
*)

Example seven_minus_three' : exists x, plusR x 3 7.
(* begin thide *)
(**
(* We could attempt to guess the quantifier instantiation manually as before, but here there is no need.  Instead of [apply], we use %\index{tactics!eapply}%[eapply], which proceeds with placeholder%\index{unification variable}% _unification variables_ standing in for those parameters we wish to postpone guessing. *)

以前とおなじように、手作業で量化子の具体化を推測しようとしますが、ここではそれは必要ありません。
[apply] の代わりに、推測を延期したいそれらのパラメータの代わりに
プレースホルダー %\index{unification variable}% _unification variables_ 
ユニフィケーション変数をつかう(proceeds with) %\index{tactics!eapply}%[eapply] を使用します。
 *)

  eapply ex_intro.
(** [[
1 subgoal
  
  ============================
   plusR ?70 3 7
]]

(* Now we can finish the proof with the right applications of [plusR]'s constructors.  Note that new unification variables are being generated to stand for new unknowns. *)

いまでは、正しく [plusR] のコンストラクタを適用することで証明を終了することができます。
なお、新しいユニフィケーション変数は新しい unknown として生成されます。
 *)
  
  apply PlusS.
(** [[
  ============================
   plusR ?71 3 6
]]
*)
  apply PlusS. apply PlusS. apply PlusS.
(** [[
  ============================
   plusR ?74 3 3
]]
*)
  apply PlusO.

(**
(* The [auto] tactic will not perform these sorts of steps that introduce unification variables, but the %\index{tactics!eauto}%[eauto] tactic will.  It is helpful to work with two separate tactics, because proof search in the [eauto] style can uncover many more potential proof trees and hence take much longer to run. *)

[auto] タクティクはユニフィケーション変数を導入するステップの順番を実行しませんが、
%\index{tactics!eauto}%[eauto] タクティクは実行します。
[eauto] スタイルの証明探索は、より多くの可能な証明木を網羅できず、
それゆえ、実行するのにより長く時間が掛かるので、このふたつのタクティクを使い分けると便利です。
*)

Restart.
  info eauto 6.
(** %\vspace{-.15in}%[[
 == eapply ex_intro; apply PlusS; apply PlusS; 
    apply PlusS; apply PlusS; apply PlusO.
]]
*)
Qed.
(* end thide *)

(**
(* This proof gives us our first example where logic programming simplifies proof search compared to functional programming.  In general, functional programs are only meant to be run in a single direction; a function has disjoint sets of inputs and outputs.  In the last example, we effectively ran a logic program backwards, deducing an input that gives rise to a certain output.  The same works for deducing an unknown value of the other input. *)

この証明は、論理プログラミングが、関数プログラミングと比べて、
証明探索を単純化する最初の例を与えます。
一般に、関数型プログラムは、単に一方方向に実行されることを意味し、
関数は入力と出力の重なりのない集合(disjoint sets)です。
最後の例では、特定の出力を生じさせる入力を推定するために、
論理型プログラムを後ろ向きに効率的に実行しました。
他の入力の未知の値を推測するために、同じことが働きます。
 *)

Example seven_minus_four' : exists x, plusR 4 x 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

(** 
(* By proving the right auxiliary facts, we can reason about specific functional programs in the same way as we did above for a logic program.  Let us prove that the constructors of [plusR] have natural interpretations as lemmas about [plus].  We can find the first such lemma already proved in the standard library, using the %\index{Vernacular commands!SearchRewrite}%[SearchRewrite] command to find a library function proving an equality whose lefthand or righthand side matches a pattern with wildcards. *)

正しい補助的な事実を証明するために、(* ?? ただし、ここから等式の証明に話題が移る *)
具体的な関数プログラムについて、上で論理プログラムにしたのと同じ方法で、
理由づけすることができます。

[plusR] のコンストラクタが、[plus] についての補題を自然に翻訳することを証明しましょう。

最初に、左辺または右辺がワイルドカードとマッチする等式を証明するライブラリ関数を見つけるための
コマンドである %\index{Vernacular commands!SearchRewrite}%[SearchRewrite] コマンドを使って、
それらの補題が、既に標準ライブラリで証明されていることを見つけることができます。
 *)

(* begin thide *)
SearchRewrite (O + _).
(** %\vspace{-.15in}%[[
plus_O_n: forall n : nat, 0 + n = n
]]

(* The command %\index{Vernacular commands!Hint Immediate}%[Hint Immediate] asks [auto] and [eauto] to consider this lemma as a candidate step for any leaf of a proof tree. *)

コマンド %\index{Vernacular commands!Hint Immediate}%[Hint Immediate] は、
[auto] と [eauto] が、この補題を証明木の任意の葉の候補として考慮するように依頼します。
*)

Hint Immediate plus_O_n.

(**
(* The counterpart to [PlusS] we will prove ourselves. *)

[PlusS] に対応するものを証明します。
*)

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
  crush.
Qed.

(**
(* The command %\index{Vernacular commands!Hint Resolve}%[Hint Resolve] adds a new candidate proof step, to be attempted at any level of a proof tree, not just at leaves. *)

コマンド %\index{Vernacular commands!Hint Resolve}%[Hint Resolve] は、
証明木の葉のみならず、任意のレベルにおいて試みられる新しい証明のステップの候補に加えます。
*)

Hint Resolve plusS.
(* end thide *)

(**
(* Now that we have registered the proper hints, we can replicate our previous examples with the normal, functional addition [plus]. *)

適切なヒントを登録したので、これまでの例を通常の機能追加[plus]で再現できます。
*)

Example seven_minus_three'' : exists x, x + 3 = 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

Example seven_minus_four : exists x, 4 + x = 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

(**
(* This new hint database is far from a complete decision procedure, as we see in a further example that [eauto] does not finish. *)

さらなる例では [eauto] が終了しないことがわかるので、この新しいヒントデータベースは、
完全な決定可能な手続き(complete decision procedure)からかけ離れています。
 *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
(* begin thide *)
  eauto 6.
Abort.
(* end thide *)

(**
(* A further lemma will be helpful. *)

さらなる補題が便利でしょう。
 *)

(* begin thide *)
Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
  crush.
Qed.

Hint Resolve plusO.
(* end thide *)

(**
(* Note that, if we consider the inputs to [plus] as the inputs of a corresponding logic program, the new rule [plusO] introduces an ambiguity.  For instance, a sum [0 + 0] would match both of [plus_O_n] and [plusO], depending on which operand we focus on.  This ambiguity may increase the number of potential search trees, slowing proof search, but semantically it presents no problems, and in fact it leads to an automated proof of the present example. *)

もし、 [plus] への入力を論理プログラムに関連する入力として考えるなら、
新しいルール [plus0] は曖昧さを導きいれます。
例えば、和 [0 + 0] は、我々の注目するオペランドに依存して、
[plus_0_n] と [plus0] のどちらにもマッチします。

この曖昧さは潜在的な探索木の数を増やし、証明探索を遅くし、
意味的には問題を供さないが、実際に自動化した証明につながります。
 *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
(* begin thide *)
  eauto 7.
Qed.
(* end thide *)

(**
(* Just how much damage can be done by adding hints that grow the space of possible proof trees?  A classic gotcha comes from unrestricted use of transitivity, as embodied in this library theorem about equality: *)

可能な証明木のスペースを広げるヒントを追加することが、どれだけ損害を被ることになるでしょうか？
古典的なものは、このライブラリの定理で具体的にしたように、
等式についての推移性(transitivity)の無制限な使用から来ています。
 *)

Check eq_trans.
(** %\vspace{-.15in}%[[
eq_trans
     : forall (A : Type) (x y z : A), x = y -> y = z -> x = z
]]
*)

(**
(* Hints are scoped over sections, so let us enter a section to contain the effects of an unfortunate hint choice. *)

ヒントはセクションのスコープ上にあるので、
不幸なヒントの選択の効果を含むためにセクションに入ります。
*)

Section slow.
  Hint Resolve eq_trans.

  (**
(* The following fact is false, but that does not stop [eauto] from taking a very long time to search for proofs of it.  We use the handy %\index{Vernacular commands!Time}%[Time] command to measure how long a proof step takes to run.  None of the following steps make any progress. *)

以下の事実は間違いですが、[eauto] のステップは、
その証明の検索に非常に長い時間を費やすことを止めません。
実行にいかに長くの時間を要したかを測るのために
便利なコマンド %\index{Vernacular commands!Time}%[Time] を使います。
以下のステップは何も進ませません。
   *)
  
  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.u,0.s)
>>
*)

    Time eauto 2.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.u,0.s)
>>
*)

    Time eauto 3.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.008u,0.s)
>>
*)

    Time eauto 4.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.068005u,0.004s)
>>
*)

    Time eauto 5.
(** %\vspace{-.15in}%
<<
Finished transaction in 2. secs (1.92012u,0.044003s)
>>
*)

(**
(* We see worrying exponential growth in running time, and the %\index{tactics!debug}%[debug] tactical helps us see where [eauto] is wasting its time, outputting a trace of every proof step that is attempted.  The rule [eq_trans] applies at every node of a proof tree, and [eauto] tries all such positions. *)

実行時間が指数的に増加することを心配なら、 %\index{tactics!debug}%[debug] タクティカルは、
[eauto] がどこで時間を無駄にしているのかを見て、試行されるすべての証明ステップのトレースを出力するのに役立ちます。
ルール [eq_trans] は証明木の各ノードでapplyし、[eauto] はがそれらの全ての位置で試します。
 *)
    
(* begin hide *)
(* begin thide *)
Definition syms := (eq_sym, plus_n_O, eq_add_S, f_equal2).
(* end thide *)
(* end hide *)

    debug eauto 3.
(** [[
1 depth=3 
1.1 depth=2 eapply ex_intro
1.1.1 depth=1 apply plusO
1.1.1.1 depth=0 eapply eq_trans
1.1.2 depth=1 eapply eq_trans
1.1.2.1 depth=1 apply plus_n_O
1.1.2.1.1 depth=0 apply plusO
1.1.2.1.2 depth=0 eapply eq_trans
1.1.2.2 depth=1 apply @eq_refl
1.1.2.2.1 depth=0 apply plusO
1.1.2.2.2 depth=0 eapply eq_trans
1.1.2.3 depth=1 apply eq_add_S ; trivial
1.1.2.3.1 depth=0 apply plusO
1.1.2.3.2 depth=0 eapply eq_trans
1.1.2.4 depth=1 apply eq_sym ; trivial
1.1.2.4.1 depth=0 eapply eq_trans
1.1.2.5 depth=0 apply plusO
1.1.2.6 depth=0 apply plusS
1.1.2.7 depth=0 apply f_equal (A:=nat)
1.1.2.8 depth=0 apply f_equal2 (A1:=nat) (A2:=nat)
1.1.2.9 depth=0 eapply eq_trans
]]
*)
  Abort.
End slow.

(**
(* Sometimes, though, transitivity is just what is needed to get a proof to go through automatically with [eauto].  For those cases, we can use named%\index{hint databases}% _hint databases_ to segregate hints into different groups that may be called on as needed.  Here we put [eq_trans] into the database [slow]. *)

ときには、しかし、推移性(transitivity)は、[eauto]で自動的に通過する証明を得るのに必要なものです。
この場合は、必要によって呼び出すことのできる、異なった別のグループ分離するために、
名前を付けた %\index{hint databases}% _hint databases_ ヒントデータベースを使うことができます。
ここで、[eq_trans] をデータベース [slow] に置きます。
 *)

(* begin thide *)
Hint Resolve eq_trans : slow.
(* end thide *)

Example from_one_to_zero : exists x, 1 + x = 0.
(* begin thide *)
  Time eauto.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.004u,0.s)
>>

(* This [eauto] fails to prove the goal, but at least it takes substantially less than the 2 seconds required above! *)

この [eauto] は、ゴールを証明するのに失敗しますが、
しかし、少なくともそれは上記の2秒よりも実質的に短い時間で済みます！
*)
Abort.
(* end thide *)

(**
(* One simple example from before runs in the same amount of time, avoiding pollution by transitivity. *)

上のひとつの単純な例は、推移性(transitivity)によって汚染されることなしに、
同じ合計時間で実行されます。
 *)

Example seven_minus_three_again : exists x, x + 3 = 7.
(* begin thide *)
  Time eauto 6.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.004001u,0.s)
>>
%\vspace{-.2in}% *)

Qed.
(* end thide *)

(**
(* When we _do_ need transitivity, we ask for it explicitly. *)

推移性を必要とするとき、それを明示的に求めます。
 *)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
(* begin thide *)
  info eauto with slow.
(** %\vspace{-.2in}%[[
 == intro x; intro y; intro H; intro H0; simple eapply ex_intro; 
    apply plusS; simple eapply eq_trans.
    exact H.
    
    exact H0.
]]
*)
Qed.
(* end thide *)

(**
(* The [info] trace shows that [eq_trans] was used in just the position where it is needed to complete the proof.  We also see that [auto] and [eauto] always perform [intro] steps without counting them toward the bound on proof tree depth. *)

[info] のトレースは、[eq_trans] がちょうど証明を完成するのに必要な位置で使われていることを示します。
[auto] と [eauto] は、[intro] を、ステップを証明木の深さの上限をに向かって数えるとなしに、
いつも実行します。(* [intro] の実行は depth のカウントに含まれない、ということだろう。 *)
 *)

(*
(** * Searching for Underconstrained Values *)
*)
(** * 拘束されていない値を探す *)

(**
(* Recall the definition of the list length function. *)

リストの length 関数の定義を思いだしましょう。
 *)

Print length.
(** %\vspace{-.15in}%[[
length = 
fun A : Type =>
fix length (l : list A) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (length l')
  end
]]

(* This function is easy to reason about in the forward direction, computing output from input. *)

この関数は、前向きの方向に、入力から出力に計算するので簡単です。
 *)

Example length_1_2 : length (1 :: 2 :: nil) = 2.
  auto.
Qed.

Print length_1_2.
(** %\vspace{-.15in}%[[
length_1_2 = eq_refl
]]

(* As in the last section, we will prove some lemmas to recast [length] in logic programming style, to help us compute inputs from outputs. *)

最後の節で、出力からの入力を計算するのを助けるために、
論理プログラミングのスタイルで [length] を再構築するためのいくつかの補題を証明します。
 *)

(* begin thide *)
Theorem length_O : forall A, length (nil (A := A)) = O.
  crush.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
  crush.
Qed.

Hint Resolve length_O length_S.
(* end thide *)

(**
(* Let us apply these hints to prove that a [list nat] of length 2 exists.  (Here we register [length_O] with [Hint Resolve] instead of [Hint Immediate] merely as a convenience to use the same command as for [length_S]; [Resolve] and [Immediate] have the same meaning for a premise-free hint.) *)

長さ2の [list nat] が存在することを証明するためのヒントとして、これらを適用しましょう。
（ここで、単に [length_S] と同じコマンドを使うのが便利なので、
[length_O] を [Hint Immediate] ではなく [Hint Resolve] で登録しています。
[Resolve] と [Immediate] は、前提のない定理をヒント
(* premise-free hint、この場合は length_O *)
にするなら同じ意味を持ちます。
*)

Example length_is_2 : exists ls : list nat, length ls = 2.
(* begin thide *)
  eauto.
(** <<
No more subgoals but non-instantiated existential variables:
Existential 1 = ?20249 : [ |- nat]
Existential 2 = ?20252 : [ |- nat]
>>

(* Coq complains that we finished the proof without determining the values of some unification variables created during proof search.  The error message may seem a bit silly, since _any_ value of type [nat] (for instance, 0) can be plugged in for either variable!  However, for more complex types, finding their inhabitants may be as complex as theorem-proving in general.

The %\index{Vernacular commands!Show Proof}%[Show Proof] command shows exactly which proof term [eauto] has found, with the undetermined unification variables appearing explicitly where they are used. *)

Coqは、証明探索の途中で導入された幾つかのユニフィケーション変数を
決定することなしに、証明を終えたことに文句をいいます。
型 [nat] の ＿任意＿ の値（たとば 0）をどちらの変数にも差し込むことができますから、
このエラーメッセージは少し馬鹿げて(silly)います！
しかし、より複雑な型では、それらの値(inhabitants)を見つけることは、
一般的に定理証明と同じくらい複雑かもしれません。

%\index{Vernacular commands!Show Proof}%[Show Proof] コマンドは、
それらが使われたところで明示的に出現する未定のユニフィケーション変数と一緒に、
[eauto] 見つけたものを正確に示します。
*)

  Show Proof.
(** <<
Proof: ex_intro (fun ls : list nat => length ls = 2)
         (?20249 :: ?20252 :: nil)
         (length_S ?20249 (?20252 :: nil)
            (length_S ?20252 nil (length_O nat)))
>>
%\vspace{-.2in}% *)

Abort.
(* end thide *)

(**
(* We see that the two unification variables stand for the two elements of the list.  Indeed, list length is independent of data values.  Paradoxically, we can make the proof search process easier by constraining the list further, so that proof search naturally locates appropriate data elements by unification.  The library predicate [Forall] will be helpful. *)

そのリストのふたつの要素を表わす、ふたつのユニフィケーション変数があります。
しかしながら、リストの長さはデータの値と独立です。
証明探索はユニフィケーションによって適切なデータの要素を自然に見つけ出すので、
逆説的に、リストの制約によって証明探索のプロセスはより簡単になります。
ライブラリ述語 [Forall] は便利でしょう。
 *)

(* begin hide *)
(* begin thide *)
Definition Forall_c := (@Forall_nil, @Forall_cons).
(* end thide *)
(* end hide *)

Print Forall.
(** %\vspace{-.15in}%[[
Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A),
                  P x -> Forall P l -> Forall P (x :: l)
]]
*)

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 1) ls.
(* begin thide *)
  eauto 9.
Qed.
(* end thide *)

(**
(* We can see which list [eauto] found by printing the proof term. *)

証明の項を印刷することによって、[eauto] がどのリストを見つけたかを見ることができます。
 *)

(* begin hide *)
(* begin thide *)
Definition conj' := (conj, le_n).
(* end thide *)
(* end hide *)

Print length_is_2.
(** %\vspace{-.15in}%[[
length_is_2 = 
ex_intro
  (fun ls : list nat => length ls = 2 /\ Forall (fun n : nat => n >= 1) ls)
  (1 :: 1 :: nil)
  (conj (length_S 1 (1 :: nil) (length_S 1 nil (length_O nat)))
     (Forall_cons 1 (le_n 1)
        (Forall_cons 1 (le_n 1) (Forall_nil (fun n : nat => n >= 1)))))
]]
*)

(**
(* Let us try one more, fancier example.  First, we use a standard higher-order function to define a function for summing all data elements of a list. *)

もうひとつ、奇妙な(fancier)例を見てみましょう。
最初に、ひとつのリストのすべてのデータ要素を合計するための関数を定義するために
標準の高階関数を使います。
 *)

Definition sum := fold_right plus O.

(**
(* Another basic lemma will be helpful to guide proof search. *)

他の基本的な補題は、証明探索を導くのに便利です。
 *)

(* begin thide *)
Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
  crush.
Qed.

Hint Resolve plusO'.

(**
(* Finally, we meet %\index{Vernacular commands!Hint Extern}%[Hint Extern], the command to register a custom hint.  That is, we provide a pattern to match against goals during proof search.  Whenever the pattern matches, a tactic (given to the right of an arrow [=>]) is attempted.  Below, the number [1] gives a priority for this step.  Lower priorities are tried before higher priorities, which can have a significant effect on proof search time. *)

最後に、カスタムヒントを登録するためのコマンド
%\index{Vernacular commands!Hint Extern}%[Hint Extern] を見ます。
これは、証明探索の間にゴールに対してマッチするパターンを(*我々が*)提供します。
ひとたび、パターンがマッチしたら、タクティク（矢印 [=>] の右辺で与えられた) が試みられます。
次に、数字 [1] は、このステップの優先度を与えます。
低い優先度は高い優先度の前に試みられ、
それは、証明探索の時間に大きな影響をもたらすことができます。
 *)

Hint Extern 1 (sum _ = _) => simpl.
(* end thide *)

(**
(* Now we can find a length-2 list whose sum is 0. *)

ここで、合計が0である長さ2のリストを見つけることができます。
*)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
(* begin thide *)
  eauto 7.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum.
(* end hide *)

(**
(* Printing the proof term shows the unsurprising list that is found.  Here is an example where it is less obvious which list will be used.  Can you guess which list [eauto] will choose? *)

証明の項を印刷することは（で）、見つかったなんの不思議もない(unsurprising)リストを示します。
ここに、どのリストが使用されるのかが明白でない例があります。
[eauto] が選んだリストがどれか判りますか？

(* suhara: 日本語版では 「42」 についての訳注が必要かもしれませんね。半ページくらい。 *)
 *)

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
(* begin thide *)
  eauto 15.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum'.
(* end hide *)

(**
(* We will give away part of the answer and say that the above list is less interesting than we would like, because it contains too many zeroes.  A further constraint forces a different solution for a smaller instance of the problem. *)

上記のリストはあまりにも多くのゼロが含まれているので、
私たちは答えの一部を放棄して、望むよりも面白くないと言うでしょう。
さらなる制約は、問題のより小さい具体例(インスタンス)に対して、異なる答えを強制します。
 *)

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
(* begin thide *)
  eauto 11.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum''.
(* end hide *)

(**
(* We could continue through exercises of this kind, but even more interesting than finding lists automatically is finding _programs_ automatically. *)

この種類の練習を通して続けることができましたが、
リストを自動的に検索するよりもさらに興味深いのは ＿プログラム＿ を自動的に見つけることでしょう。
*)

(*
(** * Synthesizing Programs *)
 *)
(** * プログラムの合成 *)

(**
(* Here is a simple syntax type for arithmetic expressions, similar to those we have used several times before in the book.  In this case, we allow expressions to mention exactly one distinguished variable. *)

ここに算術式の単純な構文の型があります。これは、本書で以前に数回使用したものと似ています。
この場合、ちょうどひとつだけの識別された変数を式のなかに言及することができます。
(* 変数は複数個使えない *)
 *)

Inductive exp : Set :=
| Const : nat -> exp
| Var : exp
| Plus : exp -> exp -> exp.

(**
(* An inductive relation specifies the semantics of an expression, relating a variable value and an expression to the expression value. *)

帰納的な関係は式の意味を指定し、変数値と式を式の値に関連付けます。
 *)

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

(* begin thide *)
Hint Constructors eval.
(* end thide *)

(**
(* We can use [auto] to execute the semantics for specific expressions. *)

[auto] を 特定の式の意味を実行するために使えます。
*)

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var)).
(* begin thide *)
  auto.
Qed.
(* end thide *)

(**
(* Unfortunately, just the constructors of [eval] are not enough to prove theorems like the following, which depends on an arithmetic identity. *)

不幸にも、[eval] のコンストラクタは、次のように、
算術的な同一性 (* suhara: x + (8 + x) と 2 * x + 8 が同じであること *) に依存するような定理
を証明するのに十分ではありません。
 *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
Abort.
(* end thide *)

(**
(* To help prove [eval1'], we prove an alternate version of [EvalPlus] that inserts an extra equality premise.  This sort of staging is helpful to get around limitations of [eauto]'s unification: [EvalPlus] as a direct hint will only match goals whose results are already expressed as additions, rather than as constants.  With the alternate version below, to prove the first two premises, [eauto] is given free reign in deciding the values of [n1] and [n2], while the third premise can then be proved by [reflexivity], no matter how each of its sides is decomposed as a tree of additions. *)

[eval1'] を証明するのを助けるために、別の等式の前提を挿入する、
別なバージョンの [EvalPlus] を証明します。

この種類の演出は、[eauto] のユニフィケーションの制限を回避するのに役に立ちます。
直接的なヒントとしての[EvalPlus]は、
結果が既に定数ではなく加算として表現されているゴールにのみ一致します。

下の代替バージョンでは、加算の木がどのように分解されたとしても、
最初の2つの前提を証明するために、
[eauto] は [n1] と [n2] の値を決める際に自由な範囲(regin)を与え、
3番目の前提は [reflexivity] によって証明されます。
 *)

(* begin thide *)
Theorem EvalPlus' : forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  crush.
Qed.

Hint Resolve EvalPlus'.

(**
(* Further, we instruct [eauto] to apply %\index{tactics!omega}%[omega], a standard tactic that provides a complete decision procedure for quantifier-free linear arithmetic.  Via [Hint Extern], we ask for use of [omega] on any equality goal.  The [abstract] tactical generates a new lemma for every such successful proof, so that, in the final proof term, the lemma may be referenced in place of dropping in the full proof of the arithmetic equality. *)

さらに、[eauto] を
量化子のない線形算術(quantifier-free linear arithmetic)
のための完全な決定手順を提供する標準タクティクである
%\index{tactics!omega}%[omega] に適用させます。
[Hint Extern] を通して、どんな等式のゴールに対してでも [omega] を使うように要求します。

[abstract] タクティカルは、成功した証明のそれぞれに対して新しい補題を生成し、
最後の証明項において、
その補題は、算術的に等しいこと(arithmetic equality)の全体の証明
を置き換える箇所で参照されます。
 *)

Hint Extern 1 (_ = _) => abstract omega.
(* end thide *)

(**
(* Now we can return to [eval1'] and prove it automatically. *)

[eval1'] に戻って、それを自動的に証明します。
 *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
(*
Restart.                                    (* suhara *)
intros var.
eapply EvalPlus'.
- apply EvalVar.
- apply EvalPlus.
  + apply EvalConst.
  + apply EvalVar.
- omega.
*)
Qed.
(* end thide *)

Print eval1'.
(** %\vspace{-.15in}%[[
eval1' = 
fun var : nat =>
EvalPlus' (EvalVar var) (EvalPlus (EvalConst var 8) (EvalVar var))
  (eval1'_subproof var)
     : forall var : nat,
       eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8)
]]
*)

(**
(* The lemma [eval1'_subproof] was generated by [abstract omega].

   Now we are ready to take advantage of logic programming's flexibility by searching for a program (arithmetic expression) that always evaluates to a particular symbolic value. *)

補題 [eval1'_subproof] は [abstract omega] によって生成されました。

これで、常に特定のシンボリック値に評価されるプログラム（算術式）を検索することで、
論理プログラミングの柔軟性を利用する準備が整いました。
 *)

Example synthesize1 : exists e, forall var, eval var e (var + 7).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print synthesize1.
(** %\vspace{-.15in}%[[
synthesize1 = 
ex_intro (fun e : exp => forall var : nat, eval var e (var + 7))
  (Plus Var (Const 7))
  (fun var : nat => EvalPlus (EvalVar var) (EvalConst var 7))
]]
*)

(**
(* Here are two more examples showing off our program synthesis abilities. *)

プログラム合成の能力を見せてくれるもう2つの例があります。
 *)

Example synthesize2 : exists e, forall var, eval var e (2 * var + 8).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

(* begin hide *)
Print synthesize2.       (* suhara: (Plus (Plus Var Var) (Const 8)) *)
(* end hide *)

Example synthesize3 : exists e, forall var, eval var e (3 * var + 42).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

(* begin hide *)
Print synthesize3. (* suhara: (Plus (Plus Var (Plus Var Var)) (Const 42)) *)
(* end hide *)

(**
(* These examples show linear expressions over the variable [var].  Any such expression is equivalent to [k * var + n] for some [k] and [n].  It is probably not so surprising that we can prove that any expression's semantics is equivalent to some such linear expression, but it is tedious to prove such a fact manually.  To finish this section, we will use [eauto] to complete the proof, finding [k] and [n] values automatically.

   We prove a series of lemmas and add them as hints.  We have alternate [eval] constructor lemmas and some facts about arithmetic. *)

これらの例は、変数 [var] の線形な式を示します。
これらのどんな式でも、適当な [k] と [n] なら、[k * var + n] に等しいです。
任意の式の意味がこのような線形の式に等しいということを証明できることは、
多分それほど驚きではありませんが、そのような事実を手動で証明するとは退屈です。
このセクションを終了するにあたり、[eauto] を使って証明を完成させ、
[k]と[n]の値を自動的に見つけてみましょう。

一連の補題を証明してヒントとして追加します。
別の [eval] コンストラクタと補題と算術に関するいくつかの事実があります。
 *)

(* begin thide *)
Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
  crush.
Qed.

Hint Resolve EvalConst'.

Theorem zero_times : forall n m r,
  r = m
  -> r = 0 * n + m.
  crush.
Qed.

Hint Resolve zero_times.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
  crush.
Qed.

Hint Resolve EvalVar'.

Theorem plus_0 : forall n r,
  r = n
  -> r = n + 0.
  crush.
Qed.

Theorem times_1 : forall n, n = 1 * n.
  crush.
Qed.

Hint Resolve plus_0 times_1.

(**
(* We finish with one more arithmetic lemma that is particularly specialized to this theorem.  This fact happens to follow by the axioms of the _semiring_ algebraic structure, so, since the naturals form a semiring, we can use the built-in tactic %\index{tactics!ring}%[ring]. *)

もうひとつ、定理に特に特化した算術的な補題で終わりましょう。
この事実は、半環代数構造の公理に従うので、半環なら自然に(since the naturals form a semiring)、
組み込みタクティク %\index{tactics!ring}%[ring] を使うことができます。
 *)

Require Import Arith Ring.

Theorem combine : forall x k1 k2 n1 n2,
  (k1 * x + n1) + (k2 * x + n2) = (k1 + k2) * x + (n1 + n2).
  intros; ring.
Qed.

Hint Resolve combine.

(**
(* Our choice of hints is cheating, to an extent, by telegraphing the procedure for choosing values of [k] and [n].  Nonetheless, with these lemmas in place, we achieve an automated proof without explicitly orchestrating the lemmas' composition. *)

私たちのヒントの選択は、[k] と [n] の値を選ぶ手続きを電報で伝える(telegraphing)ようで、
ちょっといんちきです(cheating, to an extent)。
それにもかかわらず、
これらの補題が定位置にある場合、
補題の構成を明示的に編成せずに自動証明を成しとけることができます。
 *)

Theorem linear : forall e, exists k, exists n,
  forall var, eval var e (k * var + n).
  induction e; crush; eauto.
Qed.

(* begin hide *)
Print linear.
(* end hide *)
(* end thide *)

(**
(* By printing the proof term, it is possible to see the procedure that is used to choose the constants for each input term. *)

証明項を印刷することで、入力項ごとに定数を選ぶための手続きを見ることができます。
 *)
(*
(** * More on [auto] Hints *)
 *)
(** * さらに [auto] のヒントについて *)

(**
(* Let us stop at this point and take stock of the possibilities for [auto] and [eauto] hints.  Hints are contained within _hint databases_, which we have seen extended in many examples so far.  When no hint database is specified, a default database is used.  Hints in the default database are always used by [auto] or [eauto].  The chance to extend hint databases imperatively is important, because, in Ltac programming, we cannot create "global variables" whose values can be extended seamlessly by different modules in different source files.  We have seen the advantages of hints so far, where [crush] can be defined once and for all, while still automatically applying the hints we add throughout developments.  In fact, [crush] is defined in terms of [auto], which explains how we achieve this extensibility.  Other user-defined tactics can take similar advantage of [auto] and [eauto].

The basic hints for [auto] and [eauto] are: %\index{Vernacular commands!Hint Immediate}%[Hint Immediate lemma], asking to try solving a goal immediately by applying a lemma and discharging any hypotheses with a single proof step each; %\index{Vernacular commands!Hint Resolve}%[Resolve lemma], which does the same but may add new premises that are themselves to be subjects of nested proof search; %\index{Vernacular commands!Hint Constructors}%[Constructors type], which acts like [Resolve] applied to every constructor of an inductive type; and %\index{Vernacular commands!Hint Unfold}%[Unfold ident], which tries unfolding [ident] when it appears at the head of a proof goal.  Each of these [Hint] commands may be used with a suffix, as in [Hint Resolve lemma : my_db], to add the hint only to the specified database, so that it would only be used by, for instance, [auto with my_db].  An additional argument to [auto] specifies the maximum depth of proof trees to search in depth-first order, as in [auto 8] or [auto 8 with my_db].  The default depth is 5.

All of these [Hint] commands can be expressed with a more primitive hint kind, [Extern].  A few more examples of [Hint Extern] should illustrate more of the possibilities. *)

(* suhara: パラグラフ1 *)
ここで止めて、[auto] と [eauto] のヒントの可能性を検討しましょう。
ヒントは、これまでの多くの例で拡張されるのを見た、 ＿ヒントデータベース＿ に格納されます。
ヒントデータベースが指定されていない場合は、デフォルトのデータベースが使用されます。
[auto] または [eauto] によって、デフォルトデータベースのヒントが常に使用されます。
(* suhara: 受身でないほうがよいね *)
命令的に(imperatively)ヒントデータベースを拡張する機会(chance)は重要で、なぜなら、
Ltac プログラミング言語において、
異なるソースファイル内の異なるモジュールによってシームレスにその値を拡張することのできる
「グローバル変数」を作ることができないためです。
[crush] はすべてについて一度定義できたところで、
開発の間にヒントを自動的に適用しながら、これまでのところヒントの利点を見てきました。
実際、[crush] は [auto] の観点から定義されており、
この拡張性をどのように達成するかが説明されています。
他のユーザー定義のタクティクでも、[auto] や [eauto] と同様の利点が得られます。

(* suhara: パラグラフ2 *)
[auto] と [eauto] についての基本的なヒント
%\index{Vernacular commands!Hint Immediate}%[Hint Immediate lemma] は、
補題を適用し、仮説を打ち消して(discharging)、
ただちに目標をひとつの証明のステップで解くように依頼します。

%\index{Vernacular commands!Hint Resolve}%[Resolve lemma] は、
同じことをしますが、ネストされた証明検索の対象となる新しい前提を追加するかもしれません。

%\index{Vernacular commands!Hint Constructors}%[Constructors type] は、
[Resolve] のように動作し、帰納的なすべてのコンストラクタに適用されます。

%\index{Vernacular commands!Hint Unfold}%[Unfold ident] は、
(* suhara: [ident]が *)
証明のゴールの先頭に現れるときに [ident] を展開(unfolding)することを試みます。

これらの [Hint] コマンドのそれぞれに接尾辞を付けて、
指定されたデータベースのみにヒントを追加することができます。たとえば、
[Hint Resolve lemma : my_db] で、ヒントを特定のデータベースに追加したなら、
例えば [auto with my_db] のときだけに使われるでしょう。

[auto] の追加引数は、[auto 8] や [auto 8 with my_db] のように、
深さ優先で検索する証明木の最大の深さを指定します。デフォルトの深さは5です。

(* suhara: パラグラフ3 *)
これらの [Hint] コマンドはすべて、より原始的なヒントの種類 [Extern] で表現できます。
[Hint Extern] の例をいくつか挙げると、より多くの可能性が示されます。
 *)

Theorem bool_neq : true <> false.
(* begin thide *)
  auto.

  (** A call to [crush] would have discharged this goal, but the default hint database for [auto] contains no hint that applies. *)

Abort.

(* begin hide *)
(* begin thide *)
Definition boool := bool.
(* end thide *)
(* end hide *)

(**
(* It is hard to come up with a [bool]-specific hint that is not just a restatement of the theorem we mean to prove.  Luckily, a simpler form suffices, by appealing to the built-in tactic %\index{tactics!congruence}%[congruence], a complete procedure for the theory of equality, uninterpreted functions, and datatype constructors. *)

私たちが証明しようとしている定理の再記述だけではない[bool] 特有のヒントを思いつくのは難しいです。
幸運なことに、
組み込みタクティク %\index{tactics!congruence}%[congruence] と、
等式の定理について完全な手続き、
解釈されない関数、
データ型のコンストラクタを適用することにより、十分簡単になります。
(* suhara: 動詞はどれ? *)
 *)

Hint Extern 1 (_ <> _) => congruence.

Theorem bool_neq : true <> false.
  auto.
Qed.
(* end thide *)

(**
(* A [Hint Extern] may be implemented with the full Ltac language.  This example shows a case where a hint uses a [match]. *)

[Hint Exter] は、全部 Ltac 言語で実装されているかもしれません。
この例は、ヒントがどこで [match] を使うか示しています。
*)

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
(* begin thide *)
    crush.

    (**
(* The [crush] invocation makes no progress beyond what [intros] would have accomplished.  An [auto] invocation will not apply the hypothesis [both] to prove the goal, because the conclusion of [both] does not unify with the conclusion of the goal.  However, we can teach [auto] to handle this kind of goal. *)

[crush] の呼び出しは、[intor] が行うことよりも進捗しない。
なぜなら、[both] の結論はゴールの結論とユニファイしないため、
[auto] の呼び出しは、証明するために前提 [both] を適用しない。
しかしながら、[auto] にこの種類のゴールの扱いを教えることができる。
     *)

    Hint Extern 1 (P ?X) =>
      match goal with
        | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
      end.

    auto.
  Qed.
(* end thide *)

  (**
(* We see that an [Extern] pattern may bind unification variables that we use in the associated tactic.  The function [proj1] is from the standard library, for extracting a proof of [U] from a proof of [U /\ V]. *)

[Extern] パターンは、関連するタクティクで使った、
ユニフィケーション変数を束縛するかもしれないことがわかります。
[proj1] 関数 は、
[U] の証明を [U /\ V] の証明から取り出す(extracting)標準ライブラリから取り入れました。
   *)

End forall_and.

(* begin hide *)
(* begin thide *)
Definition noot := (not, @eq).
(* end thide *)
(* end hide *)

(**
(* After our success on this example, we might get more ambitious and seek to generalize the hint to all possible predicates [P]. *)

この例が成功したあと、より野心的になって、
すべての可能な述語 [P] へのヒントを一般化することを探し求めるかもしれません。

   [[
Hint Extern 1 (?P ?X) =>
  match goal with
    | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
  end.
]]
<<
User error: Bound head variable
>>

(*
   Coq's [auto] hint databases work as tables mapping%\index{head symbol}% _head symbols_ to lists of tactics to try.  Because of this, the constant head of an [Extern] pattern must be determinable statically.  In our first [Extern] hint, the head symbol was [not], since [x <> y] desugars to [not (eq x y)]; and, in the second example, the head symbol was [P].

   Fortunately, a more basic form of [Hint Extern] also applies.  We may simply leave out the pattern to the left of the [=>], incorporating the corresponding logic into the Ltac script. *)

Coqの [auto] のヒントデータベースは、タクティクが試みるためのリストとして、
%\index{head symbol}% _head symbols_ ＿頭部シンボル＿ をマッピングするように働きます。
これはなぜなら、[Extern] パターンの定数の頭部は静的に決定されるべきだからです。
最初の [Extern] ヒントにおいて、[x <> y] の構文糖衣を取り除く(desugars)と [not (eq x y)] なので、
頭部シンボルは [not] でした。次の例では、頭部シンボルは [P] でした。

幸いにも、より基本的な形式である [Hint Extern] にも適用されます。
[=>] の左側にパターンを残して、対応するロジックを Ltac スクリプトに組み込むことができます。
 *)

Hint Extern 1 =>
  match goal with
    | [ H : forall x, ?P x /\ _ |- ?P ?X ] => apply (proj1 (H X))
  end.

(**
(* Be forewarned that a [Hint Extern] of this kind will be applied at _every_ node of a proof tree, so an expensive Ltac script may slow proof search significantly. *)

この種の [Hint Extern] は、証明木の ＿すべての＿ ノードに適用されることに注意してください。
高価な Ltac スクリプトは、証明検索を大幅に遅くする可能性があります。
*)

(*
(** * Rewrite Hints *)
 *)
(** * Rewrite のヒント *)

(**
(* Another dimension of extensibility with hints is rewriting with quantified equalities.  We have used the associated command %\index{Vernacular commands!Hint Rewrite}%[Hint Rewrite] in many examples so far.  The [crush] tactic uses these hints by calling the built-in tactic %\index{tactics!autorewrite}%[autorewrite].  Our rewrite hints have taken the form [Hint Rewrite lemma], which by default adds them to the default hint database [core]; but alternate hint databases may also be specified just as with, e.g., [Hint Resolve].

   The next example shows a direct use of [autorewrite].  Note that, while [Hint Rewrite] uses a default database, [autorewrite] requires that a database be named. *)

ヒントの他の側面は量化された等式を書き換えることです。
関連するコマンド %\index{Vernacular commands!Hint Rewrite}%[Hint Rewrite]
をこれまでの多くの例で使ったことがありました。
[crush] タクティクは、これらのヒントを組み込みタクティク
%\index{tactics!autorewrite}%[autorewrite]
を呼び出すことで使います。
rewrite ヒントは、デフォルトではデォフォルトデータベース [core] に追加される
[Hint Rewrite lemma] のかたちをとっています。
しかし、別のヒントデータベースも [Hint Resolve] のように指定することもできます。

次の例は [autorewrite] を直接使うことを示します。
[Hint Rewrite] はディフォルトのデータベースを使うので、
[autorewrite] はその名前のデータベース(* suhara: [core] の指定 *)が必要です。
 *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
    intros; autorewrite with core; reflexivity.
  Qed.

  (**
(* There are a few ways in which [autorewrite] can lead to trouble when insufficient care is taken in choosing hints.  First, the set of hints may define a nonterminating rewrite system, in which case invocations to [autorewrite] may not terminate.  Second, we may add hints that "lead [autorewrite] down the wrong path."  For instance: *)

ヒントの選択に十分な注意を払わないときに、[autorewrite] が問題を引き起こす幾つかの方法があります。
最初に、ヒントの集合が終わらない書き換えのシステムを定義しているとき、
その場合、[autorewrite] の呼び出しが終わらないことがあります。
次に、誤った道筋(path)に [autorewrite] を導くヒントを加えることがあります。例えば：
   *)

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with core.
      (** [[
============================
 g (g (g x)) = g x
          ]]
          *)

    Abort.

    (**
(* Our new hint was used to rewrite the goal into a form where the old hint could no longer be applied.  This "non-monotonicity" of rewrite hints contrasts with the situation for [auto], where new hints may slow down proof search but can never "break" old proofs.  The key difference is that [auto] either solves a goal or makes no changes to it, while [autorewrite] may change goals without solving them.  The situation for [eauto] is slightly more complicated, as changes to hint databases may change the proof found for a particular goal, and that proof may influence the settings of unification variables that appear elsewhere in the proof state. *)

新しいヒントは、古いヒントがもう適用できないかたち(form)となった、ゴールに適用されます。
この、新しいヒントが証明探索を遅くするかもしれない、
[auto] の状況と対比される rewrite ヒントの "非単調性(non-monotonicity)" は、
古い証明を "壊す(break)" ことは決してありません(* suhara: できていた証明ができなくなること *)。

キーとなる違いは、
[autorewrite] は、ゴールを解くことなしに変形するかもしれないのに対して、
[auto] は、ゴールと解くか、または、それを変えないかのどちらかです。
ヒントデータベースを変更すると特定のゴールについて見つかった証明が変更される可能性があり、
その証明は、証明状態の他の場所に表示される
ユニフィケーション変数の設定に影響を与える可能性があるので、
[eauto] の状況はやや複雑です。
     *)

  Reset garden_path.

  (**
(* The [autorewrite] tactic also works with quantified equalities that include additional premises, but we must be careful to avoid similar incorrect rewritings. *)

[autorewrite] タクティクは、追加の前提を含む量化された等式でも機能しますが、同様の誤った書き換えを避けるように注意する必要があります。
   *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with core.
      (** [[
  ============================
   g (g (g x)) = g x

subgoal 2 is:
 P x
subgoal 3 is:
 P (f x)
subgoal 4 is:
 P (f x)
          ]]
          *)

    Abort.

    (**
(* The inappropriate rule fired the same three times as before, even though we know we will not be able to prove the premises. *)

前提を証明することができないことを知っているにもかかわらず、
不適切なルールは、前と同様に3回実行(fire)しました。
     *)

  Reset garden_path.

  (**
(* Our final, successful, attempt uses an extra argument to [Hint Rewrite] that specifies a tactic to apply to generated premises.  Such a hint is only used when the tactic succeeds for all premises, possibly leaving further subgoals for some premises. *)

最終的な成功は、生成された前提に適用するタクティクを指定する [Hint Rewrite]
に対する追加の引数を使用します。
そのようなヒントは、タクティクがすべての前提で成功した場合にのみ使用され、
前提によってはいくつかの前提のためにさらにサブゴールを残します。
   *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
(* begin thide *)
    Hint Rewrite f_g using assumption.
(* end thide *)

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
(* begin thide *)
      intros; autorewrite with core; reflexivity.
    Qed.
(* end thide *)

    (**
(* We may still use [autorewrite] to apply [f_g] when the generated premise is among our assumptions. *)

生成された前提が仮定の中にあるとき、さらに、
[autorewrite] を [f_g] に適用します。
*)

    Lemma f_f_f_g : forall x, P x -> f (f x) = g x.
(* begin thide *)
      intros; autorewrite with core; reflexivity.
(* end thide *)
    Qed.
  End garden_path.

  (**
(* It can also be useful to apply the [autorewrite with db in *] form, which does rewriting in hypotheses, as well as in the conclusion. *)

結論に対するのと同様に、仮定に対して書き換えをするとき、
[autorewrite with db in *] のかたちを適用するのは便利です。
   *)

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
(* begin thide *)
    intros; autorewrite with core in *; assumption.
(* end thide *)
  Qed.

End autorewrite.

(**
(* Many proofs can be automated in pleasantly modular ways with deft combinations of [auto] and [autorewrite]. *)

多くの証明は、[auto] と [autorewrite] の巧妙な組み合わせで、
快適にモジュール化された方法で自動化することができます。
 *)

  (* suhara *)

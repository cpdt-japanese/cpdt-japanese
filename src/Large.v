(* Copyright (c) 2009-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)


(**
(* %\part{The Big Picture}

   \chapter{Proving in the Large}% *)

   %\part{大局的}

   \chapter{大きな証明をする}% *)


(**
(* It is somewhat unfortunate that the term "theorem proving" looks so much like the word "theory."  Most researchers and practitioners in software assume that mechanized theorem proving is profoundly impractical.  Indeed, until recently, most advances in theorem proving for higher-order logics have been largely theoretical.  However, starting around the beginning of the 21st century, there was a surge in the use of proof assistants in serious verification efforts.  That line of work is still quite new, but I believe it is not too soon to distill some lessons on how to work effectively with large formal proofs.
*)

「定理証明」という言葉が、「理論」という言葉によく似ていることは、やや残念です。
ソフトウェアの研究者や実務家のほとんどは、
機械化された定理証明が根本的に実用的でないと信じています。
確かに、最近まで、高階論理について証明された定理の大部分の進歩は、
主に理論的なものでした。
しかし、21世紀初頭から、重大な検証作業において証明支援系(proof assistants)の使用が急増しました。
その仕事の列線(line)はまだ新しいものですが、
私は大規模な形式的な証明で効果的に仕事をする方法について
いくつかの教訓を掘り起こすのは時期尚早ではないと思います。

(*
   Thus, this chapter gives some tips for structuring and maintaining large Coq developments. *)
したがって、この章では、大規模なCoqの開発を構造化し、保守するためのヒントを示します。
 *)

(*
(** * Ltac Anti-Patterns *)
 *)
(** * Ltac アンチパターン *)

(**
(* In this book, I have been following an unusual style, where proofs are not considered finished until they are %\index{fully automated proofs}%"fully automated," in a certain sense.  Each such theorem is proved by a single tactic.  Since Ltac is a Turing-complete programming language, it is not hard to squeeze arbitrary heuristics into single tactics, using operators like the semicolon to combine steps.  In contrast, most Ltac proofs "in the wild" consist of many steps, performed by individual tactics followed by periods.  Is it really worth drawing a distinction between proof steps terminated by semicolons and steps terminated by periods?
*)

この本では、%\index{fully automated proofs}% 「完全自動化」
になるまで、証明が完了していないというある意味で、珍しいスタイルに従っています。
そのような定理の各々は、単一ののタクティクによって証明されます。
Ltacはチューリング完全なプログラミング言語なので、
セミコロンのような演算子を使ってステップを組み合わせることで、
任意のヒューリスティックスをひとつのタクティクに絞り込むことは難しくありません。
対照的に、「野良(in the wild)」での大部分のLtacによる証明は、
個々のタクティクのピリオドに続いて実行される多くのステップで構成されています。
セミコロンで終了した証明手順とピリオドで終了した手順を区別することは本当に価値があるでしょうか？

(*
   I argue that this is, in fact, a very important distinction, with serious consequences for a majority of important verification domains.  The more uninteresting drudge work a proof domain involves, the more important it is to work to prove theorems with single tactics.  From an automation standpoint, single-tactic proofs can be extremely effective, and automation becomes more and more critical as proofs are populated by more uninteresting detail.  In this section, I will give some examples of the consequences of more common proof styles.
*)

私は、これが実際には非常に重要な違いであり、
重要な検証の領域の大多数に深刻な影響を及ぼしている、と主張しています。
実証的な領域が関与する、より面白くない、退屈な(drudge)とした仕事ほど、
単一のタクティクで定理を証明することがより重要になります。
自動化の観点からは、単一のタクティクによる証明は非常に効果的であり、
証明がより興味深い詳細によって埋められているので、
自動化はますます重要になります。
この節では、より一般的な証明のスタイルの結果のいくつかの例を示します。

(*
   As a running example, consider a basic language of arithmetic expressions, an interpreter for it, and a transformation that scales up every constant in an expression. *)

実行中の例として、
算術式の基本言語、
そのためのインタプリタ、および、
式のなかのすべての定数を拡大するトランスレータを考えてみましょう。
 *)

Inductive exp : Set :=
| Const : nat -> exp
| Plus : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
  end.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

(**
(* We can write a very manual proof that [times] really implements multiplication. *)

実際に乗算([times])を実装するという、非常に手作業の証明を書くことができます。
*)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e.

  trivial.

  simpl.
  rewrite IHe1.
  rewrite IHe2.
  rewrite mult_plus_distr_l.
  trivial.
Qed.

(* begin thide *)
(**
(* We use spaces to separate the two inductive cases, but note that these spaces have no real semantic content; Coq does not enforce that our spacing matches the real case structure of a proof.  The second case mentions automatically generated hypothesis names explicitly.  As a result, innocuous changes to the theorem statement can invalidate the proof. *)

ふたつの帰納的ケースを分離するために空白（空行）を使用しますが、
これらの空行に実際には意味的な内容がないことに注意してください;
Coqは、その空行が証明の実際の場合分けの構造(case structure)と一致するよう強制しません。
2番目のケースでは、自動的に生成された仮説名が明示的に記述されています。
結果として、定理のステートメントに対する無害な変更は、この証明を無効にすることができます。
*)

Reset eval_times.

Theorem eval_times : forall k x,
  eval (times k x) = k * eval x.
  induction x.

  trivial.

  simpl.
(** %\vspace{-.15in}%[[
  rewrite IHe1.
]]

<<
Error: The reference IHe1 was not found in the current environment.
>>

(*
  The inductive hypotheses are named [IHx1] and [IHx2] now, not [IHe1] and [IHe2]. *)

帰納的な仮説は、[IHe1]と[IHe2]ではなく、いまでは [IHx1]と[IHx2]という名前になりました。
 *)
  
Abort.

(**
(* We might decide to use a more explicit invocation of [induction] to give explicit binders for all of the names that we will reference later in the proof. *)

証明の中で後で参照するすべての名前に対して明示的な束縛子(binder)を与えるために、
[induction]のより明示的な呼び出しを使うことにします。
 *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ].

  trivial.

  simpl.
  rewrite IHe1.
  rewrite IHe2.
  rewrite mult_plus_distr_l.
  trivial.
Qed.

(**
(* We pass %\index{tactics!induction}%[induction] an%\index{intro pattern}% _intro pattern_, using a [|] character to separate instructions for the different inductive cases.  Within a case, we write [?] to ask Coq to generate a name automatically, and we write an explicit name to assign that name to the corresponding new variable.  It is apparent that, to use intro patterns to avoid proof brittleness, one needs to keep track of the seemingly unimportant facts of the orders in which variables are introduced.  Thus, the script keeps working if we replace [e] by [x], but it has become more cluttered.  Arguably, neither proof is particularly easy to follow.
*)

%\index{tactics!induction}%[induction] に、
%\index{intro pattern}% ＿intro パターン＿ を渡し、
[|]文字を使用して、帰納法の場合分けを区別します。
ある場合では、[?]を書いてCoqに自動的に名前を生成するように要求し、
その名前を対応する新しい変数に割り当てるための明示的な名前を書きます。
証明のの脆弱さを避けるためにintroパターンを使用するには、
変数が導入された順番についての、一見重要でない事実を把握する必要があることは明らかです。
したがって、[e]を[x]で置き換えるとスクリプトは動作し続けますが、
複雑になっています。 おそらく、どちらの証明も特に追いかけるのは容易ではありません。

(*
   That category of complaint has to do with understanding proofs as static artifacts.  As with programming in general, with serious projects, it tends to be much more important to be able to support evolution of proofs as specifications change.  Unstructured proofs like the above examples can be very hard to update in concert with theorem statements.  For instance, consider how the last proof script plays out when we modify [times] to introduce a bug. *)

その不満のカテゴリーは、静的な人工物としての証明を理解することと関係があります。
一般的なプログラミングと同じように、深刻なプロジェクトでは、
仕様変更に伴い証明の進化をサポートすることが重要になる傾向があります。
上の例のような構造化されていない証明は、定理にあわせて更新するのが非常に難しい場合があります。
たとえば、[times]を修正してバグを導入するときに、
最後の証明のスクリプトがどのように機能するかを考えてみましょう。
 *)

Reset times.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (1 + k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ].

  trivial.

  simpl.
(** %\vspace{-.15in}%[[
  rewrite IHe1.
]]

<<
Error: The reference IHe1 was not found in the current environment.
>>
  *)

Abort.

(**
(* Can you spot what went wrong, without stepping through the script step-by-step?  The problem is that [trivial] never fails.  Originally, [trivial] had been succeeding in proving an equality that follows by reflexivity.  Our change to [times] leads to a case where that equality is no longer true.  The invocation [trivial] happily leaves the false equality in place, and we continue on to the span of tactics intended for the second inductive case.  Unfortunately, those tactics end up being applied to the _first_ case instead.
*)

スクリプトをステップ・バイ・ステップで進めることなく、何が間違っているのか分かりますか？
問題は[trivial]が決して失敗しないということです。
もともと、[trivial]は、反射性に従う等式を証明することに成功していました。
[times]の変更は、その等式がもはや真実でない場合につながります。
[trivial] の呼び出しは、幸いにも、偽の等式を適所に残し(* suhara: ひとつめが終わらないこと *)、
帰納法のふたつめの条件のためのタクティクの範囲を続けます。
残念ながら、それらのタクティクは代わりに ＿ひとつめ＿ の場合に適用されてしまいます。

(*
   The problem with [trivial] could be "solved" by writing, e.g., [solve [ trivial ]] instead, so that an error is signaled early on if something unexpected happens.  However, the root problem is that the syntax of a tactic invocation does not imply how many subgoals it produces.  Much more confusing instances of this problem are possible.  For example, if a lemma [L] is modified to take an extra hypothesis, then uses of [apply L] will generate more subgoals than before.  Old unstructured proof scripts will become hopelessly jumbled, with tactics applied to inappropriate subgoals.  Because of the lack of structure, there is usually relatively little to be gleaned from knowledge of the precise point in a proof script where an error is raised. *)


[trivial] についての問題は、代わりに [solve [ trivial ]] と書くことで「解決」することができ、
予期しないことが起こった場合に早期にエラーが通知されます。
しかし、根本的な問題は、タクティク呼び出しの構文が、
それが生成するサブゴールの数を意味するものではないということです。
この問題のはるかに混乱する例が考えられます。
例えば、補題[L]が余分な仮説をとるように修正された場合、
[apply L]の使用は以前より多くの副目標を生成するようになります。
古い構造化されていない証明スクリプトは、
不適切なサブゴールに適用されたタクティクにより、
絶望的に混乱します。 
構造が不足しているため、
集められた、エラーが発生した証明スクリプト内の正確なポイントの知識は、
比較的少ししかありません。
 *)

Reset times.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

(**
(* Many real developments try to make essentially unstructured proofs look structured by applying careful indentation conventions, idempotent case-marker tactics included solely to serve as documentation, and so on.  All of these strategies suffer from the same kind of failure of abstraction that was just demonstrated.  I like to say that if you find yourself caring about indentation in a proof script, it is a sign that the script is structured poorly.
*)

多くの実際の開発では、本質的に構造化されていない証明を、
慎重な字下げ規則、文書としての役割を果たすための
偶発的(idempotence)なタクティクの大文字小文字の使い分(case-marker)けなどを
適用することによって構造化するようにしています。
これらの戦略のすべては、今見せた抽象化の失敗と同じ種類の障害に苦しんでいます。 
あなたが証明スクリプトでインデントを気にしていると感じたら、
スクリプトがうまく構成されていないという兆候です。

(*
   We can rewrite the current proof with a single tactic. *)

現在の証明を単一のタクティクで書き直すことができます。
*)
  
Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial ].
Qed.

(**
(* We use the form of the semicolon operator that allows a different tactic to be specified for each generated subgoal.  This change improves the robustness of the script: we no longer need to worry about tactics from one case being applied to a different case.  Still, the proof script is not especially readable.  Probably most readers would not find it helpful in explaining why the theorem is true.  The same could be said for scripts using the%\index{bullets}% _bullets_ or curly braces provided by Coq 8.4, which allow code like the above to be stepped through interactively, with periods in place of the semicolons, while representing proof structure in a way that is enforced by Coq.  Interactive replay of scripts becomes easier, but readability is not really helped.
*)

セミコロン演算子の形式を使用して、
生成された各サブゴールに対して異なる戦術を指定することができます。
この変更により、スクリプトの堅牢性が向上します:
もはや、あるケースから別のケースに適用された戦術について心配する必要はありません。
それでも、証明スクリプトは特に読めるものではありません。
たぶん大部分の読者は、なぜ定理が正しいのかを説明するのに役立つとは思わないでしょう。
%\index{bullets}% _bullets_ ＿ブレット＿ や、
Coq 8.4で提供されている中括弧を使用したスクリプトでも言えます。
これは、Coqによって強制される方法で証明構造を表現して、
上記のようなコードをセミコロンの代わりにピリオドをつけて、
対話的に進めることができます。
対話的なスクリプトの再生(replay)が容易になりますが、
読みやすさの助けには本当になりません。

(*
   The situation gets worse in considering extensions to the theorem we want to prove.  Let us add multiplication nodes to our [exp] type and see how the proof fares. *)

証明したい定理の拡張を考えると、状況は悪化します。
乗算のノードを [exp] 型に追加し、
証明がどのように費用を払うか(fares)を見てみましょう。
 *)

Reset exp.

Inductive exp : Set :=
| Const : nat -> exp
| Plus : exp -> exp -> exp
| Mult : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Mult e1 e2 => eval e1 * eval e2
  end.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
    | Mult e1 e2 => Mult (times k e1) e2
  end.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
(** %\vspace{-.25in}%[[
  induction e as [ | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial ].
]]

<<
Error: Expects a disjunctive pattern with 3 branches.
>>
  *)
Abort.

(**
(* Unsurprisingly, the old proof fails, because it explicitly says that there are two inductive cases.  To update the script, we must, at a minimum, remember the order in which the inductive cases are generated, so that we can insert the new case in the appropriate place.  Even then, it will be painful to add the case, because we cannot walk through proof steps interactively when they occur inside an explicit set of cases. *)

驚くことではありませんが、古い証明は失敗します。
なぜなら、それはふたつの帰納の場合分け(case)があることが明示しているからです。
スクリプトを更新するには、帰納の場合分けが生成される順序を少なくとも覚えておく必要があります。
これにより、新しい場合分けを適切な場所に挿入することができます。
それでも、明示的な一連の場合分けの内で発生した場合に、
証明のステップを対話的に進めることができないため、
場合分けを追加するのは苦労します。
 *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial
    | simpl; rewrite IHe1; rewrite mult_assoc; trivial ].
Qed.

(**
(* Now we are in a position to see how much nicer is the style of proof that we have followed in most of this book. *)

今、この本のほとんどで、
私たちが従ってきた証拠のスタイルがどれほど素晴らしいかを知る立場にあります。
 *)

Reset eval_times.

Hint Rewrite mult_plus_distr_l.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e; crush.
Qed.
(* end thide *)

(**
(* This style is motivated by a hard truth: one person's manual proof script is almost always mostly inscrutable to most everyone else.  I claim that step-by-step formal proofs are a poor way of conveying information.  Thus, we might as well cut out the steps and automate as much as possible.
*)

このスタイルは手強い(hard)真実によって動機づけられます:
ひとりの手作業による証明スクリプトは
ほとんどの場合、ほとんどすべての人に納得できません。
私は、ステップ・バイ・ステップの形式的な証明は情報を伝達するための貧弱な方法だと主張します。
したがって、可能な限り、ステップを切り出し、自動化することもできます。

(*
   What about the illustrative value of proofs?  Most informal proofs are read to convey the big ideas of proofs.  How can reading [induction e; crush] convey any big ideas?  My position is that any ideas that standard automation can find are not very big after all, and the _real_ big ideas should be expressed through lemmas that are added as hints.
*)

証明の説明的(illustrative)な価値はどうでしょうか？
ほとんどの非形式的な証明は、証明の大きなアイデアを伝えるために読み込まれます。
どうすれば、[induction e; crush] を読むことが、
なんらかの大きなアイデアを伝えることができるでしょうか？
私の立場は、標準的な自動化が見つけることができるアイデアは結局はあまり大きくなく、
＿本当に＿ 大きなアイデアはヒントとして追加された補題を使って表現されるべきであるということです。

(*
   An example should help illustrate what I mean.  Consider this function, which rewrites an expression using associativity of addition and multiplication. *)

ひとつの例が私が意味するものを説明するのに役立つはずです。
加算と乗算の結合性(associativity)を使って、
式を書き換える関数を考えてみましょう。
 *)

Fixpoint reassoc (e : exp) : exp :=
  match e with
    | Const _ => e
    | Plus e1 e2 =>
      let e1' := reassoc e1 in
      let e2' := reassoc e2 in
        match e2' with
          | Plus e21 e22 => Plus (Plus e1' e21) e22
          | _ => Plus e1' e2'
        end
    | Mult e1 e2 =>
      let e1' := reassoc e1 in
      let e2' := reassoc e2 in
        match e2' with
          | Mult e21 e22 => Mult (Mult e1' e21) e22
          | _ => Mult e1' e2'
        end
  end.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
(* begin thide *)
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | _ => _ end] ] =>
        destruct E; crush
    end.

  (** One subgoal remains:
     [[
  IHe2 : eval e3 * eval e4 = eval e2
  ============================
   eval e1 * eval e3 * eval e4 = eval e1 * eval e2
   ]]
(*
   The [crush] tactic does not know how to finish this goal.  We could finish the proof manually. *)

[crush] タクティクはこのゴールをどのように完成(finish)するか知りません。
ゴールを手動で完成しないといけません。
   *)
  
  rewrite <- IHe2; crush.

  (**
(* However, the proof would be easier to understand and maintain if we separated this insight into a separate lemma. *)

しかし、この洞察を別の補題に分ければ、
証明は理解しやすくなり、
保守することも容易になります。
   *)
  
Abort.

Lemma rewr : forall a b c d, b * c = d -> a * b * c = a * d.
  crush.
Qed.

Hint Resolve rewr.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | _ => _ end] ] =>
        destruct E; crush
    end.
Qed.
(* end thide *)

(**
(* In the limit, a complicated inductive proof might rely on one hint for each inductive case.  The lemma for each hint could restate the associated case.  Compared to manual proof scripts, we arrive at more readable results.  Scripts no longer need to depend on the order in which cases are generated.  The lemmas are easier to digest separately than are fragments of tactic code, since lemma statements include complete proof contexts.  Such contexts can only be extracted from monolithic manual proofs by stepping through scripts interactively.
*)

その制限があると、複雑な帰納法による証明はそれぞれの帰納法の場合分け(case)に対して、
ひとつのヒントに依存する可能性があります。
各ヒントの補題は関連する場合分けを再現(restate)する可能性があります。
手動の証明スクリプトと比較して、わかりやすい結果が得られます。
スクリプトは、場合分けが生成される順序に依存する必要がなくなりました。
補題は完全な証明の文脈を含んでいるので、
補題はタクティクのコードの断片であるよりも、別々にこなす(digest)方が簡単です。
このような文脈は、
スクリプトを対話的に踏むことによってモノリシックな手作業の証明から抽出することができます。

(*
   The more common situation is that a large induction has several easy cases that automation makes short work of.  In the remaining cases, automation performs some standard simplification.  Among these cases, some may require quite involved proofs; such a case may deserve a hint lemma of its own, where the lemma statement may copy the simplified version of the case.  Alternatively, the proof script for the main theorem may be extended with some automation code targeted at the specific case.  Even such targeted scripting is more desirable than manual proving, because it may be read and understood without knowledge of a proof's hierarchical structure, case ordering, or name binding structure.
*)

より一般的な状況は、大きな帰納法は、
自動化が短い作業を行う、いくつかの簡単な場合を有することです。
それ以外の場合、自動化は標準的な単純化を実行します。
これらのケースの中には、かなり複雑な証明が必要なものもあります。
そのような場合は、
その補題のステートメントが場合分けの単純化されたバージョンをコピーしたのならば、
それ自身のヒントの補題に相当するかもしれません。
あるいは、主な定理のための証明スクリプトは、
特定の場合を対象とするいくつかの自動化コードで拡張することができるかもしれません。
そのような対象のスクリプトは、
証明の階層構造や、ケースの順序付けや、名前の束縛の構造(name binding structure)の知識がなくても、
読まれ理解される可能性があるため、
手作業による証明よりも望ましいです。

(*
   A competing alternative to the common style of Coq tactics is the%\index{declarative proof scripts}% _declarative_ style, most frequently associated today with the %\index{Isar}%Isar%~\cite{Isar}% language.  A declarative proof script is very explicit about subgoal structure and introduction of local names, aiming for human readability.  The coding of proof automation is taken to be outside the scope of the proof language, an assumption related to the idea that it is not worth building new automation for each serious theorem.  I have shown in this book many examples of theorem-specific automation, which I believe is crucial for scaling to significant results.  Declarative proof scripts make it easier to read scripts to modify them for theorem statement changes, but the alternate%\index{adaptive proof scripts}% _adaptive_ style from this book allows use of the _same_ scripts for many versions of a theorem.
*)

Coq戦術の一般的なスタイルの代わりに、
%\index{declarative proof scripts}% _declarative_ ＿宣言的＿ スタイルがあります。
これは今日最も頻繁に
%\index{Isar}%Isar%~\cite{Isar}% 言語に関連付けられています。
宣言的な証明スクリプトは、
人間の可読性を目指して、サブゴール構造とローカル名の導入について非常に明示的です。
自動証明のコーディングは、
各々の深刻な定理のための新しい自動化を構築する価値がないという考えに関連した
証明言語の範囲外であるとみなされます。
この本では、定理に特化した自動化の多くの例を示しました。
私は、重要な結果を得るために重要であると信じています。
宣言的な証明スクリプトを使用すると、定理の変更のためにスクリプトを変更しやすくなりますが、
本書の代替 %\index{adaptive proof scripts}% _adaptive_ ＿適応形＿ スタイルでは、
多くのバージョンの定理で _same_ ＿同じ＿ スクリプトを使用できます。

(*
   Perhaps I am a pessimist for thinking that fully formal proofs will inevitably consist of details that are uninteresting to people, but it is my preference to focus on conveying proof-specific details through choice of lemmas.  Additionally, adaptive Ltac scripts contain bits of automation that can be understood in isolation.  For instance, in a big [repeat match] loop, each case can generally be digested separately, which is a big contrast from trying to understand the hierarchical structure of a script in a more common style.  Adaptive scripts rely on variable binding, but generally only over very small scopes, whereas understanding a traditional script requires tracking the identities of local variables potentially across pages of code.
*)

おそらく私は、形式的な証明の全体が
必然的に、人々には面白くない詳細で構成されていると考える悲観論者ですが、
補題の選択を通じて証明固有の詳細を伝えることに焦点を当てることが、私の好みです。
さらに、適応形(adaptive)のLtacスクリプトには、
独立して理解できる一連の自動化が含まれています。
たとえば、大きな[repeat match]ループでは、それぞれのケースを別々に消化することができます。
これは、スクリプトの階層構造をより一般的なスタイルで理解しようとするのとは大きく異なっています。
適応形のスクリプトは可変な束縛に依存(rely)しますが、
一般的に非常に小さなスコープでしか使用だけです。
一方、従来のスクリプトを理解するには、
コードのページ全体で、潜在的なローカル変数の同一性(identities)を追跡する必要があります。

(*
   One might also wonder why it makes sense to prove all theorems automatically (in the sense of adaptive proof scripts) but not construct all programs automatically.  My view there is that _program synthesis_ is a very useful idea that deserves broader application!  In practice, there are difficult obstacles in the way of finding a program automatically from its specification.  A typical specification is not exhaustive in its description of program properties.  For instance, details of performance on particular machine architectures are often omitted.  As a result, a synthesized program may be correct in some sense while suffering from deficiencies in other senses.  Program synthesis research will continue to come up with ways of dealing with this problem, but the situation for theorem proving is fundamentally different.  Following mathematical practice, the only property of a formal proof that we care about is which theorem it proves, and it is trivial to check this property automatically.  In other words, with a simple criterion for what makes a proof acceptable, automatic search is straightforward.  Of course, in practice we also care about understandability of proofs to facilitate long-term maintenance, which is just what motivates the techniques outlined above, and the next section gives some related advice. *)

すべての定理を自動的に（適応形の証明スクリプトの意味で）証明するのはなぜ理にかなっているでしょうが、
すべてのプログラムを自動的に構築するのはそうではありあせん。
私の見解では、_program synthesis_ ＿プログラム合成＿
は広範なアプリケーションに適した非常に便利なアイデアです！
実際には、仕様から自動的にプログラムを見つけるのに困難な障害があります。
典型的な仕様は、プログラム特性の記述において網羅的ではありません。
例えば、特定の機械アーキテクチャ上の性能の詳細は、しばしば省略されます。
結果として、合成されたプログラムは、ある意味では正しいかもしれませんが、
別の観点から欠陥に苦しみます。
プログラム合成の研究はこの問題に対処する方法を生み出し続けますが、
定理証明のための状況は基本的にに異なります。

数学的な実践に続いて、
私たちが気にする形式証明の唯一の性質は、それが証明する定理であり、
この特性を自動的にチェックすることは自明です。
言い換えれば、
証明を受け入れられるものとする、簡単な基準(criterion)では、自動探索は簡単です。
もちろん、実際には、
長期の保守を容易にするための証明の理解可能性(understandability)にも気を配ります。
これは上に概説した技術を動機付けるものであり、
次の節ではいくつかの関連するアドバイスを提供します。
 *)

(*
(** * Debugging and Maintaining Automation *)
 *)
(** * 自動化証明のデバックと保守 *)

(**
(* Fully automated proofs are desirable because they open up possibilities for automatic adaptation to changes of specification.  A well-engineered script within a narrow domain can survive many changes to the formulation of the problem it solves.  Still, as we are working with higher-order logic, most theorems fall within no obvious decidable theories.  It is inevitable that most long-lived automated proofs will need updating.
*)

完全に自動化された証明は、仕様の変更に対して自動的に適応することの可能性を広げているので、
望ましいです。
狭い領域内のうまく設計されたスクリプトは、
それが解決する問題の定式化に多くの変更を生き残ることができます。
それでも、高階論理を使って作業しているので、ほとんどの定理は明らかな決定可能な定理にはなりません。
長く使われている自動化された証明のほとんどは更新が必要であることは避けられません。

(*
   Before we are ready to update our proofs, we need to write them in the first place.  While fully automated scripts are most robust to changes of specification, it is hard to write every new proof directly in that form.  Instead, it is useful to begin a theorem with exploratory proving and then gradually refine it into a suitable automated form.
*)

証明を更新する準備が整う前に、それらの証明を最初に書く必要があります。
完全に自動化されたスクリプトは仕様の変更に対して最も堅牢ですが、
新しいすべての証明をその形式で直接書き込むことは困難です。
代わりに、定理を、探索的な証明(exploratory proving)で開始し、
それを徐々に適切な自動化された形式に修正することは有用です。

(*
   Consider this theorem from Chapter 8, which we begin by proving in a mostly manual way, invoking [crush] after each step to discharge any low-hanging fruit.  Our manual effort involves choosing which expressions to case-analyze on. *)

第8章のこの定理を考えてみましょう。ほとんど手作業で証明することから始まり、
各ステップの後に、さっさと済ますべきこと(low-hanging fruit)を済ますために[crush]を呼びます。
手作業では、場合分け分析の対象となる式を選択する必要があります。

 *)
(* suhara: MoreDep がうまく読めないので「Cpdt.」を付けた。 *)
(* begin hide *)
Require Import Cpdt.MoreDep.
(* end hide *)

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
(* begin thide *)
  induction e; crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (expDenote e1); crush.

  dep_destruct (cfold e); crush.

  dep_destruct (cfold e); crush.
Qed.

(**
(* In this complete proof, it is hard to avoid noticing a pattern.  We rework the proof, abstracting over the patterns we find. *)

この完全な証明では、パターンに気づくのを避けるのは難しいです。
見つけたパターンを抽象化して証明を書き直します。
 *)

Reset cfold_correct.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush.

  (**
(* The expression we want to destruct here turns out to be the discriminee of a [match], and we can easily enough write a tactic that destructs all such expressions. *)

ここで destruct しようとしている式は、
[match]で場合分け(discriminee)しようとしているものであり、
そのような表現をすべて destruct するタクティクを簡単に書くことができます。
   *)
  
  Ltac t :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct E
            end; crush).

  t.

  (**
(* This tactic invocation discharges the whole case.  It does the same on the next two cases, but it gets stuck on the fourth case. *)

このタクティクの使用はすべての場合を済まします。
次の2つの場合では同じですが、第4番めの場合では立ち往生します。
   *)
  
  t.

  t.

  t.

  (**
(* The subgoal's conclusion is:
*)
第4番めのサブゴールの結論は：
     [[
    ============================
   (if expDenote e1 then expDenote (cfold e2) else expDenote (cfold e3)) =
   expDenote (if expDenote e1 then cfold e2 else cfold e3)
   ]]

(*
   We need to expand our [t] tactic to handle this case. *)

この場合を扱うためには、[t] タクティクを拡張する必要があります。
   *)
  
  Ltac t' :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
            end; crush).

  t'.

  (**
  (* Now the goal is discharged, but [t'] has no effect on the next subgoal. *)

今度は、ゴールは済まされていますが、[t ']は次のサブゴールに影響を与えません。
*)

  t'.

  (**
   (* A final revision of [t] finishes the proof. *)

[t]の最終の改訂版は、証明を終了します。
   *)

  Ltac t'' :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
              | [ |- context[match pairOut ?E with Some _ => _
                               | None => _ end] ] =>
                dep_destruct E
            end; crush).

  t''.

  t''.
Qed.

(**
(* We can take the final tactic and move it into the initial part of the proof script, arriving at a nicely automated proof. *)

最終的なタクティクを採用し、それを証明スクリプトの最初の部分に移して、
うまく自動化された証明に到達しました。
 *)

Reset cfold_correct.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush;
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
              | [ |- context[match pairOut ?E with Some _ => _
                               | None => _ end] ] =>
                dep_destruct E
            end; crush).
Qed.
(* end thide *)

(**
(* Even after we put together nice automated proofs, we must deal with specification changes that can invalidate them.  It is not generally possible to step through single-tactic proofs interactively.  There is a command %\index{Vernacular commands!Debug On}%[Debug On] that lets us step through points in tactic execution, but the debugger tends to make counterintuitive choices of which points we would like to stop at, and per-point output is quite verbose, so most Coq users do not find this debugging mode very helpful.  How are we to understand what has broken in a script that used to work?
*)

よい自動化された証明を作った後でさえも、
それらを無効にすることができる仕様の変更に対処する必要があります。
タクティックのひとつずつ(single-tactic)によって、
対話的に証明を進めること(step through)は、一般的に不可能です。
コマンド %\index{Vernacular commands!Debug On}%[Debug On] を使用すると、
タクティクの実行(step through)のポイントを進めることができますが、
デバッカは直感に反して停止したいポイントを選択する傾向があり、
ポイントごとの出力は非常に冗長です。
したがって、Coqのほとんどのユーザーはこれを便利だとは気づきません。
以前使用していたスクリプトで何が壊れているのかを理解するにはどうすればよいでしょうか？

(*
   An example helps demonstrate a useful approach.  Consider what would have happened in our proof of [reassoc_correct] if we had first added an unfortunate rewriting hint. *)

例は、有用なアプローチを示すのに役立ちます。
不適切な書き換え(rewrite)のためのヒントを追加してしまった場合、
[reassoc_correct]の証明で何が起きたかを考えてみましょう。
*)

Reset reassoc_correct.

Theorem confounder : forall e1 e2 e3,
  eval e1 * eval e2 * eval e3 = eval e1 * (eval e2 + 1 - 1) * eval e3.
  crush.
Qed.

Hint Rewrite confounder.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
(* begin thide *)
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | _ => _ end] ] =>
        destruct E; crush
    end.

  (**
  (* One subgoal remains: *)

     ひとつのサブゴールが残ります：

     [[
  ============================
   eval e1 * (eval e3 + 1 - 1) * eval e4 = eval e1 * eval e2
   ]]

(*
   The poorly chosen rewrite rule fired, changing the goal to a form where another hint no longer applies.  Imagine that we are in the middle of a large development with many hints.  How would we diagnose the problem?  First, we might not be sure which case of the inductive proof has gone wrong.  It is useful to separate out our automation procedure and apply it manually. *)

不適切に選択された書き換え規則選択され(fired)、
ゴールを別のヒントが適用されなくなった式(form)に変更しました。
私たちが多くのヒントを持つ大きな開発の真っ只中にいると想像してください。
問題をどのように診断しますか？
最初に、帰納的な証明のどの場合分けが間違っているのかわからないかもしれません。
自動化した手順を分けて手動で適用すると便利です。
   *)

  Restart.

  Ltac t := crush; match goal with
                     | [ |- context[match ?E with Const _ => _ | _ => _ end] ] =>
                       destruct E; crush
                   end.

  induction e.

  (**
(* Since we see the subgoals before any simplification occurs, it is clear that we are looking at the case for constants.  Our [t] makes short work of it. *)

単純化が起こる前にサブゴールを見るので、
（最初のサブゴールは）定数の場合分けを見ていることがわかります。
   *)
      
  t.

  (**
  (* The next subgoal, for addition, is also discharged without trouble. *)

加算(addition)のための、次のサブゴールも問題なく済まされます(discharged)。
*)

  t.

  (**
  (* The final subgoal is for multiplication, and it is here that we get stuck in the proof state summarized above. *)

最後のサブゴールはは乗算(multiplication)のためのものであり、
ここでは、上で説明した状態で、証明は立ち往生します。
*)  

  t.

  (**
  (* What is [t] doing to get us to this point?  The %\index{tactics!info}%[info] command can help us answer this kind of question.  (As of this writing, [info] is no longer functioning in the most recent Coq release, but I hope it returns.) *)

この時点で [t] は何をしていますか？
%\index{tactics!info}%[info] コマンドはこの種の質問に答えるのに役立ちます。
これを書いている時点で、最近のCoqのリリースでは、[info] はもう機能していませんが、
私は復帰することを期待しています。
   *)
  
  Undo.
  info t.

  (* begin hide *)
  (* begin thide *)
  Definition eir := eq_ind_r.
  (* end thide *)
  (* end hide *)

  (** %\vspace{-.15in}%[[
 == simpl in *; intuition; subst; autorewrite with core in *; 
    simpl in *; intuition; subst; autorewrite with core in *; 
    simpl in *; intuition; subst; destruct (reassoc e2).
    simpl in *; intuition.
    
    simpl in *; intuition.
    
    simpl in *; intuition; subst; autorewrite with core in *;
       refine (eq_ind_r
                 (fun n : nat =>
                  n * (eval e3 + 1 - 1) * eval e4 = eval e1 * eval e2) _ IHe1);
       autorewrite with core in *; simpl in *; intuition; 
    subst; autorewrite with core in *; simpl in *; 
    intuition; subst.
 
    ]]

(*
    A detailed trace of [t]'s execution appears.  Since we are using the very general [crush] tactic, many of these steps have no effect and only occur as instances of a more general strategy.  We can copy-and-paste the details to see where things go wrong. *)


[t]の実行の詳細なトレースが表示されます。
非常に一般的な[crush]タクティクを使用しているので、
これらのステップの多くは効果がなく、より一般的なタクティクのインスタンスとしてのみ発生します。
詳細をコピー＆ペーストして、どこが間違っているかを確認することができます。
   *)
  
  Undo.

  (**
  (* We arbitrarily split the script into chunks.  The first few seem not to do any harm. *)

私たちは任意にスクリプトを複数の塊に分割しています。
最初のいくつかは悪影響(harm)を及ぼさないようです。
*)

  simpl in *; intuition; subst; autorewrite with core in *.
  simpl in *; intuition; subst; autorewrite with core in *.
  simpl in *; intuition; subst; destruct (reassoc e2).
  simpl in *; intuition.
  simpl in *; intuition.

  (**
  (* The next step is revealed as the culprit, bringing us to the final unproved subgoal. *)

次のステップは、最終的に証明されないいサブゴールに至らせる原因(culprit)として、明かにされます。
*)

  simpl in *; intuition; subst; autorewrite with core in *.

  (**
  (* We can split the steps further to assign blame. *)

私たちはさらに責任を明確にする(assign blame)ためにステップを分けることができます。
   *)
  
  Undo.

  simpl in *.
  intuition.
  subst.
  autorewrite with core in *.

  (**
  (* It was the final of these four tactics that made the rewrite.  We can find out exactly what happened.  The [info] command presents hierarchical views of proof steps, and we can zoom down to a lower level of detail by applying [info] to one of the steps that appeared in the original trace. *)

これらの4つのタクティクのうち最後のものは、書き換えを行ないました。
何が起こったのかを正確に知ることができます。

[info]コマンドは証明のステップの階層の視点(view)を示し、
元のトレースに表示されたステップのひとつ[info]を適用することで、
より詳細なレベルまでズームダウンすることができます。
   *)
  
  Undo.

  info autorewrite with core in *.
  (** %\vspace{-.15in}%[[
 == refine (eq_ind_r (fun n : nat => n = eval e1 * eval e2) _
              (confounder (reassoc e1) e3 e4)).
      ]]

(*
      The way a rewrite is displayed is somewhat baroque, but we can see that theorem [confounder] is the final culprit.  At this point, we could remove that hint, prove an alternate version of the key lemma [rewr], or come up with some other remedy.  Fixing this kind of problem tends to be relatively easy once the problem is revealed. *)

書き換えの方法はやや凝ったもの(baroque)ですが、
定理[confounder]が最終的な原因(culprit)であることがわかります。
この時点で、そのヒントを取り除き、鍵となる補題[rewr]の代替バージョンを証明するか、
あるいは他のいくつかの救済方法を考え出すことができます。
この種の問題を解決するには、問題が明らかになったならば、比較的容易になる傾向があります。
*)

Abort.
(* end thide *)

(**
(* Sometimes a change to a development has undesirable performance consequences, even if it does not prevent any old proof scripts from completing.  If the performance consequences are severe enough, the proof scripts can be considered broken for practical purposes.
*)

時に、古い証明スクリプトが完成しないようにしても、
開発への変更は望ましくないパフォーマンスへの影響(consequences)をもたらすことがあります。
パフォーマンスへの影響が十分に厳しい場合は、
実際的な意味で、証明スクリプトが壊れたとみなすことができます。

(*
   Here is one example of a performance surprise. *)

パフォーマンスについての驚きの一例を以下に示します。
 *)

Section slow.
  Hint Resolve trans_eq.

  (**
  (* The central element of the problem is the addition of transitivity as a hint.  With transitivity available, it is easy for proof search to wind up exploring exponential search spaces.  We also add a few other arbitrary variables and hypotheses, designed to lead to trouble later. *)
  
問題の中心的な要素は、推移性(transitivity)をヒントとして追加することです。
推移性を利用すると、証明検索で指数関数的な探索空間を探索することが容易になり、
後でトラブルを起こします。
   *)
  
  Variable A : Set.
  Variables P Q R S : A -> A -> Prop.
  Variable f : A -> A.

  Hypothesis H1 : forall x y, P x y -> Q x y -> R x y -> f x = f y.
  Hypothesis H2 : forall x y, S x y -> R x y.

  (**
  (* We prove a simple lemma very quickly, using the %\index{Vernacular commands!Time}%[Time] command to measure exactly how quickly. *)

単純な補題をとても早く証明し、 %\index{Vernacular commands!Time}%[Time] コマンドを使っていかに早く
証明できるか計測できます。
   *)
  
  Lemma slow : forall x y, P x y -> Q x y -> S x y -> f x = f y.
    Time eauto 6.
(** <<
Finished transaction in 0. secs (0.068004u,0.s)
>>
*)

  Qed.

  (**
  (* Now we add a different hypothesis, which is innocent enough; in fact, it is even provable as a theorem. *)

ここで、別の仮説を追加します。これは無益なもの(innocent)です：
実際には、定理としても証明可能です。
   *)
  
  Hypothesis H3 : forall x y, x = y -> f x = f y.

  Lemma slow' : forall x y, P x y -> Q x y -> S x y -> f x = f y.
    Time eauto 6.
    (** <<
Finished transaction in 2. secs (1.264079u,0.s)
      >>
(*
      %\vspace{-.15in}%Why has the search time gone up so much?  The [info] command is not much help, since it only shows the result of search, not all of the paths that turned out to be worthless. *)

%\vspace{-.15in}% 検索時間があまりにも長くなったのはなぜでしょうか？
[info]コマンドはあまり役に立ちません。
検索の結果だけを表示するだけで、有用でないと判明したすべてのパスが表示されるわけではありません。
     *)
    
(* begin thide *)
    Restart.
    info eauto 6.
    (** %\vspace{-.15in}%[[
 == intro x; intro y; intro H; intro H0; intro H4;
       simple eapply trans_eq.
    simple apply eq_refl.
    
    simple eapply trans_eq.
    simple apply eq_refl.
    
    simple eapply trans_eq.
    simple apply eq_refl.
    
    simple apply H1.
    eexact H.
    
    eexact H0.
    
    simple apply H2; eexact H4.
    ]]

(*
    This output does not tell us why proof search takes so long, but it does provide a clue that would be useful if we had forgotten that we added transitivity as a hint.  The [eauto] tactic is applying depth-first search, and the proof script where the real action is ends up buried inside a chain of pointless invocations of transitivity, where each invocation uses reflexivity to discharge one subgoal.


  Each increment to the depth argument to [eauto] adds another silly use of transitivity.  This wasted proof effort only adds linear time overhead, as long as proof search never makes false steps.  No false steps were made before we added the new hypothesis, but somehow the addition made possible a new faulty path.  To understand which paths we enabled, we can use the %\index{tactics!debug}%[debug] command. *)

この出力は、証明検索に時間がかかりすぎる理由を教えてくれませんが、
推論をヒントとして追加したことを忘れてしまった場合に役立つヒントを提供します。
[eauto]タクティクは深さ優先探索を適用しており、
実際のアクションが終わっている証明スクリプトは、
それぞれの呼び出しがひとつの副目標を済ます(discharege)ために反射性を使用する
無意味な呼び出しの連鎖の中に埋もれてしまいます。

[eauto]の深さを指定する引数への各増分は、推論の別の愚かな使用を追加します。
この浪費された証明の努力は、証明検索が誤ったステップを決してしない限り、
線形時間オーバーヘッドを追加するだけです。
新しい仮説を追加する前に、間違った手順はありませんでしたが、
何らかの形で追加すると、新しい欠陥のあるパスが可能になりました。
有効にしたパスを理解するために、%\index{tactics!debug}%[debug] コマンドを使用できます。
     *)
    
    Restart.
    debug eauto 6.

    (* begin hide *)
    (* begin thide *)
    Definition deeeebug := (@eq_refl, @sym_eq).
    (* end thide *)
    (* end hide *)

    (**
    (* The output is a large proof tree.  The beginning of the tree is enough to reveal what is happening:
*)

出力は大きな証明木です。
木の始まりは何が起こっているかを明らかにするには十分です：

       [[
1 depth=6 
1.1 depth=6 intro
1.1.1 depth=6 intro
1.1.1.1 depth=6 intro
1.1.1.1.1 depth=6 intro
1.1.1.1.1.1 depth=6 intro
1.1.1.1.1.1.1 depth=5 apply H3
1.1.1.1.1.1.1.1 depth=4 eapply trans_eq
1.1.1.1.1.1.1.1.1 depth=4 apply eq_refl
1.1.1.1.1.1.1.1.1.1 depth=3 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1 depth=3 apply eq_refl
1.1.1.1.1.1.1.1.1.1.1.1 depth=2 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1 depth=2 apply eq_refl
1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=1 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=1 apply eq_refl
1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 depth=1 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.3 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2 depth=2 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.2.1 depth=1 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.1 depth=1 apply eq_refl
1.1.1.1.1.1.1.1.1.1.1.1.2.1.1.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.2 depth=1 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.2.1.2.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.3 depth=0 eapply trans_eq
       ]]

(*
       The first choice [eauto] makes is to apply [H3], since [H3] has the fewest hypotheses of all of the hypotheses and hints that match.  However, it turns out that the single hypothesis generated is unprovable.  That does not stop [eauto] from trying to prove it with an exponentially sized tree of applications of transitivity, reflexivity, and symmetry of equality.  It is the children of the initial [apply H3] that account for all of the noticeable time in proof execution.  In a more realistic development, we might use this output of [debug] to realize that adding transitivity as a hint was a bad idea. *)

最初の選択肢[eauto]は[H3]を適用することです。
なぜなら、[H3]は一致するすべての仮説とヒントの仮説が少ないためです。
しかしながら、生成された単一の仮説は証明できないことがわかりました。
それは、推移的、反射性、平等の対称性の指数関数的なツリーでそれを証明しようとすることを止めるものではありません。
証明実行の際の顕著な時間のすべてを占めるのは、最初の[apply H3]の子供たちです。
より現実的な開発では、この出力を[debug]として使用して、
推移性をヒントとして追加することは悪い考えであることに気付くかもしれません。
     *)
    
  Qed.
(* end thide *)
End slow.

(**
(* As aggravating as the above situation may be, there is greater aggravation to be had from importing library modules with commands like %\index{Vernacular commands!Require Import}%[Require Import].  Such a command imports not just the Gallina terms from a module, but also all the hints for [auto], [eauto], and [autorewrite].  Some very recent versions of Coq include mechanisms for removing hints from databases, but the proper solution is to be very conservative in exporting hints from modules.  Consider putting hints in named databases, so that they may be used only when called upon explicitly, as demonstrated in Chapter 13.
*)

上記の状況が悪化すると、
%\index{Vernacular commands!Require Import}%[Require Import]
のようなコマンドを使ってライブラリモジュールをインポートすると、
非常に最近のバージョンのCoqには、
データベースからヒントを取り除くためのメカニズムが含まれていますが、
適切な解決策は、ヒントをエクスポートする際には非常に慎重でなければなりません。
ヒントを明示的に呼び出されたときにのみ使用できるように、
名前付きデータベースにヒントを入れることを検討してください（第13章を参照）。

(*
It is also easy to end up with a proof script that uses too much memory.  As tactics run, they avoid generating proof terms, since serious proof search will consider many possible avenues, and we do not want to build proof terms for subproofs that end up unused.  Instead, tactic execution maintains%\index{thunks}% _thunks_ (suspended computations, represented with closures), such that a tactic's proof-producing thunk is only executed when we run %\index{Vernacular commands!Qed}%[Qed].  These thunks can use up large amounts of space, such that a proof script exhausts available memory, even when we know that we could have used much less memory by forcing some thunks earlier.
*)

あまりにも多くのメモリを使用する証明スクリプトで終わるのも簡単です。
タクティクが実行されるにつれて、
重大な証拠検索では多くの可能な手段が考慮されるため、証明項の生成は避けられます。
また、使用されない副証明(subproof)に関する証明項語を作成したくありません。
代わりに、タクティックの実行は、%\index{Vernacular commands!Qed}%[Qed]
を実行したときにのみ実行されるように、%\index{thunks}% _thunks_ 
（中断された計算、クロージャで表される）を維持します。 
これらのサンクは大量のスペースを消費することがあります。thunks を早期に強制することで
メモリを大幅に節約できたとしても、証明スクリプトが使用可能なメモリを使い果たしてしまいます。

(*
   The %\index{tactics!abstract}%[abstract] tactical helps us force thunks by proving some subgoals as their own lemmas.  For instance, a proof [induction x; crush] can in many cases be made to use significantly less peak memory by changing it to [induction x; abstract crush].  The main limitation of [abstract] is that it can only be applied to subgoals that are proved completely, with no undetermined unification variables in their initial states.  Still, many large automated proofs can realize vast memory savings via [abstract]. *)

%\index{tactics!abstract}%[abstract] タクティカルは、
いくつかのサブゴールを独自の補題として証明することによって、
thunks を強制するのに役立ちます。

例えば、証明 [induction x; crush] は、多くの場合で、
[induction x; abstract crush] に変更することによって
大幅に少ないメモリを使用することができます。
[abstract] の主な制限は、初期状態では未定の統一変数がなく、
完全に証明されたサブゴールにしか適用できないということです。
それでも、多くの大規模な自動証明は、
[abstract]を介して膨大なメモリ節約を実現することができます。
 *)

(*
(** * Modules *)
 *)
(** * モージュール *)

(**
(*
 Last chapter's examples of proof by reflection demonstrate opportunities for implementing abstract proof strategies with stronger formal guarantees than can be had with Ltac scripting.  Coq's _module system_ provides another tool for more rigorous development of generic theorems.  This feature is inspired by the module systems found in Standard ML%~\cite{modules}% and OCaml, and the discussion that follows assumes familiarity with the basics of one of those systems.
*)

前章のリフレクションによる証明の例は、Ltacスクリプトよりもより強力な形式的保証を伴う抽象的な証明戦略を実装する機会を示しています。
Coqの ＿モジュール・システム＿ は、一般的な定理(generic theorems)の
厳格な開発のための別なツールを提供します。
この機能は、Standard ML %~\cite{modules}% と OCaml にあるモジュールz・システムから
インスピレーションを受けています。以下の議論では、
これらのシステムのひとつについて熟知していることを前提とします。

(*
   ML modules facilitate the grouping of %\index{abstract type}%abstract types with operations over those types.  Moreover, there is support for%\index{functor}% _functors_, which are functions from modules to modules.  A canonical example of a functor is one that builds a data structure implementation from a module that describes a domain of keys and its associated comparison operations.
*)

MLのモジュールは、%\index{abstract type}%抽象型 (abstract types) と
それらの型に対する操作のグループ化を容易にします。
また、モジュール間の関数である %\index{functor}% ＿関手＿ (_functors_) もサポートされています。
関手の標準的な例は、キーとなるのドメインと、
関連する比較演算子(* suhara: 結合性を満たす、ではなないと思う*)を記述するモジュールから
データ構造の実装を構築するものです。

(*
   When we add modules to a base language with dependent types, it becomes possible to use modules and functors to formalize kinds of reasoning that are common in algebra.  For instance, the following module signature captures the essence of the algebraic structure known as a group.  A group consists of a carrier set [G], an associative binary operation [f], a left identity element [id] for [f], and an operation [i] that is a left inverse for [f].%\index{Vernacular commands!Module Type}% *)

依存型を持つ基本言語にモジュールを追加すると、
モジュールとファンクタを使用して、代数で一般的な推論の種類を正式化することが可能になります。
例えば、以下のモジュールのシグネチャは、群(group)と呼ばれる代数構造の本質を捉えています。
群は、台集合(carrier set) [G]、
結合性を満たす二項演算[f]、
[f]の左単位元[id]、
[f]の左逆元ある演算[i]で構成されます。
%\index{Vernacular commands!Module Type}%
 *)

Module Type GROUP.
  Parameter G : Set.
  Parameter f : G -> G -> G.
  Parameter id : G.
  Parameter i : G -> G.

  Axiom assoc : forall a b c, f (f a b) c = f a (f b c).
  Axiom ident : forall a, f id a = a.
  Axiom inverse : forall a, f (i a) a = id.
End GROUP.

(**
(* Many useful theorems hold of arbitrary groups.  We capture some such theorem statements in another module signature.%\index{Vernacular commands!Declare Module}% *)

多くの便利な定理は任意の群を保持していますが、
他のモジュールのシグネチャでそのような定理文をいくつか取ります。
%\index{Vernacular commands!Declare Module}%
 *)

Module Type GROUP_THEOREMS.
  Declare Module M : GROUP.

  Axiom ident' : forall a, M.f a M.id = a.

  Axiom inverse' : forall a, M.f a (M.i a) = M.id.

  Axiom unique_ident : forall id', (forall a, M.f id' a = a) -> id' = M.id.
End GROUP_THEOREMS.

(**
(* We implement generic proofs of these theorems with a functor, whose input is an arbitrary group [M]. %\index{Vernacular commands!Module}% *)

これらの定理の一般的な証明は、入力が任意の群[M]であるファンクタで実装されます。
%\index{Vernacular commands!Module}%
 *)

Module GroupProofs (M : GROUP) : GROUP_THEOREMS with Module M := M.

  (**
  (* As in ML, Coq provides multiple options for ascribing signatures to modules.  Here we use just the colon operator, which implements%\index{opaque ascription}% _opaque ascription_, hiding all details of the module not exposed by the signature.  Another option is%\index{transparent ascription}% _transparent ascription_ via the [<:] operator, which checks for signature compatibility without hiding implementation details.  Here we stick with opaque ascription but employ the [with] operation to add more detail to a signature, exposing just those implementation details that we need to.  For instance, here we expose the underlying group representation set and operator definitions.  Without such a refinement, we would get an output module proving theorems about some unknown group, which is not very useful.  Also note that opaque ascription can in Coq have some undesirable consequences without analogues in ML, since not just the types but also the _definitions_ of identifiers have significance in type checking and theorem proving. *)

MLのように、Coqはシグネチャをモジュールに帰属させるための複数のオプションを提供します。
ここでは、%\index{opaque ascription}% _opaque ascription_
(* suhara: wikipedia.jp の SMLの項でも英語のまま *)
を実装するコロン演算子を使用して、
シグネチャによって公開されていないモジュールのすべての詳細を隠します。
もうひとつのオプションは、実装の詳細を隠すことなく、
シグネチャの互換性をチェックする [<:] 演算子による
%\index{transparent ascription}% _transparent ascription_
です。
ここでは、[op]を使用します。このような洗練がなければ、
あまり有用でないいくつかの未知のグループについての定理を証明する出力モジュールを得ることになります。
Coqの不透明な帰納法は、型のチェックだけでなく、
識別子の_definitions_もタイプチェックと定理証明の意味を持つため、
MLの中で関連性(analogues)がないと望ましくない結果をもたらす可能性があることにも注意してください。
   *)

  Module M := M.
  (**
  (* To ensure that the module we are building meets the [GROUP_THEOREMS] signature, we add an extra local name for [M], the functor argument. *)

構築しているモジュールが[GROUP_THEOREMS]署名を満たしていることを確認するために、
関手の引数の[M]に追加のローカル名を追加します。
   *)
  
  Import M.
  (*
  (** It would be inconvenient to repeat the prefix [M.] everywhere in our theorem statements and proofs, so we bring all the identifiers of [M] into the local scope unqualified.
 *)

定理宣言と証明ではどこにでも接頭辞[M]を繰り返すのは不便かもしれません。
したがって、[M]のすべての識別子を無限定のローカルスコープに持ち込みます。

(*
     Now we are ready to prove the three theorems.  The proofs are completely manual, which may seem ironic given the content of the previous sections!  This illustrates another lesson, which is that short proof scripts that change infrequently may be worth leaving unautomated.  It would take some effort to build suitable generic automation for these theorems about groups, so I stick with manual proof scripts to avoid distracting us from the main message of the section.  We take the proofs from the Wikipedia page on elementary group theory. *)

今我々は3つの定理を証明する準備ができています。
証明は完全にマニュアルであり、
これは前のセクションの内容を考えると皮肉に思えるかもしれません！
これは別のレッスンを示しています。
頻繁に変更される短い証明スクリプトは、自動化されないままにする価値があります。
群についてのこれらの定理に適した一般的な自動化を構築するには多少の努力が必要なので、
セクションの主なメッセージから私たちを邪魔しないように手作業による証明スクリプトを貼り付けます。
私たちは、Wikipediaの「群論入門」のページから証明を取っています。 *）
   *)
  
  Theorem inverse' : forall a, f a (i a) = id.
    intro.
    rewrite <- (ident (f a (i a))).
    rewrite <- (inverse (f a (i a))) at 1.
    rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc (i a) a (i a)).
    rewrite inverse.
    rewrite ident.
    apply inverse.
  Qed.

  Theorem ident' : forall a, f a id = a.
    intro.
    rewrite <- (inverse a).
    rewrite <- assoc.
    rewrite inverse'.
    apply ident.
  Qed.

  Theorem unique_ident : forall id', (forall a, M.f id' a = a) -> id' = M.id.
    intros.
    rewrite <- (H id).
    symmetry.
    apply ident'.
  Qed.
End GroupProofs.

(**
(* We can show that the integers with [+] form a group. *)

整数は [+] について群をなすことをしめします。
*)

Require Import ZArith.
Open Scope Z_scope.

Module Int.
  Definition G := Z.
  Definition f x y := x + y.
  Definition id := 0.
  Definition i x := -x.

  Theorem assoc : forall a b c, f (f a b) c = f a (f b c).
    unfold f; crush.
  Qed.
  Theorem ident : forall a, f id a = a.
    unfold f, id; crush.
  Qed.
  Theorem inverse : forall a, f (i a) a = id.
    unfold f, i, id; crush.
  Qed.
End Int.

(**
(* Next, we can produce integer-specific versions of the generic group theorems. *)

次に、一般的な群の定理の整数固有のバージョンを生成することができます。
*)

Module IntProofs := GroupProofs(Int).

Check IntProofs.unique_ident.
(** %\vspace{-.15in}% [[
  IntProofs.unique_ident
     : forall e' : Int.G, (forall a : Int.G, Int.f e' a = a) -> e' = Int.e
     ]]

(*
Projections like [Int.G] are known to be definitionally equal to the concrete values we have assigned to them, so the above theorem yields as a trivial corollary the following more natural restatement: *)

[Int.G]のような射影(projection)は、
我々がそれらに割り当てた具体的な値と定義的に等しいことが知られているので、
上記の定理は、以下のより自然な再記述を簡単な結果としてもたらします：
 *)

Theorem unique_ident : forall id', (forall a, id' + a = a) -> id' = 0.
(* begin thide *)
  exact IntProofs.unique_ident.
Qed.
(* end thide *)

(**
(* As in ML, the module system provides an effective way to structure large developments.  Unlike in ML, Coq modules add no expressiveness; we can implement any module as an inhabitant of a dependent record type.  It is the second-class nature of modules that makes them easier to use than dependent records in many cases.  Because modules may only be used in quite restricted ways, it is easier to support convenient module coding through special commands and editing modes, as the above example demonstrates.  An isomorphic implementation with records would have suffered from lack of such conveniences as module subtyping and importation of the fields of a module.  On the other hand, all module values must be determined statically, so modules may not be computed, e.g., within the definitions of normal functions, based on particular function parameters. *)

MLのように、モジュール・システムは、大規模な開発を構築する効果的な方法を提供します。
MLとは異なり、Coqモジュールは表現力を追加せず、
依存型のレコードのフィールド(inhabitant)として任意のモジュールを実装することができます。
多くの場合、依存レコードよりも使いやすくするセカンド・クラス(second-class nature)のモジュールです。
モジュールは非常に限定された方法でしか使用できないので、上記の例が示すように、
特別なコマンドと編集モードで便利なモジュールコーディングをサポートする方が簡単です。
レコードの同形(isomorphic)の実装は、
モジュールのサブタイプ化やモジュールのフィールドのインポートなどの利便性の欠如に悩まされていました。
一方、すべてのモジュール値は静的に決定されなければならないので、モジュールは、例えば、特定の関数パラメータに基づいて、通常の関数の定義内で計算されないことがあります。
 *)

(*
(** * Build Processes *)
 *)
(** * ビルド・プロセス *)

(* begin hide *)
(* begin thide *)
Module Lib.
  Module A.
  End A.
  Module B.
  End B.
  Module C.
  End C.
End Lib.
Module Client.
  Module D.
  End D.
  Module E.
  End E.
End Client.
(* end thide *)
(* end hide *)

(**
(* As in software development, large Coq projects are much more manageable when split across multiple files and when decomposed into libraries.  Coq and Proof General provide very good support for these activities.
*)

ソフトウェア開発のように、大規模なCoqプロジェクトは、
複数のファイルに分割してライブラリに分解すると、はるかに管理しやすくなります。
CoqとProof Generalはこれらの活動を非常にうまくサポートしています。

(*
   Consider a library that we will name [Lib], housed in directory <<LIB>> and split between files <<A.v>>, <<B.v>>, and <<C.v>>.  A simple %\index{Makefile}%Makefile will compile the library, relying on the standard Coq tool %\index{coq\_makefile}%<<coq_makefile>> to do the hard work.
*)

ディレクトリ <<LIB>> に格納され、ファイル <<A.v>>、<<B.v>>、および <<C.v>> の間で
分割される[Lib]という名前のライブラリを考えてみましょう。
シンプルな %\index{Makefile}%Makefile は、標準的なCoqツール
%\index{coq\_makefile}%<<coq_makefile>> を使ってライブラリをコンパイルします。

<<
MODULES := A B C
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
        coq_makefile -R . Lib $(VS) -o Makefile.coq

clean:: Makefile.coq
        $(MAKE) -f Makefile.coq clean
        rm -f Makefile.coq
>>

(*
   The Makefile begins by defining a variable <<VS>> holding the list of filenames to be included in the project.  The primary target is <<coq>>, which depends on the construction of an auxiliary Makefile called <<Makefile.coq>>.  Another rule explains how to build that file.  We call <<coq_makefile>>, using the <<-R>> flag to specify that files in the current directory should be considered to belong to the library [Lib].  This Makefile will build a compiled version of each module, such that <<X.v>> is compiled into <<X.vo>>.
*)

Makefileは、
プロジェクトに含めるファイル名のリストを保持する変数 <<VS>> を定義することから始まります。
主なターゲットは<<coq>>です。
これは<<Makefile.coq>>と呼ばれる補助的なMakefileの構成に依存します。
別のルールは、そのファイルを構築する方法を説明します。
カレント・ディレクトリのファイルをライブラリ[Lib]に属するとみなすために、
<<-R>>フラグを使用して、<<coq_makefile>> を呼び出します。
このMakefileは、（たとえば）<<X.v>>が<<X.vo>>にコンパイルされるように、
各モジュールのコンパイルされたバージョンを構築します。

(*
   Now code in <<B.v>> may refer to definitions in <<A.v>> after running
*)
ここで、<<B.v>>のコードは、実行後に<<A.v>>の定義を参照することがあります

   [[
Require Import Lib.A.
   ]]
(*
   %\vspace{-.15in}%Library [Lib] is presented as a module, containing a submodule [A], which contains the definitions from <<A.v>>.  These are genuine modules in the sense of Coq's module system, and they may be passed to functors and so on.
*)

%\vspace{-.15in}%ライブラリ [Lib] はモジュールとして表示され、
<<A.v>>から定義されるサブモジュール[A]を含みます。
これらはCoqのモジュール・システムの意味での本物のモジュールであり、
ファンクタ(functor)などに渡すことができます。

(*
   The command [Require Import] is a convenient combination of two more primitive commands.  The %\index{Vernacular commands!Require}%[Require] command finds the <<.vo>> file containing the named module, ensuring that the module is loaded into memory.  The %\index{Vernacular commands!Import}%[Import] command loads all top-level definitions of the named module into the current namespace, and it may be used with local modules that do not have corresponding <<.vo>> files.  Another command, %\index{Vernacular commands!Load}%[Load], is for inserting the contents of a named file verbatim.  It is generally better to use the module-based commands, since they avoid rerunning proof scripts, and they facilitate reorganization of directory structure without the need to change code.
*)

[Require Import]コマンドは、さらにふたつの基本的(primitive)なコマンドの便利な組み合わせです。
%\index{Vernacular commands!Require}%[Require] コマンドは、
名前付きモジュールを含む<<.vo>>ファイルを見つけ、
モジュールがメモリにロードされていることを確認します。
%\index{Vernacular commands!Import}%[Import] コマンドは、
名前付きモジュールのすべてのトップレベルの定義を現在の名前空間にロードし、
対応する<<.vo>>ファイルを持たないローカルなモジュールで使用できます。
別のコマンド、%\index{Vernacular commands!Load}%[Load] は、
名前付きファイルの内容をそのまま挿入するためのものです。
証明スクリプトを再実行するのを避け、
コードを変更することなくディレクトリ構造の再編成を容易にするので、
モジュールベースのコマンド(suhara: Load ではなく、Require と Import)
を使用する方が一般的に適しています。

(*
   Now we would like to use our library from a different development, called [Client] and found in directory <<CLIENT>>, which has its own Makefile.
*)

今度は、<<CLIENT>>ディレクトリにある、[Client]と呼ばれる独自のMakefileを持つ、
別の開発用ライブラリを使用したいと考えます。

<<
MODULES := D E
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
        coq_makefile -R LIB Lib -R . Client $(VS) -o Makefile.coq

clean:: Makefile.coq
        $(MAKE) -f Makefile.coq clean
        rm -f Makefile.coq
>>

(*
   We change the <<coq_makefile>> call to indicate where the library [Lib] is found.  Now <<D.v>> and <<E.v>> can refer to definitions from [Lib] module [A] after running
*)
<<coq_makefile>>の呼び出しを変更して、ライブラリ[Lib]がどこにあるかを示します。
現在、<<D.v>>と<<E.v>>は、実行後の[Lib]モジュール[A]の定義を参照できます。

   [[
Require Import Lib.A.
   ]]
(*
   %\vspace{-.15in}\noindent{}%and <<E.v>> can refer to definitions from <<D.v>> by running
*)
   %\vspace{-.15in}\noindent{}% そして、<<E.v>>は、実行によって<<D.v>>の定義を参照できます。

   [[
Require Import Client.D.
   ]]
(*
   %\vspace{-.15in}%It can be useful to split a library into several files, but it is also inconvenient for client code to import library modules individually.  We can get the best of both worlds by, for example, adding an extra source file <<Lib.v>> to [Lib]'s directory and Makefile, where that file contains just this line:%\index{Vernacular commands!Require Export}%
*)

   %\vspace{-.15in}% ライブラリを複数のファイルに分割すると便利ですが、
クライアントのコードが個別にライブラリのモジュールをインポートすることも不便です。
たとえば、余分なソースファイル "Lib.v"を[Lib]のディレクトリとMakefileに追加することで、
両方にとっての最良を得ることができます。
このファイルには、次の行だけが含まれています：
%\index{Vernacular commands!Require Export}%

   [[
Require Export Lib.A Lib.B Lib.C.
   ]]
(*
   %\vspace{-.15in}%Now client code can import all definitions from all of [Lib]'s modules simply by running
*)
   %\vspace{-.15in}%ここで、クライアントのコードはすべての[Lib]のモジュールから、
すべての定義を単純に実行することでインポートできます。
   [[
Require Import Lib.
   ]]
(*
   %\vspace{-.15in}%The two Makefiles above share a lot of code, so, in practice, it is useful to define a common Makefile that is included by multiple library-specific Makefiles.
*)
   %\vspace{-.15in}%上記のふたつのMakefileは多くのコードを共有しているので、
実際には、複数のライブラリ固有のMakefileに含まれる（定義を）
共通のMakefileに定義すると便利です。

   %\medskip%

(*
   The remaining ingredient is the proper way of editing library code files in Proof General.  Recall this snippet of <<.emacs>> code from Chapter 2, which tells Proof General where to find the library associated with this book.
*)

残りの成分は、Proof Generalでライブラリのコードのファイルを編集する適切な方法です。
第2章の<<.emacs >>コードのこのスニペットを思い出してください。
このスニペットは、Proof Generalにこの本に関連するライブラリを見つける場所を教えてくれます。

<<
(custom-set-variables
  ...
  '(coq-prog-args '("-R" "/path/to/cpdt/src" "Cpdt"))
  ...
)
>>

(*
   To do interactive editing of our current example, we just need to change the flags to point to the right places.
*)
現在の例を対話的に編集するには、適切な場所を指すようにフラグを変更するだけです。

<<
(custom-set-variables
  ...
; '(coq-prog-args '("-R" "/path/to/cpdt/src" "Cpdt"))
  '(coq-prog-args '("-R" "LIB" "Lib" "-R" "CLIENT" "Client"))
  ...
)
>>

(*
   When working on multiple projects, it is useful to leave multiple versions of this setting in your <<.emacs>> file, commenting out all but one of them at any moment in time.  To switch between projects, change the commenting structure and restart Emacs.
*)

複数のプロジェクトに取り組んでいるときは、
この設定の複数のバージョンを<<.emacs>>ファイルに残しておいて、
いつでもそのうちのひとつを除いてすべてをコメントアウトすると便利です。
プロジェクトの間で切り替えるには、コメント構造を変更してEmacsを再起動します。

(*
   Alternatively, we can revisit the directory-local settings approach and write the following into a file <<.dir-locals.el>> in <<CLIENT>>:
*)

あるいは、ディレクトリにローカルな設定の方法を再訪し、
<<CLIENT>> の <<.dir-locals.el>>ファイルに次のように書き込むことができます：

<<
((coq-mode . ((coq-prog-args .
  ("-emacs-U" "-R" "LIB" "Lib" "-R" "CLIENT" "Client")))))
>>

(*
   A downside of this approach is that users of your code may not want to trust the arbitrary Emacs Lisp programs that you are allowed to place in such files, so that they prefer to add mappings manually.
*)

このアプローチの欠点は、コードのユーザが、
そのようなファイルに置くことが許されている任意のEmacs Lispプログラムを信頼したくないことで、
マッピングを手動で追加することが好きなことです。

(*
   Relatively recent versions of Coq support another, more principled approach to all this.  A project's list of settings and source files may be saved in a single file named <<_CoqProject>>, which is processed uniformly by recent enough versions of <<coq_makefile>>, Proof General, and CoqIDE.  For details, see the Coq manual.
*)

Coqの比較的最近のバージョンでは、
このすべてに対するもう一つのより原理的なアプローチがサポートされています。
プロジェクトの設定とソースファイルのリストは、
最新のバージョンの、<<coq_makefile>>、Proof General、CoqIDEで
一様に処理される <<_CoqProject>> という名前の単一ファイルに保存されます。
詳細については、Coqマニュアルを参照してください。
 *)

(* END *)

(* Copyright (c) 2008-2013, 2015, 2017, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(**
(*%\chapter{Introduction}%*)
%\chapter{イントロダクション}%
*)

(** 
(* * Whence This Book? *)
* 本書の生い立ち

(*We would all like to have programs check that our programs are correct.  Due in no small part to some bold but unfulfilled promises in the history of computer science, today most people who write software, practitioners and academics alike, assume that the costs of formal program verification outweigh the benefits.  The purpose of this book is to convince you that the technology of program verification is mature enough today that it makes sense to use it in a support role in many kinds of research projects in computer science.  Beyond the convincing, I also want to provide a handbook on practical engineering of certified programs with the Coq proof assistant.  Almost every subject covered is also relevant to interactive computer theorem-proving in general, such as for traditional mathematical theorems.  In fact, I hope to demonstrate how verified programs are useful as building blocks in all sorts of formalizations.*)

プログラムの正しさは、プログラムに検査させたいものです。
実務に携わっている人であれ研究者であれ、
現在ソフトウェアを書いている人のなかには、
形式的プログラム検証にかかるコストは利益に見合わないものであると思い込んでいる人がかなり多くいます。
その思い込みの少なからぬ原因は、
かつて計算機科学の歴史において約束されながらいまだ成就していない大言壮語の数々にあるのでしょう。
プログラム検証の技術について言えば、いまや十分に成熟しており、
計算機科学の各種研究プロジェクトの支援に活用できるものになっています。
それを納得してもらうのが本書の目的です。
納得してもらうだけでなく、定理証明支援器Coqを使って認証付きプログラムを工学的に応用するために必要な手引き書となることも目指しています。
(* ノート(才川): すぐ後でcertified, certification, certificate, provingなどが
   微妙に違う意味で用いられるので, certifyの訳語を認証するとして統一的に訳してみた. 
   これは20161129時点での訳語集と反する（certifiedを証明付きと訳すことになっている）
   のでいずれ調整が必要になる. *)
本書のほとんどすべての題材は、計算機による対話的な定理証明全般にも関係しています。
そのなかには伝統的な数学の定理を対象にした内容も含まれます。
著者には、あらゆる種類の形式化にとって検証されたプログラムが部品として有用になることを本書を通じて実証してみせたいという思いもあります。
(* 池渕: 検証されたプログラムが形式化の部品になる、と唐突に言われるとどういうことなのか分からないので、「部品として有用になる」のほうがいいのではないかと思った。 *)

(*Research into mechanized theorem proving began in the second half of the 20th century, and some of the earliest practical work involved Nqthm%~\cite{Nqthm}\index{Nqthm}%, the "Boyer-Moore Theorem Prover," which was used to prove such theorems as correctness of a complete hardware and software stack%~\cite{Piton}%.  ACL2%~\cite{CAR}\index{ACL2}%, Nqthm's successor, has seen significant industry adoption, for instance, by AMD to verify correctness of floating-point division units%~\cite{AMD}%.*)

機械化された定理証明（mechanized theorem proving）の研究は、20世紀後半に始まりました。
最初期の実用的な成果のいくつかは、「Boyer-Moore定理証明器」Nqthm%~\cite{Nqthm}\index{Nqthm}%に関与するものでした。
Boyer-Moore定理証明器は、ハードウェアとソフトウェアの全体に対する正しさのような定理を証明するために用いられたものです%~\cite{Piton}%。
Nqthmの後継にあたるACL2%~\cite{CAR}\index{ACL2}%は、
AMD社によって浮動小数点除算ユニットの正しさの検証に用いられるなど、産業界で重用されています%~\cite{AMD}%。
(* 池渕: floating point を浮動小数と訳すのはあまり聞かない気がする *)

(*Around the beginning of the 21st century, the pace of progress in practical applications of interactive theorem proving accelerated significantly.  Several well-known formal developments have been carried out in Coq, the system that this book deals with.  In the realm of pure mathematics, Georges Gonthier built a machine-checked proof of the four-color theorem%~\cite{4C}%, a mathematical problem first posed more than a hundred years before, where the only previous proofs had required trusting ad-hoc software to do brute-force checking of key facts.  In the realm of program verification, Xavier Leroy led the CompCert project to produce a verified C compiler back-end%~\cite{CompCert}% robust enough to use with real embedded software.*)

21世紀初頭になると、対話的な定理証明の応用が大きく加速しました。
本書で説明するCoqを利用した形式的開発の事例がいくつも知られています。
純粋数学の分野では、Georges Gonthierにより、四色定理に対する機械的に検査された証明（machine-checked proof）が構築されました%~\cite{4C}%。
四色定理は百年以上前に提示された数学の問題です。
四色定理に対してそれまでに得られていた唯一の証明では、
鍵となる事実を総当たりで確かめるために使っていた場当たり的なソフトウェアの正しさを前提としていました。
プログラム検証（program verification）の分野では、
Xavier Leroyの主導によるCompCertプロジェクトにおいて、
現実の組み込みソフトウェアでの利用に耐えるだけの堅牢性を備える
検証されたCコンパイラのバックエンドが作り上げられました%~\cite{CompCert}%。

(*Many other recent projects have attracted attention by proving important theorems using computer proof assistant software.  For instance, the L4.verified project%~\cite{seL4}% led by Gerwin Klein has given a mechanized proof of correctness for a realistic microkernel, using the Isabelle/HOL proof assistant%~\cite{Isabelle/HOL}\index{Isabelle/HOL}%.  The amount of ongoing work in the area is so large that I cannot hope to list all the recent successes, so from this point I will assume that the reader is convinced both that we ought to want machine-checked proofs and that they seem to be feasible to produce.  (To readers not yet convinced, I suggest a Web search for "machine-checked proof"!)*)

それ以外にも、重要な定理を計算機証明支援ソフトウェアで証明することで注目を集めている最近のプロジェクトはたくさんあります。
例えば、Gerwin Kleinが主導するL4.verifiedプロジェクト%~\cite{seL4}%では、
証明支援系Isabelle/HOL%~\cite{Isabelle/HOL}\index{Isabelle/HOL}%を用いることで、
現実的なマイクロカーネルの正しさを機械的に証明しました。
機械的に検査された証明（machine-checked proof）に関しては、
あまりにも多くのプロジェクトが進行中であり、
最近の成功例をすべて挙げることはほぼ不可能です。
ここでは、機械的に検査された証明があると嬉しいこと、
そして、そのような証明を得ることが可能らしいことについて、
読者に十分に納得してもらえたものとして先に進みます
（まだ納得できない読者には、「machine-checked proof」でWebを検索することをお勧めします）。

(*The idea of %\index{certified program}% _certified program_ features prominently in this book's title.  Here the word "certified" does _not_ refer to governmental rules for how the reliability of engineered systems may be demonstrated to sufficiently high standards.  Rather, this concept of certification, a standard one in the programming languages and formal methods communities, has to do with the idea of a _certificate_, or formal mathematical artifact proving that a program meets its specification.  Government certification procedures rarely provide strong mathematical guarantees, while certified programming provides guarantees about as strong as anything we could hope for.  We trust the definition of a foundational mathematical logic, we trust an implementation of that logic, and we trust that we have encoded our informal intent properly in formal specifications, but few other opportunities remain to certify incorrect software.  For compilers and other programs that run in batch mode, the notion of a %\index{certifying program}% _certifying_ program is also common, where each run of the program outputs both an answer and a proof that the answer is correct.  Any certifying program can be composed with a proof checker to produce a certified program, and this book focuses on the certified case, while also introducing principles and techniques of general interest for stating and proving theorems in Coq.*)

_[認証付きプログラム]_（certified program%\index{認証付きプログラム}%）という考え方は、本書のタイトルにも明示されています。
この「認証」という語が意味しているのは、工学的なシステムの信頼性を示すために政府によって設定されるような規格のこと_[ではありません]_。
ここでいう「認証付き」という概念は、プログラミング言語や形式手法のコミュニティにおいては、
むしろ「証明書」（certificate）という考え方に関係しています。
詳しく言うと、プログラムが仕様に則していることを形式的な数学で証明するもののことを指します。
(* ノート(才川): certified, certification, certificate, proveなどの
   訳語調整しないと何言ってるのかわかりにくくなっている.
   あるいは思いきった意訳が必要かも. *)
(* ここのcertificateは、一般には証明書と訳されてるもののことですね。英語のノリで説明しているので、訳語調整はあきらめて、文意を日本語として納得できる文にするのがいいと思います（しました）。
それとは別に、「認証された」は訳語として微妙な気がします（とくにタイトルに使うとなると） -kshikano *)
(* 池渕: 元の訳が「つまり」から始まっていたが、「つまり」と言うには前後のつながりが非自明だと思った *)
政府による認証では、強力な数学的保証はまず与えられません。
一方、認証付きプログラムを書くことでは、望みうる限り最強の保証が与えられます。
基礎となる数理論理学を信頼し、その論理の実装を信頼し、
自分たちの非形式的な意図を正しく形式的仕様に落とし込めていることを信頼するならば、
正しくないソフトウェアが認証されてしまう可能性はほとんど残りません。
コンパイラをはじめ、バッチ処理として走るプログラムでは、
_[認証]_プログラム（certifying program%\index{認証プログラム}%）という表現も一般によく使われます。
これは、実行するたびに解答と一緒にその解答が正しいことの証明を出力するプログラムのことを指しています。
(* 池渕: certifying programが指すのは「〜〜が出力されること」ではなく「〜〜を出力するプログラム」なので、それが明確になるようにしてみた *)
証明検査器と組み合わせて認証プログラムを構成することもでき、その場合は認証プログラムが認証付きプログラムを生成できます。
(* 池渕: 元の文の「認証されたプログラムが得られるように」の「ように」が like の意味かと思って最初よく分からなかった。 *)
本書で焦点を当てるのは、認証付きプログラムのほうです。
同時に、Coqにおける定理の記述と証明にとって一般に必要となる興味深い原理や技術も紹介します。

%\medskip%

(*There are a good number of (though definitely not "many") tools that are in wide use today for building machine-checked mathematical proofs and machine-certified programs.  The following is my attempt at an exhaustive list of interactive "proof assistants" satisfying a few criteria.  First, the authors of each tool must intend for it to be put to use for software-related applications.  Second, there must have been enough engineering effort put into the tool that someone not doing research on the tool itself would feel his time was well spent using it.  A third criterion is more of an empirical validation of the second: the tool must have a significant user community outside of its own development team.*)
機械的に検査された数学の証明を構築したり機械的に認証付きプログラムを構築したりするためのツールは、決して多くはないものの、現在では広く利用されているものがいくつかあります。
以下に、いくつかの条件を満たす対話的な「証明支援器」を網羅してみました。
条件の一つめは、ツールの作者がソフトウェアに関連した応用を意図して開発しているツールであることです。
二つめは、そのツールを研究している当事者以外でも有意義に利用できるように十分な工学的努力がなされていることです。
三つめは、二つめの条件が実証されていること、つまり、ツールの開発チーム以外のユーザコミュニティがちゃんと存在していることです。

%
\medskip

\begin{tabular}{rl}
\textbf{ACL2} & \url{http://www.cs.utexas.edu/users/moore/acl2/} \\
\textbf{Coq} & \url{http://coq.inria.fr/} \\
\textbf{Isabelle/HOL} & \url{http://isabelle.in.tum.de/} \\
\textbf{PVS} & \url{http://pvs.csl.sri.com/} \\
\textbf{Twelf} & \url{http://www.twelf.org/} \\
\end{tabular}

\medskip
%
#
<table align="center">
<tr><td align="right"><b>ACL2</b></td> <td><a href="http://www.cs.utexas.edu/users/moore/acl2/">http://www.cs.utexas.edu/users/moore/acl2/</a></td></tr>
<tr><td align="right"><b>Coq</b></td> <td><a href="http://coq.inria.fr/">http://coq.inria.fr/</a></td></tr>
<tr><td align="right"><b>Isabelle/HOL</b></td> <td><a href="http://isabelle.in.tum.de/">http://isabelle.in.tum.de/</a></td></tr>
<tr><td align="right"><b>PVS</b></td> <td><a href="http://pvs.csl.sri.com/">http://pvs.csl.sri.com/</a></td></tr>
<tr><td align="right"><b>Twelf</b></td> <td><a href="http://www.twelf.org/">http://www.twelf.org/</a></td></tr>
</table>
#著者

(*Isabelle/HOL, implemented with the "proof assistant development framework" Isabelle%~\cite{Isabelle}%, is the most popular proof assistant for the HOL logic.  The other implementations of HOL can be considered equivalent for purposes of the discussion here.*)
Isabelle/HOLは、「証明支援器開発のフレームワーク」である
Isabelle%~\cite{Isabelle}%を用いて実装されており、
論理体系HOLのための証明支援器として最もよく利用されています。
(* 池渕: 「〜としては最もよく利用されている」だと否定的なニュアンスを感じたり他の用途もあることを示唆しているように感じる読者もいるかもしれないと思いました。「よく利用されているものです」は冗長で、「よく利用されています」のほうがシンプルに見えます。 *)
HOLの他の実装は、ここでの議論においてはIsabelle/HOLと同列に考えてかまいません。
*)

(** 
(* * Why Coq? *)
* どうしてCoqを使うのか

(*This book is going to be about certified programming using Coq, and I am convinced that it is the best tool for the job.  Coq has a number of very attractive properties, which I will summarize here, mentioning which of the other candidate tools lack which properties.*)
本書では、認証付きプログラミングについて、Coqを使って解説していきます。
著者は本書の目的にとってCoqが最適なツールだと確信しています。
Coqにはとても魅力的な性質が多く備わっています。
ここでは、上記で紹介したCoq以外のツールに欠けている性質にも言及しつつ、それらを要約します。

(* ** Based on a Higher-Order Functional Programming Language *)
** 高階の関数型プログラミング言語に基づいている

(*%\index{higher-order vs. first-order languages}%There is no reason to give up the familiar comforts of functional programming when you start writing certified programs.  All of the tools I listed are based on functional programming languages, which means you can use them without their proof-related features to write and run regular programs.

%\index{ACL2}%ACL2 is notable in this field for having only a _first-order_ language at its foundation.  That is, you cannot work with functions over functions and all those other treats of functional programming.  By giving up this facility, ACL2 can make broader assumptions about how well its proof automation will work, but we can generally recover the same advantages in other proof assistants when we happen to be programming in first-order fragments.*)

認証プログラムを書くからといって、関数型プログラミング言語の快適さを諦める必要はありません。
先に挙げたツールは、いずれも関数型プログラミング言語に基づいており、証明に関係する機能抜きでも普通のプログラムを書くのに使えます。

ACL2は、_[一階]_の言語のみを基礎とするので注意が必要です。
具体的には、関数上の関数といった、関数型プログラミングの便利な仕掛けが使えません。
ACL2では、その便利さを代償にすることで、自動証明がより広い前提のもとで動作することを可能にしています。
(* 池渕: 元の訳の「自動証明の動作に対して広範な前提を置く」は意味が分かるような分からないようなという感じだった *)

しかし他の証明支援器でも、一階の部分だけでプログラムを書くならば、一般には同様のことが再現可能です。

(* ** Dependent Types *)
** 依存型

(*A language with _dependent types_ may include references to programs inside of types.  For instance, the type of an array might include a program expression giving the size of the array, making it possible to verify absence of out-of-bounds accesses statically.  Dependent types can go even further than this, effectively capturing any correctness property in a type.  For instance, later in this book, we will see how to give a compiler a type that guarantees that it maps well-typed source programs to well-typed target programs.

%\index{ACL2}%ACL2 and %\index{HOL}%HOL lack dependent types outright.  Each of %\index{PVS}%PVS and %\index{Twelf}%Twelf supports a different strict subset of Coq's dependent type language.  Twelf's type language is restricted to a bare-bones, monomorphic lambda calculus, which places serious restrictions on how complicated _computations inside types_ can be.  This restriction is important for the soundness argument behind Twelf's approach to representing and checking proofs.

In contrast, %\index{PVS}%PVS's dependent types are much more general, but they are squeezed inside the single mechanism of _subset types_, where a normal type is refined by attaching a predicate over its elements.  Each member of the subset type is an element of the base type that satisfies the predicate.  Chapter 6 of this book introduces that style of programming in Coq, while the remaining chapters of Part II deal with features of dependent typing in Coq that go beyond what PVS supports.

Dependent types are useful not only because they help you express correctness properties in types.  Dependent types also often let you write certified programs _without writing anything that looks like a proof_.  Even with subset types, which for many contexts can be used to express any relevant property with enough acrobatics, the human driving the proof assistant usually has to build some proofs explicitly.  Writing formal proofs is hard, so we want to avoid it as far as possible.  Dependent types are invaluable for this purpose.*)

_[依存型]_を持つ言語では、型の内部にプログラムに対する言及を含められます。
例えば、配列の型にその配列の長さを指定するプログラム式を含ませられ、それによって配列の範囲外アクセスがないかどうかを静的に検査できます。
(* 池渕: 「配列を表す型」は依存型の文脈だと「配列の型」とは別物と解釈できてしまいそう。
 *「型の内部にプログラムに対する言及を含められ」ることへの「例えば」なので、まず「配列の型にその長さを指定するプログラム式を含ませられる」ことをはっきりと主張したほうがいいと思った。
 *「指定する」は意訳だけど、そっちのほうが分かりやすいと思う。 *)
依存型の利用例はそれだけではありません。
正しさを表すどんな性質も、一つの型の中で効果的に捉えられるようになるのです。
(* 池渕: 「型によって」だと、型そのものが「正しさを表す性質」を表現するかどうかは分からなくて、たとえば「型を補助的に使って性質を捉える」とも読めてしまうと思った *)
後ほど本書では、正しく型付けされたソースプログラムから正しく型付けされたターゲットプログラムへと変換されることを保証する型を、コンパイラに対して与える方法を見ていきます。

%\index{ACL2}%ACL2と%\index{HOL}%HOLでは依存型をまったく使えません。
%\index{PVS}%PVSと%\index{Twelf}%TwelfはそれぞれCoqの依存型言語のサブセットをサポートしています。
(* 池渕: 言語のsubsetはサブセットと呼ぶ方がプログラム畑の人には親近感がありそう *)
Twelfの型言語は必要最小限である単相ラムダ計算に制限されていることから、_[型の内部に]_どのくらい複雑な計算が書けるかについて重大な制約があります。
この制約は、証明の表現と検査に対するTwelfの方法論の健全性をめぐる議論で重要になっています。
この制約は、Twelfの証明の表現方法と検査方法に対する健全性において重要になっています。
(* 池渕: 「健全性をめぐる議論」だと「研究者同士が健全性について議論し合っている」というような意味に見えた *)

PVSの依存型は、Twelfのものより制約が少ないですが、_[subset type]_という単一の仕組みの内部に押し込められています。
(* 池渕: 元の訳の「一般的」はcommonなのかgeneralなのか分からなかった *)
この仕組みでは、要素に対する述語を付加することで、通常の型が詳細化されます。
(* 池渕: “refine”は専門用語で、日本語では「詳細化する」だと思います *)
subset typeの要素はその述語を満たすような基礎型の要素です。
本書でも、このようなスタイルのプログラミングをCoqで実現する方法について第6章で紹介します。
第II部の残りの章で扱うCoqの依存型付けの機能はPVSの範囲外の内容です。

依存型が有用なのは、正しさを型の内部で表現できるようになるからだけではありません。
依存型のおかげで、_[証明らしいものを書かずに]_、認証付きプログラムを書ける場合があるのです。
subset typeでも、離れ業を駆使すれば、妥当な性質を表現できる場合があります。
しかしsubset typeが使えたとしても、ある種の証明については、証明支援器を利用する人間が明示的に証明を構築するしかありません。
形式的な証明を書くのは大変なので、なるべく避けたいものです。
その目的にとって依存型には計り知れない価値があります。

(* ** An Easy-to-Check Kernel Proof Language *)
** 核となる証明言語が検査しやすい

(*%\index{de Bruijn criterion}%Scores of automated decision procedures are useful in practical theorem proving, but it is unfortunate to have to trust in the correct implementation of each procedure.  Proof assistants satisfy the "de Bruijn criterion" when they produce _proof terms_ in small kernel languages, even when they use complicated and extensible procedures to seek out proofs in the first place.  These core languages have feature complexity on par with what you find in proposals for formal foundations for mathematics (e.g., ZF set theory).  To believe a proof, we can ignore the possibility of bugs during _search_ and just rely on a (relatively small) proof-checking kernel that we apply to the _result_ of the search.

Coq meets the de Bruijn criterion, while %\index{ACL2}%ACL2 does not, as it employs fancy decision procedures that produce no "evidence trails" justifying their results.  %\index{PVS}%PVS supports _strategies_ that implement fancier proof procedures in terms of a set of primitive proof steps, where the primitive steps are less primitive than in Coq.  For instance, a propositional tautology solver is included as a primitive, so it is a question of taste whether such a system meets the de Bruijn criterion.  The HOL implementations meet the de Bruijn criterion more manifestly; for Twelf, the situation is murkier.*)

実践的な定理証明においては、たくさんの自動化された決定手続き（automated decision procedures）を便利に使います。
しかし、それぞれの決定手続きについて、その実装が正しいかどうかは信頼するしかない、というのでは困ります。
証明支援器が証明を探し出すために複雑で拡張可能な手続きを使うとしても、
核となる小さな言語で_[証明項]_が表現される場合、その証明支援器は「de Bruijn基準%\index{de Bruijn基準}%を満たす」と言います。
(* 池渕: 「証明を探し出すために複雑で拡張可能な手続きを使うとしても」は文の中で補助的であってかつ長いので、
 * メインの「核となる小さな言語で_[証明項]_が表現される場合」「『de Bruijn criterionを満たす』と言います」の間に入っていると分かりづらく感じた。
 * あと、「証明項」という言葉に対して注釈を付けてもいいかもしれない *)
こうした核となる言語の機能による複雑性は、数学の形式的な基礎付け（ZF集合論など）と比肩できます。
(* 池渕: 元の「数学における基礎付け」は「数学の基礎付け」を含むけど、他の基礎付け(数学を使った基礎付け)とも思えてしまう(ZF集合論など、と書いてあるけれども) *)
証明を信じるには、証明の_[探索]_の際のバグの可能性は無視してもよく、探索の_[結果]_に対して証明を検査する（比較的小さな）核が信頼できればいいというわけです。
(* 原文でも “proof search” ではなく単に “search” としか言っていないけれど、「証明の」探索であると明記したほうが分かりやすいと思う。 *)

Coqはde Bruijn criterionを満たします。一方、ACL2は満たしません。
なぜならACL2では、結果を正当化する「証拠となるもの」を生成しない、手の込んだ決定手続きを採用しているからです。
PVS%\index{PVS}%は_strategy_と呼ばれる、より手の込んだ証明手続きを原始的な証明ステップの集まりとして実装する機能を持ちます。
ただし、PVSにおける原始的な証明ステップは、Coqにおけるものほどは原始的ではありません。
(* 池渕: fancyについて「手の込んだ」が「独特な」に編集されていたが、ACL2のその手続きは「独特」ではないと思うので、私は「手の込んだ」のほうがいいように思えた。 *)
例えばPVSでは、命題論理の恒真式ソルバが原始的な証明ステップとされているので、PVSがde Bruijn criterionを満たすかどうかは人によって意見が分かれます。
HOLの各実装については、もう少しはっきりとde Bruijn criterionに適合するといえます。
Twelfについては、それほどはっきりとは言い切れません。

(* ** Convenient Programmable Proof Automation *)
** プログラム可能な証明自動化の利便性

(*A commitment to a kernel proof language opens up wide possibilities for user extension of proof automation systems, without allowing user mistakes to trick the overall system into accepting invalid proofs.  Almost any interesting verification problem is undecidable, so it is important to help users build their own procedures for solving the restricted problems that they encounter in particular theorems.

%\index{Twelf}%Twelf features no proof automation marked as a bona fide part of the latest release; there is some automation code included for testing purposes.  The Twelf style is based on writing out all proofs in full detail.  Because Twelf is specialized to the domain of syntactic metatheory proofs about programming languages and logics, it is feasible to use it to write those kinds of proofs manually.  Outside that domain, the lack of automation can be a serious obstacle to productivity.  Most kinds of program verification fall outside Twelf's forte.

Of the remaining tools, all can support user extension with new decision procedures by hacking directly in the tool's implementation language (such as OCaml for Coq).  Since %\index{ACL2}%ACL2 and %\index{PVS}%PVS do not satisfy the de Bruijn criterion, overall correctness is at the mercy of the authors of new procedures.

%\index{Isabelle/HOL}%Isabelle/HOL and Coq both support coding new proof manipulations in ML in ways that cannot lead to the acceptance of invalid proofs.  Additionally, Coq includes a domain-specific language for coding decision procedures in normal Coq source code, with no need to break out into ML.  This language is called %\index{Ltac}%Ltac, and I think of it as the unsung hero of the proof assistant world.  Not only does Ltac prevent you from making fatal mistakes, it also includes a number of novel programming constructs which combine to make a "proof by decision procedure" style very pleasant.  We will meet these features in the chapters to come.*)

証明自動化のシステムにおいて、利用者が証明言語の核となる部分に手を入れられるようになっていれば、さまざまな拡張の可能性が生まれます。
もちろん、利用者のミスによってシステム全体がおかしなことになり、不正な証明が受け入れられてしまってはいけないので、そのようなことは防ぐ必要があります。
検証に関する問題で興味を引くようなものは、ほとんどが決定不能です。
そのため、利用者が独自の手続きを構成できるようになっていて、特定の定理に出てくる限定的な問題を解けるようになっていることが重要になります。

Twelf%\index{Twelf}%の最新のリリースには、正真正銘の証明自動化の機能がありません。
テストを目的とした自動化のためのコードがいくつかあるだけです。
証明を完全に細部まですべて書き出すのが、Twelfの基本的なやり方です。
Twelfの用途は、プログラミング言語と論理に関する構文的なメタ定理の証明に特化しており、その手の証明を手動で書くというものです。
それ以外の分野では、自動化の機能がないことから、あまり生産的ではありません。
プログラム証明の大半はTwelfの範疇ではないのです。

Twelf以外のツールはすべて、ツールの実装に使われている言語（Coqの場合はOCaml）を直接利用して、利用者が新しい決定手続きを拡張できるようになっています。
ACL2%\index{ACL2}%とPVS%\index{PVS}%はde Bruijn criterionを満たさないので、証明全体の正しさは新しい決定手続きの出来に左右されます。

Isabelle/HOL%\index{Isabelle/HOL}%とCoqは、どちらもMLを使って新たな証明操作を記述できます。
それによって不正な証明が受け入れられることはありません。
さらにCoqには、通常のCoqのソースコードの中に決定手続きをコーディングできるドメイン特化言語が備わっているので、外部でMLを書く必要がありません。
このドメイン特化言語はLtacと呼ばれており、証明支援器の世界における陰の英雄ともいえるでしょう。
Ltacによって利用者による深刻な間違いが防止されるだけではありません。
Ltacには斬新なプログラミングの構成要素がいくつも含まれており、それらを組み合わせることで「決定手続きによる証明」が快適にできるようになります。
こうしたLtacの機能は以降の各章で見ていきます。

(* ** Proof by Reflection *)
** リフレクションによる証明

(*%\index{reflection}\index{proof by reflection}%A surprising wealth of benefits follows from choosing a proof language that integrates a rich notion of computation.  Coq includes programs and proof terms in the same syntactic class.  This makes it easy to write programs that compute proofs.  With rich enough dependent types, such programs are _certified decision procedures_.  In such cases, these certified procedures can be put to good use _without ever running them_!  Their types guarantee that, if we did bother to run them, we would receive proper "ground" proofs.

The critical ingredient for this technique, many of whose instances are referred to as _proof by reflection_, is a way of inducing non-trivial computation inside of logical propositions during proof checking.  Further, most of these instances require dependent types to make it possible to state the appropriate theorems.  Of the proof assistants I listed, only Coq really provides support for the type-level computation style of reflection, though PVS supports very similar functionality via refinement types.*)

証明言語として、計算に関する多様な概念を利用できるものを選べば、嬉しいことがたくさんあります。
Coqでは、プログラムと証明項を同じ階層の構文で表現できます。
そのおかげで、証明を計算するプログラムが簡単に書けます。
そのようなプログラムは、十分に豊富な依存型のおかげで、_[認証付き決定手続き]_（certified decision procedure）になります。
そして、そのような認証付き手続きは、実行するまでもなく有用なのです！
型により、もしあえて実行すれば適切で十分に根拠のある証明が得られる、ということが保証されるのです。

このテクニックで中心となるのは、証明検査の際に、論理的な命題の中に非自明な計算を取り入れるというものです。
その実践例の多くは_[リフレクションによる証明]_（proof by reflection）と呼ばれ%\index{reflection}\index{proof by reflection}%、
さらにその大半は、適切な定理の表現を可能とするために依存型を必要とします。
先に挙げた証明支援器のうち、型レベル計算という方法でリフレクションに対応しているのはCoqだけです。
なお、PVSは、これによく似たrefinement typeという機能に対応しています。
*)

(**
(* * Why Not a Different Dependently Typed Language? *)
* 他の依存型の言語ではだめなのか

(*The logic and programming language behind Coq belongs to a type-theory ecosystem with a good number of other thriving members.  %\index{Agda}%{{http://appserv.cs.chalmers.se/users/ulfn/wiki/agda.php}Agda} and %\index{Epigram}%{{https://code.google.com/p/epigram/}Epigram} are the most developed tools among the alternatives to Coq, and there are others that are earlier in their lifecycles.  All of the languages in this family feel sort of like different historical offshoots of Latin.  The hardest conceptual epiphanies are, for the most part, portable among all the languages.  Given this, why choose Coq for certified programming?

I think the answer is simple.  None of the competition has well-developed systems for tactic-based theorem proving.  Agda and Epigram are designed and marketed more as programming languages than proof assistants.  Dependent types are great, because they often help you prove deep theorems without doing anything that feels like proving.  Nonetheless, almost any interesting certified programming project will benefit from some activity that deserves to be called proving, and many interesting projects absolutely require semi-automated proving, to protect the sanity of the programmer.  Informally, proving is unavoidable when any correctness proof for a program has a structure that does not mirror the structure of the program itself.  An example is a compiler correctness proof, which probably proceeds by induction on program execution traces, which have no simple relationship with the structure of the compiler or the structure of the programs it compiles.  In building such proofs, a mature system for scripted proof automation is invaluable.

On the other hand, Agda, Epigram, and similar tools have less implementation baggage associated with them, and so they tend to be the default first homes of innovations in practical type theory.  Some significant kinds of dependently typed programs are much easier to write in Agda and Epigram than in Coq.  The former tools may very well be superior choices for projects that do not involve any "proving."  Anecdotally, I have gotten the impression that manual proving is orders of magnitudes more costly than manual coping with Coq's lack of programming bells and whistles.  In this book, I will devote significant space to patterns for programming with dependent types in Coq as it is today.  We can hope that the type theory community is tending towards convergence on the right set of features for practical programming with dependent types, and that we will eventually have a single tool embodying those features.*)

Coqの論理とプログラミング言語の拠り所となっている型理論の枠組みは、他の技術でも利用されています。
Coqの代替として考えられるツールのうち、特に成熟したものとしては、
{{http://appserv.cs.chalmers.se/users/ulfn/wiki/agda.php}Agda}%\index{Agda}%および
{{https://code.google.com/p/epigram/}Epigram}%\index{Epigram}%があります。
それ以外にも、現在ではまだ発展途上にある仕組みがいくつかあります。
これらの言語の違いは、ラテン語から歴史的に派生した言語の違いくらいのものです。
特に根幹となる概念的な洞察については、どの言語も互いにほとんど似通っています。
であるならば、認証付きプログラムを書くためにCoqを選ぶ理由はどこにあるのでしょうか。

著者にとって、その答えは単純です。Coq以外の競合では、tacticを使った定理証明のためのシステムが不十分だからです。AgdaとEpigramは、定理支援器というより、プログラミング言語として知られています。
依存型のすばらしさは、証明らしいことを何もせずに、深い定理の証明が可能になる場合がある点です。
そうはいっても、認証付きプログラムに関するプロジェクトのうち興味深い内容を持つものでは、やはり証明と呼ぶしかない行為が重要になるでしょう。
そして、そうしたプロジェクトにおいてプログラマの正気を保つには、証明の半自動化が絶対に必要になります。
これは非形式的な言い分ですが、あるプログラムの正しさの証明が、そのプログラム自体の構造をそのまま反映したものでない場合、実際に証明することは避けられません。
例えば、コンパイラの正しさを証明する際には、プログラムの実行トレースに対する帰納法を使うことになるでしょうが、その証明と、コンパイラの構造やコンパイラが生成するプログラムの構造との間には、単純な関係がありません。
そのような証明を構築するにあたり、スクリプトでの証明の自動化のための洗練されたシステムが持つ価値は計り知れません。

AgdaやEpigramなどのツールには、そうした仕組みの実装の余地があまりありません。
だからこそ、それらのツールには、実践的な型理論における新しい試みが活発であるという傾向があります。
依存型を駆使したプログラムのなかには、AgdaやEpigramのほうがCoqよりも書きやすいものもあります。
「証明」に関係しないプロジェクトであれば、AgdaやEpigramのほうが優れた選択肢かもしれません。
これは著者の感想ですが、手動で証明を書くことは、プログラミングのための便利な仕組みが少ないCoqで手動でプログラムをコピーするより、何段階もコストがかかる作業です。
本書では、現在のCoqにおける依存型を使ったプログラミングのパターンについて、かなりの紙面を割いて説明する予定です。
依存型を使った実践的なプログラミングにとって必要となる機能について型理論のコミュニティの見解が収斂しつつあり、将来的にはそれらの機能を包含した単一のツールが登場することに期待しましょう。

*)

(**
(* * Engineering with a Proof Assistant *)
* 証明支援器を使ったエンジニアリング

(*In comparisons with its competitors, Coq is often derided for promoting unreadable proofs.  It is very easy to write proof scripts that manipulate proof goals imperatively, with no structure to aid readers.  Such developments are nightmares to maintain, and they certainly do not manage to convey "why the theorem is true" to anyone but the original author.  One additional (and not insignificant) purpose of this book is to show why it is unfair and unproductive to dismiss Coq based on the existence of such developments.

I will go out on a limb and guess that the reader is a fan of some programming language and may even have been involved in teaching that language to undergraduates.  I want to propose an analogy between two attitudes: coming to a negative conclusion about Coq after reading common Coq developments in the wild, and coming to a negative conclusion about Your Favorite Language after looking at the programs undergraduates write in it in the first week of class.  The pragmatics of mechanized proving and program verification have been under serious study for much less time than the pragmatics of programming have been.  The computer theorem proving community is still developing the key insights that correspond to those that programming texts and instructors impart to their students, to help those students get over that critical hump where using the language stops being more trouble than it is worth.  Most of the insights for Coq are barely even disseminated among the experts, let alone set down in a tutorial form.  I hope to use this book to go a long way towards remedying that.

If I do that job well, then this book should be of interest even to people who have participated in classes or tutorials specifically about Coq.  The book should even be useful to people who have been using Coq for years but who are mystified when their Coq developments prove impenetrable by colleagues.  The crucial angle in this book is that there are "design patterns" for reliably avoiding the really grungy parts of theorem proving, and consistent use of these patterns can get you over the hump to the point where it is worth your while to use Coq to prove your theorems and certify your programs, even if formal verification is not your main concern in a project.  We will follow this theme by pursuing two main methods for replacing manual proofs with more understandable artifacts: dependently typed functions and custom Ltac decision procedures.*)

Coqの証明は他のシステムに比べて読みにくいと言われることが少なくありません。
証明を読みやすくするための構造を意識せずに、証明の帰結を操作する命令的なスクリプトとして証明を書くのは、とても簡単です。
そのような形で開発された証明を保守するのは悪夢でしょう。
それに、「なぜその定義が真になるのか」が証明を書いた本人以外の誰にも伝わらない証明になってしまいます。
そんなふうに開発された証明があるからCoqは使えない、という主張がいかに不公平で非生産的であるかを示すことも、本書のささやかな目的のひとつです。

読者の皆さんには好きなプログラミング言語があり、それを学生に教えたことがあるような人もいると思います。
どこかでCoqにより開発されたものを読み、それでCoqに対して否定的な印象を抱くことは、あなたが好きな言語を教わった学生が最初の週にその言語を使って書いたプログラムを見て、あなたがその言語に否定的な印象を抱くようなものであると言えるのではないでしょうか。
機械的な証明とプログラム検証の実践面には、プログラミングの実践面に比べて、まだまだ研究に費やされている年月が足りません。
プログラミングの説明では、その言語を使うことに伴う大変さを凌駕する価値がどの辺りにあるのかを、教科書や講師が学生に伝えることができます。
コンピュータによる定理証明のコミュニティは、そのような習得において鍵となる洞察をまだ模索しているところです。
Coqに関しては、そのような洞察はまだまだ専門家の間で普及しているだけであり、チュートリアルのような形にもまとまっていません。
本書がその状況を変える長い道のりの一歩になればと考えています。

もしそれがうまくいったなら、本書は、Coqに特化した入門授業やチュートリアルに参加する人にとっても有意義なものになるでしょう。
すでに何年間もCoqを使っているけれど、Coqで開発したものを同僚に理解してもらえないような人にも、本書は有益なはずです。
定理証明には、泥臭い部分を安全に回避するための「デザインパターン」があります。
そのパターンをきちんと活用すれば、形式的なプログラム検証が主目的でないプロジェクトであっても、少しだけ時間を割いてCoqにより定理を証明し自分のプログラムを認証する意味があるような部分を見極められるようになるでしょう。
これが本書における極めて重要な考え方です。
その主題にのっとり、手動による証明を置き換えてより理解しやすい形にするための2つの方法として、
依存型を持つ関数と独自のLtac決定手続きを駆使します。
*)

(**
(* * Prerequisites *)
* 前提知識

(*I try to keep the required background knowledge to a minimum in this book.  I will assume familiarity with the material from usual discrete math and logic courses taken by undergraduate computer science majors, and I will assume that readers have significant experience programming in one of the ML dialects, in Haskell, or in some other, closely related language.  Experience with only dynamically typed functional languages might lead to befuddlement in some places, but a reader who has come to understand Scheme deeply will probably be fine.

My background is in programming languages, formal semantics, and program verification.  I sometimes use examples from that domain.  As a reference on these topics, I recommend _Types and Programming Languages_ %\cite{TAPL}%, by Benjamin C. Pierce; however, I have tried to choose examples so that they may be understood without background in semantics.*)

本書では、必要な背景知識が最小限になるように心がけます。
前提とするのは、情報科学専攻の学部で履修する一般的な離散数学と論理学に馴染みがあり、
MLの方言かHaskell、もしくはそれらに類する言語によるプログラミングをそれなりに経験していることです。
動的型付きの関数型言語しか使った経験がないと、理解できずに戸惑う箇所があるかもしれませんが、
Schemeに対する深い理解がある読者であれば、おそらく大丈夫でしょう。

著者の専門は、プログラミング言語、形式意味論、そしてプログラム検証です。
これらの分野における話題を例として使用する場合があります。
そうした話題についての参考文献としては、_[Types and Programming Languages]_ %\cite{TAPL}%をお勧めします。とはいえ、できるだけ背景の意味を知らなくても理解できるような例を選んだつもりです。

(* * Using This Book *)
* 本書の使い方

(*This book is generated automatically from Coq source files using the wonderful coqdoc program.  The latest PDF version, with hyperlinks from identifier uses to the corresponding definitions, is available at:
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.pdf}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.pdf">http://adam.chlipala.net/cpdt/cpdt.pdf</a></tt></blockquote>#
There is also an online HTML version available, which of course also provides hyperlinks:
%\begin{center}\url{http://adam.chlipala.net/cpdt/html/toc.html}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/html/toc.html">http://adam.chlipala.net/cpdt/html/toc.html</a></tt></blockquote>#
The source code to the book is also freely available at:
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote>#

There, you can find all of the code appearing in this book, with prose interspersed in comments, in exactly the order that you find in this document.  You can step through the code interactively with your chosen graphical Coq interface.  The code also has special comments indicating which parts of the chapters make suitable starting points for interactive class sessions, where the class works together to construct the programs and proofs.  The included Makefile has a target <<templates>> for building a fresh set of class template files automatically from the book source.

A traditional printed version of the book is slated to appear from MIT Press in the future.  The online versions will remain available at no cost even after the printed book is released, and I intend to keep the source code up-to-date with bug fixes and compatibility changes to track new Coq releases.

%\index{graphical interfaces to Coq}%I believe that a good graphical interface to Coq is crucial for using it productively.  I use the %\index{Proof General}%{{http://proofgeneral.inf.ed.ac.uk/}Proof General} mode for Emacs, which supports a number of other proof assistants besides Coq.  There is also the standalone %\index{CoqIDE}%CoqIDE program developed by the Coq team.  I like being able to combine certified programming and proving with other kinds of work inside the same full-featured editor.  In the initial part of this book, I will reference Proof General procedures explicitly, in introducing how to use Coq, but most of the book will be interface-agnostic, so feel free to use CoqIDE if you prefer it.  The one issue with CoqIDE before version 8.4, regarding running through the book source, is that I will sometimes begin a proof attempt but cancel it with the Coq [Abort] or #<span class="inlinecode"><span class="id" type="keyword">#%\coqdockw{%Restart%}%#</span></span># commands, which CoqIDE did not support until recently.  It would be bad form to leave such commands lying around in a real, finished development, but I find these commands helpful in writing single source files that trace a user's thought process in designing a proof.*)

本書は、Coqのソースファイルから、coqdocという素晴らしいプログラムを使って自動的に生成されています。
最新のPDFは、識別子から対応する定義へとハイパーリンクが貼られた状態で、以下から入手できます。
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.pdf}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.pdf">http://adam.chlipala.net/cpdt/cpdt.pdf</a></tt></blockquote>#
オンラインのHTML版も利用できます。もちろんこちらにもハイパーリンクが付いています。
%\begin{center}\url{http://adam.chlipala.net/cpdt/html/toc.html}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/html/toc.html">http://adam.chlipala.net/cpdt/html/toc.html</a></tt></blockquote>#
本書のソースファイルも無料で利用できます。
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote>#

ソースファイルには、文章によるコメントが随所に付された状態で、
本書に掲載されているすべてのコードが本書に登場するのと同じ順番で含まれています。
お好きなCoqのGUIを使って、そのコードを1ステップずつ対話的に実行していけます。
対話的なセッションにおいて、プログラムと証明の構成にクラスを利用する場合には、どの章から始めればいいのかを示す特別なコメントも挿入してあります。
Makefileの<<templates>>というターゲットを使うことで、クラスのテンプレートとなるファイルを書籍のソースから自動で新規に構築できるようになっています。

印刷された従来型の書籍は、MIT Pressから発行されます。
印刷された本が出た後も、オンライン版は無償で利用可能な状態のままとします。
ソースコードに対するバグ修正や新しいバージョンのCoqのリリースに伴う変更にも追随していく予定です。

Coqを生産的に使うには優れたGUIが必要不可欠でしょう%\index{graphical interfaces to Coq}%。
著者はEmacsの%\index{Proof General}%{{http://proofgeneral.inf.ed.ac.uk/}Proof General}モードを使っています。
Proof Generalは、Coqだけでなく、いくつもの証明支援系に対応しています。
Coqの開発チームが用意しているスタンドアローンのCoqIDE%\index{CoqIDE}%というプログラムもあります。
著者自身は、認証付きプログラムと証明の開発を、他のさまざまな作業と一緒に同じエディタ上で進めるのが好きです。
本書では、最初にCoqの使い方を紹介する際にはProof Generalでの操作を示しますが、
ほとんどの内容はGUIに依存しないのでCoqIDEを使ってもかまいません。
ただし、本書のソースにはCoqの[Abort]もしくは#<span class="inlinecode"><span class="id" type="keyword">#%\coqdockw{%Restart%}%#</span></span>#コマンドを使って証明を途中でキャンセルしている箇所があり、CoqIDEでは最近までこれらの対応していないので、バージョン8.4以下のCoqIDEでソースを実行する場合には問題があります。
これらのコマンドは、開発が終わった後のソースファイルには残しておかないほうがいいのでしょうが、証明を設計している人間の思考プロセスをソースファイルだけでたどる手助けになると思うので、本書のソースには残してあります。

(* ** Reading This Book *)
** 本書の読み方

(*For experts in functional programming or formal methods, learning to use Coq is not hard, in a sense.  The Coq manual%~\cite{CoqManual}%, the textbook by Bertot and Cast%\'%eran%~\cite{CoqArt}%, and Pierce et al.'s %\emph{%Software Foundations%}\footnote{\url{http://www.cis.upenn.edu/~bcpierce/sf/}}% have helped many people become productive Coq users.  However, I believe that the best ways to manage significant Coq developments are far from settled.  In this book, I mean to propose my own techniques, and, rather than treating them as advanced material for a final chapter or two, I employ them from the very beginning.  After a first chapter showing off what can be done with dependent types, I retreat into simpler programming styles for the first part of the book.  I adopt the other main thrust of the book, Ltac proof automation, more or less from the very start of the technical exposition.

Some readers have suggested that I give multiple recommended reading orders in this introduction, targeted at people with different levels of Coq expertise.  It is certainly true that Part I of the book devotes significant space to basic concepts that most Coq users already know quite well.  However, as I am introducing these concepts, I am also developing my preferred automated proof style, so I think even the chapters on basics are worth reading for experienced Coq hackers.

Readers with no prior Coq experience can ignore the preceding discussion!  I hope that my heavy reliance on proof automation early on will seem like the most natural way to go, such that you may wonder why others are spending so much time entering sequences of proof steps manually.

Coq is a very complex system, with many different commands driven more by pragmatic concerns than by any overarching aesthetic principle.  When I use some construct for the first time, I try to give a one-sentence intuition for what it accomplishes, but I leave the details to the Coq reference manual%~\cite{CoqManual}%.  I expect that readers interested in complete understanding will be consulting that manual frequently; in that sense, this book is not meant to be completely standalone.  I often use constructs in code snippets without first introducing them at all, but explanations should always follow in the prose paragraphs immediately after the offending snippets.

Previous versions of the book included some suggested exercises at the ends of chapters.  Since then, I have decided to remove the exercises and focus on the main book exposition.  A database of exercises proposed by various readers of the book is #<a href="http://adam.chlipala.net/cpdt/ex/">#available on the Web#</a>#%\footnote{\url{http://adam.chlipala.net/cpdt/ex/}}%.  I do want to suggest, though, that the best way to learn Coq is to get started applying it in a real project, rather than focusing on artificial exercises. *)

関数プログラミングや形式手法の熟練者にとって、Coqの使い方を習得する際の困難は何もないと言えます。
Coqのマニュアル%~\cite{CoqManual}%や、BertotとCasteranによる教科書%~\cite{CoqArt}%、Pierceらによる%``\emph{%Software Foundations%''}\footnote{\url{http://www.cis.upenn.edu/~bcpierce/sf/}}%によりCoqを使いこなせるようになった人は数多くいます。
とはいえ、それなりの規模でCoqによる開発をうまくやる最善の方法は、まだまだ確立には程遠いというのが著者の考えです。
著者は、本書で自分自身が持つテクニックを示すつもりです。
しかもそれらのテクニックを、最後の数章で発展的な話題として扱うのではなく、冒頭から導入していきます。
第1章では、依存型で何ができるかをお見せします。
そのあとの第1部では、よりシンプルなスタイルのプログラミングに戻します。
本書のもう1つの主眼であるLtacによる証明の自動化についても、ほぼ冒頭から技術的な説明を導入していきます。

何人かの方々からは、各章を読む順番について、Coqの熟練度に応じたお勧めをイントロダクションで示してはどうかという提案をしていただきました。
確かに、本書の第1部ではCoqを利用している大部分の人がよく知っている基本的な概念の説明に紙面の多くを割いています。
しかし、そうした概念を提示する際には著者が好ましいと考える証明自動化のスタイルも明らかにしていくので、たとえ基礎的な章であっても、経験豊富なCoqハッカーにとって読む価値があるものと考えています。

これまでCoqを使ったことがない読者には関係ない話でしたね！
証明の各ステップを時間をかけて手動で入力する人のことが不思議に見えるくらい、最初から著者が証明の自動化を当てにしていることを当然に感じてもらえればと思います。

Coqはとても複雑なシステムです。何か重要で審美的な原理でなく、もっと実用的な観点で必要になるコマンドがたくさん用意されています。
本書では、はじめて登場する構成概念については、それが何を実現するものなのか、短文で直観的な説明を与えます。しかし、詳細な説明はCoqのリファレンスマニュアル%~\cite{CoqManual}%に譲ります。
完璧な理解を求める読者は、リファレンスマニュアルを頻繁に参照することになるでしょう。
その意味で本書は完全にスタンドアローンになるようには書かれていません。
コード中には、まだ説明していない構成概念が出てくることもありますが、これらは常にコードの直後の段落で説明していきます。

以前は各章の終わりに演習問題を付けていましたが、演習問題はなくして解説に注力することにしました。
#<a href="http://adam.chlipala.net/cpdt/ex/">#Webでは、さまざまな本書の読者向けの演習問題のデータベースが利用できます#</a>#%\footnote{\url{http://adam.chlipala.net/cpdt/ex/}}%。
ただ著者としては、人工的な演習問題を解くよりも、Coqを実際のプロジェクトに応用し始めることがCoqを学ぶ最良の方法であると言いたいところです。

(* ** On the Tactic Library *)
** タクティクライブラリについて

(*To make it possible to start from fancy proof automation, rather than working up to it, I have included with the book source a library of _tactics_, or programs that find proofs, since the built-in Coq tactics do not support a high enough level of automation.  I use these tactics even from the first chapter with code examples.

Some readers have asked about the pragmatics of using this tactic library in their own developments.  My position there is that this tactic library was designed with the specific examples of the book in mind; I do not recommend using it in other settings.  Part III should impart the necessary skills to reimplement these tactics and beyond.  One generally deals with undecidable problems in interactive theorem proving, so there can be no tactic that solves all goals, though the %\index{tactics!crush}%[crush] tactic that we will meet soon may sometimes feel like that!  There are still very useful tricks found in the implementations of [crush] and its cousins, so it may be useful to examine the commented source file <<CpdtTactics.v>>.  I implement a new tactic library for each new project, since each project involves a different mix of undecidable theories where a different set of heuristics turns out to work well; and that is what I recommend others do, too.*)

徐々に手の込んだ自動証明へ進むのではなく、いきなり実践したいので、本書のソースにはそのための_[タクティク]_のライブラリを含めてあります。
タクティクとは証明を探すプログラムのことです。
あらかじめCoqにも組み込まれていますが、高級な自動証明には対応していないので、本書専用のタクティクライブラリを用意しました。
このタクティクライブラリは、本書の最初の章のコード例から使っています。

この本書専用のタクティクライブラリを自分の開発に使いたいという声をいただくこともあります。
著者としては、本書の特定の例を念頭に置いて設計したタクティクライブラリなので、他の場面での使用は推奨しません。
これらのタクティクを再実装したり、その先に進むために必要な技術については、第三部で扱います。
対話的な定理証明では決定不可能な問題を扱うことも多いので、すべてのゴールを解くようなタクティクはありえないでしょう。
ただ、すぐに後で登場する[crush]%\index{tactics!crush}%タクティクは、そのような万能のタクティクに感じられるかもしれません。
[crush]に類するタクティクの実装では、とても便利なトリックを使っているので、コメント付きのソースファイル<<CpdtTactics.v>>を調べてみると有益かもしれません。
どんな決定不可能な定理が関係してくるかはプロジェクトによって異なり、それに応じて有効なヒューリスティクスも変わってくるので、著者は新しいプロジェクトごとに新しいタクティクライブラリを実装しています。皆さんにもそれを勧めます。

(* ** Installation and Emacs Set-Up *)
** インストールとEmacsの設定

(*At the start of the next chapter, I assume that you have installed Coq and Proof General.  The code in this book is tested with Coq versions 8.4pl6, 8.5pl3, and 8.6.  Though parts may work with other versions, it is expected that the book source will fail to build with _earlier_ versions.

%\index{Proof General|(}%To set up your Proof General environment to process the source to the next chapter, a few simple steps are required.

%\begin{enumerate}%#<ol>#

%\item %#<li>#Get the book source from
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote></li>#

%\item %#<li>#Unpack the tarball to some directory <<DIR>>.#</li>#

%\item %#<li>#Run <<make>> in <<DIR>> (ideally with a <<-j>> flag to use multiple processor cores, if you have them).#</li>#

%\item %#<li>#There are some minor headaches associated with getting Proof General to pass the proper command line arguments to the <<coqtop>> program, which provides the interactive Coq toplevel.  One way to add settings that will be shared by many source files is to add a custom variable setting to your %\index{.emacs file@\texttt{.emacs} file}%<<.emacs>> file, like this:
<<
(custom-set-variables
  ...
  '(coq-prog-args '("-R" "DIR/src" "Cpdt"))
  ...
)
>>
The extra arguments demonstrated here are the proper choices for working with the code for this book.  The ellipses stand for other Emacs customization settings you may already have.  It can be helpful to save several alternate sets of flags in your <<.emacs>> file, with all but one commented out within the <<custom-set-variables>> block at any given time.

Alternatively, Proof General configuration can be set on a per-directory basis, using a %\index{.dir-locals.el file@\texttt{.dir-locals.el} file}%<<.dir-locals.el>> file in the directory of the source files for which you want the settings to apply.  Here is an example that could be written in such a file to enable use of the book source.  Note the need to include an argument that starts Coq in Emacs support mode.
<<
((coq-mode . ((coq-prog-args . ("-emacs-U" "-R" "DIR/src" "Cpdt")))))
>>
 #</li>#

#</ol>#%\end{enumerate}%

Every chapter of this book is generated from a commented Coq source file.  You can load these files and run through them step-by-step in Proof General.  Be sure to run the Coq binary <<coqtop>> with the command-line argument <<-R DIR/src Cpdt>>.  If you have installed Proof General properly, the Coq mode should start automatically when you visit a <<.v>> buffer in Emacs, and the above advice on <<.emacs>> settings should ensure that the proper arguments are passed to <<coqtop>> by Emacs.

With Proof General, the portion of a buffer that Coq has processed is highlighted in some way, like being given a blue background.  You step through Coq source files by positioning the point at the position you want Coq to run to and pressing C-C C-RET.  This can be used both for normal step-by-step coding, by placing the point inside some command past the end of the highlighted region; and for undoing, by placing the point inside the highlighted region.
%\index{Proof General|)}% *)

次章ではCoqとProof Generalがインストールされているものとして説明を始めます。
本書のコードは、Coqのバージョン8.4pl6、8.5pl3、8.6でテスト済みです。
他のバージョンで動く部分もあると思いますが、これら_[以前]_のバージョンだと、本書のソースのビルドには失敗するでしょう。

次章でソースを処理できるようにProof Generalを設定するには、いくつか簡単な段階を踏む必要があります。%\index{Proof General|(}%

%\begin{enumerate}%#<ol>#

%\item %#<li>#以下からソースを取得
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote></li>#

%\item %#<li>#tarballをディレクトリ<<DIR>>に展開#</li>#

%\item %#<li>#<<DIR>>内で<<make>>を実行（マルチコアのマシンでは<<-j>>フラグを指定してください）#</li>#

%\item %#<li>#Coqの対話的な仕組みのトップレベルを提供する<<coqtop>>というプログラムがあり、そのコマンドライン引数をProof Generalに渡すのですが、これには本質的でない部分で少し面倒があります。複数のソースファイルで同じ設定を共有する方法としては、以下のように独自の変数を<<.emacs>>ファイルに追加設定する方法があります%\index{.emacs file@\texttt{.emacs} file}%。
<<
(custom-set-variables
  ...
  '(coq-prog-args '("-R" "DIR/src" "Cpdt"))
  ...
)
>>
上記に提示しているのは、本書のコードを動かすための設定です。
省略した部分には、Emacsの他のカスタマイズのために設定されている変数があれば、それが入ります。<<.emacs>>ファイルの<<custom-set-variables>>ブロックには複数の設定を書いて保存しておき、適宜必要なもの以外をコメントアウトして使うとよいでしょう。

Proof Generalの設定をディレクトリごとに指定することも可能です。
それには、設定を適用したいソースファイルのディレクトリ内に<<.dir-locals.el>>ファイルを配置します%\index{.dir-locals.el file@\texttt{.dir-locals.el} file}%。
本書のソース向けの設定ファイルの例を以下に示します。
EmacsサポートモードでCoqを開始するための引数を含める必要がある点に注意してください。
<<
((coq-mode . ((coq-prog-args . ("-emacs-U" "-R" "DIR/src" "Cpdt")))))
>>
 #</li>#

#</ol>#%\end{enumerate}%

本書の各章はコメント付きのCoqソースファイルから生成されています。
Proof Generalでそれらをロードして1ステップずつ実行できます。
Coqのバイナリ<<coqtop>>は、必ずコマンドライン引数<<-R DIR/src Cpdt>>を指定して実行してください。
Proof Generalが適切にインストールされていれば、Emacs内で<<.v>>バッファに入ったときに自動でCoqモードが立ち上がるはずです。
そして、上記のように<<.emacs>>を設定してあれば、適切な引数がEmacsから<<coqtop>>に渡されるでしょう。

Proof Generalでは、バッファのうちCoqが実行した部分の背景がハイライトされ、青色などで表示されます。
実行したい場所にカーソルを置いて<<C-C C-RET>>を押すと、その位置までCoqのソースファイルをステップごとに実行できます。
<<C-C C-RET>>は、ハイライト済みの領域より後ろにカーソルを置いてステップごとに実行するときだけでなく、ハイライトされた領域内にカーソルを置くことで、そこまで実行を巻き戻すときにも使えます。

%\index{Proof General|)}% *)

(** (*%\section{Chapter Source Files}*)
%\section{各章のソースファイル}
\begin{center} \begin{tabular}{|r|l|}
\hline
\textbf{Chapter} & \textbf{Source} \\
\hline
Some Quick Examples & \texttt{StackMachine.v} \\
\hline
Introducing Inductive Types & \texttt{InductiveTypes.v} \\
\hline
Inductive Predicates & \texttt{Predicates.v} \\
\hline
Infinite Data and Proofs & \texttt{Coinductive.v} \\
\hline
Subset Types and Variations & \texttt{Subset.v} \\
\hline
General Recursion & \texttt{GeneralRec.v} \\
\hline
More Dependent Types & \texttt{MoreDep.v} \\
\hline
Dependent Data Structures & \texttt{DataStruct.v} \\
\hline
Reasoning About Equality Proofs & \texttt{Equality.v} \\
\hline
Generic Programming & \texttt{Generic.v} \\
\hline
Universes and Axioms & \texttt{Universes.v} \\
\hline
Proof Search by Logic Programming & \texttt{LogicProg.v} \\
\hline
Proof Search in Ltac & \texttt{Match.v} \\
\hline
Proof by Reflection & \texttt{Reflection.v} \\
\hline
Proving in the Large & \texttt{Large.v} \\
\hline
A Taste of Reasoning About Programming Language Syntax & \texttt{ProgLang.v} \\
\hline
\end{tabular} \end{center}
%*)
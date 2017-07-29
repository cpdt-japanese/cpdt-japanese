(* Copyright (c) 2008-2013, 2015, 2017, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\chapter{Introduction}% *)


(** * Whence This Book? *)

(**

(*We would all like to have programs check that our programs are correct.  Due in no small part to some bold but unfulfilled promises in the history of computer science, today most people who write software, practitioners and academics alike, assume that the costs of formal program verification outweigh the benefits.  The purpose of this book is to convince you that the technology of program verification is mature enough today that it makes sense to use it in a support role in many kinds of research projects in computer science.  Beyond the convincing, I also want to provide a handbook on practical engineering of certified programs with the Coq proof assistant.  Almost every subject covered is also relevant to interactive computer theorem-proving in general, such as for traditional mathematical theorems.  In fact, I hope to demonstrate how verified programs are useful as building blocks in all sorts of formalizations.*)
書いた(*our*)プログラムが正しいことを検査してくれるプログラムが欲しいものです. 
今日ソフトウェアを書く人々のほとんどが, 
実践者であるか学者かにかかわらず, 
形式的プログラム検証のコストが利益を
上まわってしまう(*outweigh*)ときめつけて(*assume*)います.
計算機科学の歴史においてかつて語られ, そして失敗した,
いくつかの強気な展望(*bold promises*)が, このきめつけの少なからぬ原因となっています. 
本書の目的は, 
プログラム検証の技術が十分成熟したものであり,
計算機科学の各種研究プロジェクトの補助として用いる意味があるということを,
あなたに納得してもらうことです. 
また, 納得を与えるにとどまらず, 認証されたプログラム(*certified program*)を実用的にエンジニアリングするための手引き書を提供することも私の望みです. 
(* ノート(才川): すぐ後でcertified, certification, certificate, provingなどが
   微妙に違う意味で用いられるので, certifyの訳語を認証するとして統一的に訳してみた. 
   これは20161129時点での訳語集と反する（certifiedを証明付きと訳すことになっている）
   のでいずれ調整が必要になる. *)
本書のあつかう主題のほとんどは, 伝統的な数学の定理の扱いなどを含む, 計算機による対話的な定理証明一般と関係のあるものです. 
実際に私は, 検証されたプログラムが, 
あらゆる種類の形式化における構成要素として役にたつのだということを, 
実証してみせたいと考えています. 

(*Research into mechanized theorem proving began in the second half of the 20th century, and some of the earliest practical work involved Nqthm%~\cite{Nqthm}\index{Nqthm}%, the "Boyer-Moore Theorem Prover," which was used to prove such theorems as correctness of a complete hardware and software stack%~\cite{Piton}%.  ACL2%~\cite{CAR}\index{ACL2}%, Nqthm's successor, has seen significant industry adoption, for instance, by AMD to verify correctness of floating-point division units%~\cite{AMD}%.*)
機械化された(*mechanized*)定理証明の研究は20世紀後半に始まりました. 
最初期の実用的な成果(*work*)の一つに, 「Boyer-Moore定理証明器」Nqthm%~\cite{Nqthm}\index{Nqthm}%があります. 
これはハードウェアとソフトウェア両方の層(*stack*)にわたる正しさを定理として証明する目的などに用いられました%~\cite{Piton}%. 
Nqthmの後継であるACL2%~\cite{CAR}\index{ACL2}%は産業界で顕著に受けいれられ,  
例えばAMDによって浮動小数除算の正しさを保証するために用いられました%~\cite{AMD}%. 

(*Around the beginning of the 21st century, the pace of progress in practical applications of interactive theorem proving accelerated significantly.  Several well-known formal developments have been carried out in Coq, the system that this book deals with.  In the realm of pure mathematics, Georges Gonthier built a machine-checked proof of the four-color theorem%~\cite{4C}%, a mathematical problem first posed more than a hundred years before, where the only previous proofs had required trusting ad-hoc software to do brute-force checking of key facts.  In the realm of program verification, Xavier Leroy led the CompCert project to produce a verified C compiler back-end%~\cite{CompCert}% robust enough to use with real embedded software.*)
21世紀初頭に対話的定理証明の実用的用法は著しく加速しつつ発展しました. 
幾つかのよく知られた形式的開発が, 本書の扱うシステムであるCoqを用いて行われました. 
純粋数学の領域(*realm*)においては, Georges Gonthierが
四色定理の機械的に検査された(*machine-checked*)証明を構築しました%~\cite{4C}%. 
四色定理は百年以上前に提示された数学の問題で,
これまでに得られていた証明は,
鍵となる事実を総当たりで確かめるための
場当たり的なソフトウェアを信用しなければならないものでした. 
プログラム検証(*program verification*)の領域においては, 
Xavier LeroyがCompCertプロジェクトを主導し, 
本物の組み込みソフトウェアで使うのに十分な堅牢さを持つ, 
検証された(*verified*)Cコンパイラバックエンドを
作り上げ(*produce*)ました%~\cite{CompCert}%. 

(*Many other recent projects have attracted attention by proving important theorems using computer proof assistant software.  For instance, the L4.verified project%~\cite{seL4}% led by Gerwin Klein has given a mechanized proof of correctness for a realistic microkernel, using the Isabelle/HOL proof assistant%~\cite{Isabelle/HOL}\index{Isabelle/HOL}%.  The amount of ongoing work in the area is so large that I cannot hope to list all the recent successes, so from this point I will assume that the reader is convinced both that we ought to want machine-checked proofs and that they seem to be feasible to produce.  (To readers not yet convinced, I suggest a Web search for "machine-checked proof"!)*)
他にも近頃多くのプロジェクトが, 計算機による証明支援系ソフトウェアを用いて
重要な定理の証明を行い, 注目を集めています. 
例えばGerwin Kleinが主導するL4.verifiedプロジェクト%~\cite{seL4}%は, 
現実的なマイクロカーネルの正しさを,
証明支援系Isabelle/HOL%~\cite{Isabelle/HOL}\index{Isabelle/HOL}%を用いて
機械的に証明しました. 
この分野における進行中の事業は数多くあり,
最近の成功例を全てを挙げることはほぼ不可能です. 
従ってこれ以降, 機械的に検査された証明を追求すべきであることと, 
それを作り出すことがどうやら可能であるということについて,
読者は納得したという仮定をすることにしたいと思います. 
(まだ納得していない読者には, "machine-checked proof"でWebを検索することをお勧めします.)

(*The idea of %\index{certified program}% _certified program_ features prominently in this book's title.  Here the word "certified" does _not_ refer to governmental rules for how the reliability of engineered systems may be demonstrated to sufficiently high standards.  Rather, this concept of certification, a standard one in the programming languages and formal methods communities, has to do with the idea of a _certificate_, or formal mathematical artifact proving that a program meets its specification.  Government certification procedures rarely provide strong mathematical guarantees, while certified programming provides guarantees about as strong as anything we could hope for.  We trust the definition of a foundational mathematical logic, we trust an implementation of that logic, and we trust that we have encoded our informal intent properly in formal specifications, but few other opportunities remain to certify incorrect software.  For compilers and other programs that run in batch mode, the notion of a %\index{certifying program}% _certifying_ program is also common, where each run of the program outputs both an answer and a proof that the answer is correct.  Any certifying program can be composed with a proof checker to produce a certified program, and this book focuses on the certified case, while also introducing principles and techniques of general interest for stating and proving theorems in Coq.*)
本書のタイトルでは%\index{認証されたプログラム(certified program)}%＿認証されたプログラム＿という考えがはっきりと打ち出されています.
「認証された」という語が意味するものは政府の規則＿ではありません＿. 
つまり作り上げられた(*engineered*)システムの信頼性が十分厳しい規格に従うことを, 
どのように実証する(*demonstrate*)か定めた規則のことを言うのではありません. 
そうではなく, この認証(*certification*)という概念は,
プログラミング言語や形式手法のコミュニティでは標準的に, 
＿認証書＿(*certificate*)の考えと関連づけられます.
認証書とは, 言いかえると形式的で数学的な産物であり,
プログラムが仕様に合っていることを証明するものです. 
(* ノート(才川): certified, certification, certificate, proveなどの
   訳語調整しないと何言ってるのかわかりにくくなっている.
   あるいは思いきった意訳が必要かも. *)
政府の認証手続きが強い数学的な保証を与えることはほとんどありませんが,  
認証されたプログラムを書くことは,
われわれの望むような保証をほとんどいくらでも強く与えてくれます. 
基礎的な数理論理学を信頼し, その論理の実装のどれかを信頼し,
そしてわれわれが非形式的な意図を正しく形式的仕様にエンコードできたことを信頼するならば, 
正しくないソフトウェアを認証してしまう可能性は他にほとんど残りません. 
コンパイラや他のバッチ処理として走るプログラムについては,
%\index{認証を伴うプログラム(certifying program)}%＿認証を伴う＿プログラムという
概念
(* ノート(才川): concept, notionを訳しわけるかどうか. とりあえずどちらも概念にした *)
もよく知られており, これは実行すると, 回答と共に回答が正しいことの証明を出力します. 
認証を伴うプログラムを証明検査器と組み合わせることで認証されたプログラムが得られますが, 
本書では認証されたプログラムの方に焦点をあてることにします. 
同時に, Coqで定理を述べて証明するための, 一般的興味を惹くような原理や技術も紹介します. 

%\medskip%

(*There are a good number of (though definitely not "many") tools that are in wide use today for building machine-checked mathematical proofs and machine-certified programs.  The following is my attempt at an exhaustive list of interactive "proof assistants" satisfying a few criteria.  First, the authors of each tool must intend for it to be put to use for software-related applications.  Second, there must have been enough engineering effort put into the tool that someone not doing research on the tool itself would feel his time was well spent using it.  A third criterion is more of an empirical validation of the second: the tool must have a significant user community outside of its own development team.*)
今日では, 機械的に確かめられた数学の証明や機械的に認証されたプログラムを構築するために, 
広く利用されているツールがいくつも（決して「沢山」というわけではありませんが）存在します. 
いくつかの条件を満たす対話的な「証明支援系」を, 以下に列挙し尽くしてみようと思います. 
条件の一つめとして, 作者がツールの用途として,
ソフトウェアに関連した応用を意図していなければなりません. 
二つめとして, ツール自体の研究者以外の利用者が有意義に利用できるよう,
十分な工学的努力(*engineering effort*)がなされていなければなりません. 
三つめの条件は二つめをより経験的に(*empirical, 具体的にのほうがよいか*)保証するものです. 
すなわち, ツールの開発チーム以外のユーザコミュニティが
ちゃんと存在していなければなりません. 

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
#

(*Isabelle/HOL, implemented with the "proof assistant development framework" Isabelle%~\cite{Isabelle}%, is the most popular proof assistant for the HOL logic.  The other implementations of HOL can be considered equivalent for purposes of the discussion here.*)
Isabelle/HOLは「証明支援系開発のフレームワーク」である
Isabelle%~\cite{Isabelle}%を用いて実装されており,
論理体系HOLのための証明支援系で最もよく利用されるものです. 
ここで議論した目的のためには, HOLの他の実装も同様に利用できます. 
(* ノート：「利用できる」はfor purposesに呼応させての意訳 *)

*)


(** * Why Coq? *)

(**
(**
This book is going to be about certified programming using Coq, and I am convinced that it is the best tool for the job.  Coq has a number of very attractive properties, which I will summarize here, mentioning which of the other candidate tools lack which properties.
*)
この本はCoqを使った認証を伴うプログラミングについての本になる予定です．
私はそれ（Coq）がこの仕事（certified programming）に最良のツールだと確信しています．
Coqにはとても魅力的な性質が多く備わっていますので，ここ（以下）でまとめます．
同時に他の候補となるツールがどの性質を欠いているかも説明します．
*)


(**
(** ** Based on a Higher-Order Functional Programming Language *)
*)
(** ** 高階の関数型プログラミング言語に基づいている *)

(**
(**
%\index{higher-order vs. first-order languages}%There is no reason to give up the familiar comforts of functional programming when you start writing certified programs.  All of the tools I listed are based on functional programming languages, which means you can use them without their proof-related features to write and run regular programs.

%\index{ACL2}%ACL2 is notable in this field for having only a _first-order_ language at its foundation.  That is, you cannot work with functions over functions and all those other treats of functional programming.  By giving up this facility, ACL2 can make broader assumptions about how well its proof automation will work, but we can generally recover the same advantages in other proof assistants when we happen to be programming in first-order fragments.
*)
認証を伴うプログラムを書くとき，関数型プログラミング言語のよく知られた便利さをあきらめる理由はありません．ここで挙げるツールは関数型プログラミング言語を基礎としているため，証明に関係する機能を使わなくても普通のプログラムを書いたり実行したりできます．
＿1階の＿言語のみを基礎とするという点点でACL2は重要です．
つまり，(1階の言語のツールでは)関数上の関数などの関数型プログラミングの便利な機能が使えないのです．
この便利さの代わりに，自動証明がいかにうまく動くかについてより多様な仮定がACL2ではできるのですが，他の証明支援系でも1階のプログラムを書くときは同様の利点を回復できます．
*)


(**
(** ** Dependent Types *)
*)
(** ** 依存型 *)

(**
(**
A language with _dependent types_ may include references to programs inside of types.  For instance, the type of an array might include a program expression giving the size of the array, making it possible to verify absence of out-of-bounds accesses statically.  Dependent types can go even further than this, effectively capturing any correctness property in a type.  For instance, later in this book, we will see how to give a compiler a type that guarantees that it maps well-typed source programs to well-typed target programs.

%\index{ACL2}%ACL2 and %\index{HOL}%HOL lack dependent types outright.  Each of %\index{PVS}%PVS and %\index{Twelf}%Twelf supports a different strict subset of Coq's dependent type language.  Twelf's type language is restricted to a bare-bones, monomorphic lambda calculus, which places serious restrictions on how complicated _computations inside types_ can be.  This restriction is important for the soundness argument behind Twelf's approach to representing and checking proofs.

In contrast, %\index{PVS}%PVS's dependent types are much more general, but they are squeezed inside the single mechanism of _subset types_, where a normal type is refined by attaching a predicate over its elements.  Each member of the subset type is an element of the base type that satisfies the predicate.  Chapter 6 of this book introduces that style of programming in Coq, while the remaining chapters of Part II deal with features of dependent typing in Coq that go beyond what PVS supports.

Dependent types are useful not only because they help you express correctness properties in types.  Dependent types also often let you write certified programs _without writing anything that looks like a proof_.  Even with subset types, which for many contexts can be used to express any relevant property with enough acrobatics, the human driving the proof assistant usually has to build some proofs explicitly.  Writing formal proofs is hard, so we want to avoid it as far as possible.  Dependent types are invaluable for this purpose.

*)
＿依存型＿を持つ言語は型の内部への言及を含むことができます．
例えば，配列をあらわす型にはその配列のサイズを与えるプログラム式を含むことができるので，配列の範囲外アクセスがないことを静的に確かめることができるようになります．
型の正しさを表す性質を効果的に捉えることで，依存型はさらに先まで行けます．
例えば，この本で後ほど，正しく型付けされたソースプログラムから正しく型付けされたターゲットプログラムに変換することを保証する型をコンパイラに与える方法を見ます．

公然のことですが，%\index{ACL2}%ACL2と%\index{HOL}%HOLでは依存型は使えません．
%\index{PVS}%PVSと%\index{Twelf}%TwelfはCoqの依存型言語のそれぞれ別の真部分集合をサポートします．
Twelfの型言語はbare-bonesに制限されています．つまり単相ラムダ計算です．
そのため型の内部での計算に重大な制約が置かれます．
この制約はTwelfが証明を表現したり証明したりするアプローチの健全性を議論するときに重要です．

それに対して%\index{PVS}%PVSの依存型はより一般的ですが，subset typeという単一の仕組みに制限されています．
つまり，通常の型は述語を付加することで定義されます．
subset typeの要素の1つ1つはbase typeの要素のうちその述語を満たすものです．
この本の6章ではこの様式のプログラミングをCoqでする方法を紹介します．
一方Part IIの他の章ではCoqによる依存型を扱い，PVSがサポートする範囲外です．

依存型が有用なのは，型の正しさを表現するのを助けるからだけではありません．
依存型のおかげで，しばしば証明らしいものを書かずにcertified programを書くことができるようになるんです．
subset typeだけだと，離れ業を十分駆使すれば妥当な性質を表現できるのですが，人間が操作するような証明支援機は通常，証明を明示的に構築する必要があります．
形式的な証明を書くのは大変なので，なるべく避けたいものです．
この目的のために，依存型には計り知れない価値があります．
*)

(**
(** ** An Easy-to-Check Kernel Proof Language *)
*)
(** ** 確認しやすいカーネル証明言語 *)

(**
(**
%\index{de Bruijn criterion}%Scores of automated decision procedures are useful in practical theorem proving, but it is unfortunate to have to trust in the correct implementation of each procedure.  Proof assistants satisfy the "de Bruijn criterion" when they produce _proof terms_ in small kernel languages, even when they use complicated and extensible procedures to seek out proofs in the first place.  These core languages have feature complexity on par with what you find in proposals for formal foundations for mathematics (e.g., ZF set theory).  To believe a proof, we can ignore the possibility of bugs during _search_ and just rely on a (relatively small) proof-checking kernel that we apply to the _result_ of the search.

Coq meets the de Bruijn criterion, while %\index{ACL2}%ACL2 does not, as it employs fancy decision procedures that produce no "evidence trails" justifying their results.  %\index{PVS}%PVS supports _strategies_ that implement fancier proof procedures in terms of a set of primitive proof steps, where the primitive steps are less primitive than in Coq.  For instance, a propositional tautology solver is included as a primitive, so it is a question of taste whether such a system meets the de Bruijn criterion.  The HOL implementations meet the de Bruijn criterion more manifestly; for Twelf, the situation is murkier.
*)

%\index{de Bruijn criterion}%自動化された決定手続きが判定してくれるというのは実践的な定理証明では有用です．
しかし，一つずつの手続きが正しく実装されているということを信頼しないと行けないのは残念です．
複雑で拡張可能な手順を使って証明を探し出すのが先かどうかに関わらず，証明支援機が核となる小さな言語で表現された_証明項_を生成するとき，
その証明支援機はde Bruijn criterionを満たすと言います．
数学の形式的な基礎の提案の中で見られるのと同様の複雑さをこのようなコア言語も持っています．
証明を_探す_際のバグの可能性は無視してもよく，証明を検証するのに必要な小さな部分だけだけによって，証明を信じることができます．

Coqはde Bruijn criterionを満たします．一方%\index{ACL2}%ACL2は満たしません．
というのは，ACL2は手の込んだ決定手続きを採用し，ACL2の結果を正当化する証跡を生成しないからです．
%\index{PVS}%PVSは_戦略_をサポートします．戦略では手の込んだ証明手順を「原始的な」証明の段階で実装します．
ここで「原始的な」といってもCoqほど原始的ではないです．
例えば，命題論理の恒真式ソルバはPVSでは原始的とされるため，そういうものがde Bruijn criterionを満たすかどうかという好みの問題になります．
HOLの実装がde Bruijn criterionに適合するのはより明らかです．Twelfに対してはより不明瞭です．
*)

(**
(** ** Convenient Programmable Proof Automation *)
*)

(** ** 便利でプログラム可能な証明自動化 *)

(**
(**
A commitment to a kernel proof language opens up wide possibilities for user extension of proof automation systems, without allowing user mistakes to trick the overall system into accepting invalid proofs.  Almost any interesting verification problem is undecidable, so it is important to help users build their own procedures for solving the restricted problems that they encounter in particular theorems.

%\index{Twelf}%Twelf features no proof automation marked as a bona fide part of the latest release; there is some automation code included for testing purposes.  The Twelf style is based on writing out all proofs in full detail.  Because Twelf is specialized to the domain of syntactic metatheory proofs about programming languages and logics, it is feasible to use it to write those kinds of proofs manually.  Outside that domain, the lack of automation can be a serious obstacle to productivity.  Most kinds of program verification fall outside Twelf's forte.

Of the remaining tools, all can support user extension with new decision procedures by hacking directly in the tool's implementation language (such as OCaml for Coq).  Since %\index{ACL2}%ACL2 and %\index{PVS}%PVS do not satisfy the de Bruijn criterion, overall correctness is at the mercy of the authors of new procedures.

%\index{Isabelle/HOL}%Isabelle/HOL and Coq both support coding new proof manipulations in ML in ways that cannot lead to the acceptance of invalid proofs.  Additionally, Coq includes a domain-specific language for coding decision procedures in normal Coq source code, with no need to break out into ML.  This language is called %\index{Ltac}%Ltac, and I think of it as the unsung hero of the proof assistant world.  Not only does Ltac prevent you from making fatal mistakes, it also includes a number of novel programming constructs which combine to make a "proof by decision procedure" style very pleasant.  We will meet these features in the chapters to come.
*)

残りのツールについては，全て，新しい決定手続きのユーザー拡張をサポートします．
それは，直接ツールの実装（Coqの場合はOCamlです）をハックする形になります．
ACL2とPVSはde Bruijn条件を満たさないため，全体の正しさは新しい手順を作った人に左右されてしまいます．

ISabelle/HOLとCoqはどちらもあらあな証明操作をMLでコードすることをサポートします．
それによって不正な証明が受け入れられることはありません．
加えて，Coqはドメイン特化言語をもっていて決定手続きを通常のCoqソースコードの中でコーディングすることができます．
MLに抜け出す必要はありません．
この言語（DSL）はLtacと呼ばれていて，私が思うに，Ltacは証明支援系の世界における無名の英雄です．
Ltacは深刻な間違い犯すことを防ぐだけではありません．多くの画期的なプログラム構成要素を持っていて，それを組み合わせることで「決定手続きによる証明」というスタイルをとても快適にしてくれます．
私たちはこれらの機能を後の章で見て行きます．
*)

(**
(** ** Proof by Reflection *)
*)

(** ** リフレクションによる証明 *)

(**
(**
%\index{reflection}\index{proof by reflection}%A surprising wealth of benefits follows from choosing a proof language that integrates a rich notion of computation.  Coq includes programs and proof terms in the same syntactic class.  This makes it easy to write programs that compute proofs.  With rich enough dependent types, such programs are _certified decision procedures_.  In such cases, these certified procedures can be put to good use _without ever running them_!  Their types guarantee that, if we did bother to run them, we would receive proper "ground" proofs.

The critical ingredient for this technique, many of whose instances are referred to as _proof by reflection_, is a way of inducing non-trivial computation inside of logical propositions during proof checking.  Further, most of these instances require dependent types to make it possible to state the appropriate theorems.  Of the proof assistants I listed, only Coq really provides support for the type-level computation style of reflection, though PVS supports very similar functionality via refinement types.
*)
*)

(**
計算についての概念を豊富に統合した証明言語を選ぶことで驚くほど多くの利点が得られます．
Coqはプログラムと証明項を同じ構文クラスで表現します（？）
これによって証明を計算するプログラムを作るのが簡単になります．
十分豊富な依存型があることで，そのようなプログラムは＿認証を伴う決定手続き＿になります．
そのような場合，それらの認証を伴う手続きは走らせないとしても有用なのです．
もしそのプログラムをわざわざ実行した場合，適切な十分な根拠のある証明が得られる，ということをそれらの型が保証してくれます．

このテクニックは多くは＿リフレクションによる証明＿と呼ばれます．
証明検査の際，論理的な命題の中に非自明な計算を取り入れるというものです．
さらに，このようなもののほとんどの例では適切な定理を表現するために依存型を必要とします．
先ほどより挙げている証明支援機の中では，Coqだけが型レベルでの計算をするというスタイルのリフレクションを提供しています．
一方PVSではとても似た機能をrefinement typeを使ってサポートしています．

*)

(**
(** * Why Not a Different Dependently Typed Language? *)
*)
(** * 他の依存型の言語じゃない理由 *)

(**
The logic and programming language behind Coq belongs to a type-theory ecosystem with a good number of other thriving members.  %\index{Agda}%{{http://appserv.cs.chalmers.se/users/ulfn/wiki/agda.php}Agda} and %\index{Epigram}%{{https://code.google.com/p/epigram/}Epigram} are the most developed tools among the alternatives to Coq, and there are others that are earlier in their lifecycles.  All of the languages in this family feel sort of like different historical offshoots of Latin.  The hardest conceptual epiphanies are, for the most part, portable among all the languages.  Given this, why choose Coq for certified programming?

I think the answer is simple.  None of the competition has well-developed systems for tactic-based theorem proving.  Agda and Epigram are designed and marketed more as programming languages than proof assistants.  Dependent types are great, because they often help you prove deep theorems without doing anything that feels like proving.  Nonetheless, almost any interesting certified programming project will benefit from some activity that deserves to be called proving, and many interesting projects absolutely require semi-automated proving, to protect the sanity of the programmer.  Informally, proving is unavoidable when any correctness proof for a program has a structure that does not mirror the structure of the program itself.  An example is a compiler correctness proof, which probably proceeds by induction on program execution traces, which have no simple relationship with the structure of the compiler or the structure of the programs it compiles.  In building such proofs, a mature system for scripted proof automation is invaluable.

On the other hand, Agda, Epigram, and similar tools have less implementation baggage associated with them, and so they tend to be the default first homes of innovations in practical type theory.  Some significant kinds of dependently typed programs are much easier to write in Agda and Epigram than in Coq.  The former tools may very well be superior choices for projects that do not involve any "proving."  Anecdotally, I have gotten the impression that manual proving is orders of magnitudes more costly than manual coping with Coq's lack of programming bells and whistles.  In this book, I will devote significant space to patterns for programming with dependent types in Coq as it is today.  We can hope that the type theory community is tending towards convergence on the right set of features for practical programming with dependent types, and that we will eventually have a single tool embodying those features.
*)


(**
(** * Engineering with a Proof Assistant *)
*)
(** * 証明支援器を使ったエンジニアリング *)

(**
In comparisons with its competitors, Coq is often derided for promoting unreadable proofs.  It is very easy to write proof scripts that manipulate proof goals imperatively, with no structure to aid readers.  Such developments are nightmares to maintain, and they certainly do not manage to convey "why the theorem is true" to anyone but the original author.  One additional (and not insignificant) purpose of this book is to show why it is unfair and unproductive to dismiss Coq based on the existence of such developments.

I will go out on a limb and guess that the reader is a fan of some programming language and may even have been involved in teaching that language to undergraduates.  I want to propose an analogy between two attitudes: coming to a negative conclusion about Coq after reading common Coq developments in the wild, and coming to a negative conclusion about Your Favorite Language after looking at the programs undergraduates write in it in the first week of class.  The pragmatics of mechanized proving and program verification have been under serious study for much less time than the pragmatics of programming have been.  The computer theorem proving community is still developing the key insights that correspond to those that programming texts and instructors impart to their students, to help those students get over that critical hump where using the language stops being more trouble than it is worth.  Most of the insights for Coq are barely even disseminated among the experts, let alone set down in a tutorial form.  I hope to use this book to go a long way towards remedying that.

If I do that job well, then this book should be of interest even to people who have participated in classes or tutorials specifically about Coq.  The book should even be useful to people who have been using Coq for years but who are mystified when their Coq developments prove impenetrable by colleagues.  The crucial angle in this book is that there are "design patterns" for reliably avoiding the really grungy parts of theorem proving, and consistent use of these patterns can get you over the hump to the point where it is worth your while to use Coq to prove your theorems and certify your programs, even if formal verification is not your main concern in a project.  We will follow this theme by pursuing two main methods for replacing manual proofs with more understandable artifacts: dependently typed functions and custom Ltac decision procedures.
*)


(**
(** * Prerequisites *)
*)
(** * 前提知識 *)

(**
(**
I try to keep the required background knowledge to a minimum in this book.  I will assume familiarity with the material from usual discrete math and logic courses taken by undergraduate computer science majors, and I will assume that readers have significant experience programming in one of the ML dialects, in Haskell, or in some other, closely related language.  Experience with only dynamically typed functional languages might lead to befuddlement in some places, but a reader who has come to understand Scheme deeply will probably be fine.

My background is in programming languages, formal semantics, and program verification.  I sometimes use examples from that domain.  As a reference on these topics, I recommend _Types and Programming Languages_ %\cite{TAPL}%, by Benjamin C. Pierce; however, I have tried to choose examples so that they may be understood without background in semantics.
*)
*)
(**
私はこの本を読む上で必要な背景知識を最小限に抑えようとしています。
私は、情報科学専攻の学部生が習う通常の離散数学と論理学を理解していること、そしてMLの方言かHaskellかその他の関連言語についてのプログラミング経験があることを仮定します。
動的型付きの関数型言語の経験だけでは理解出来なくて困る部分もあるかもしれません。Schemeについての深い理解があればおそらく大丈夫です。

私のバックグラウンドはプログラミング言語、形式意味論、そしてプログラム検証です。
それらの分野からの例を使うことがあります。
参考文献として _Type and Programming Languages_ %\cite{TAPL}% (訳注:和訳は「型システム入門 オーム社」)をお勧めします。しかし、なるべく意味論の背景なしに理解できるように例を選んでいます。
*)


(** * Using This Book *)

(**
(**
This book is generated automatically from Coq source files using the wonderful coqdoc program.  The latest PDF version, with hyperlinks from identifier uses to the corresponding definitions, is available at:
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.pdf}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.pdf">http://adam.chlipala.net/cpdt/cpdt.pdf</a></tt></blockquote>#
There is also an online HTML version available, which of course also provides hyperlinks:
%\begin{center}\url{http://adam.chlipala.net/cpdt/html/toc.html}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/html/toc.html">http://adam.chlipala.net/cpdt/html/toc.html</a></tt></blockquote>#
The source code to the book is also freely available at:
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote>#

There, you can find all of the code appearing in this book, with prose interspersed in comments, in exactly the order that you find in this document.  You can step through the code interactively with your chosen graphical Coq interface.  The code also has special comments indicating which parts of the chapters make suitable starting points for interactive class sessions, where the class works together to construct the programs and proofs.  The included Makefile has a target <<templates>> for building a fresh set of class template files automatically from the book source.

A traditional printed version of the book is slated to appear from MIT Press in the future.  The online versions will remain available at no cost even after the printed book is released, and I intend to keep the source code up-to-date with bug fixes and compatibility changes to track new Coq releases.

%\index{graphical interfaces to Coq}%I believe that a good graphical interface to Coq is crucial for using it productively.  I use the %\index{Proof General}%{{http://proofgeneral.inf.ed.ac.uk/}Proof General} mode for Emacs, which supports a number of other proof assistants besides Coq.  There is also the standalone %\index{CoqIDE}%CoqIDE program developed by the Coq team.  I like being able to combine certified programming and proving with other kinds of work inside the same full-featured editor.  In the initial part of this book, I will reference Proof General procedures explicitly, in introducing how to use Coq, but most of the book will be interface-agnostic, so feel free to use CoqIDE if you prefer it.  The one issue with CoqIDE before version 8.4, regarding running through the book source, is that I will sometimes begin a proof attempt but cancel it with the Coq [Abort] or #<span class="inlinecode"><span class="id" type="keyword">#%\coqdockw{%Restart%}%#</span></span># commands, which CoqIDE did not support until recently.  It would be bad form to leave such commands lying around in a real, finished development, but I find these commands helpful in writing single source files that trace a user's thought process in designing a proof.
*)
*)
(**
本書はcoqdocというプログラムを使ってCoqのソースファイルから自動的に生成されています。識別子から対応する定義にハイパーリンクの貼られたPDFバージョンは以下で利用できます：
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.pdf}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.pdf">http://adam.chlipala.net/cpdt/cpdt.pdf</a></tt></blockquote>#
オンラインのHTMLバージョンも利用できます。もちろんこちらでもハイパーリンクが付いています：
%\begin{center}\url{http://adam.chlipala.net/cpdt/html/toc.html}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/html/toc.html">http://adam.chlipala.net/cpdt/html/toc.html</a></tt></blockquote>#
本書のソースファイルも無料で利用できます：
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote>#

ソースファイルでは本書に載っているすべてのコードがあり、コメントの中に本書と同じ順番で説明がつけられています。後述するCoqのグラフィカルインターフェースを使えばコードを1ステップずつ対話的に読み進めめられます。The code also has special comments indicating which parts of the chapters make suitable starting points for interactive class sessions, where the class works together to construct the programs and proofs.  The included Makefile has a target <<templates>> for building a fresh set of class template files automatically from the book source.

(* A traditional printed version of the book is slated to appear from MIT Press in the future.  The online versions will remain available at no cost even after the printed book is released, and I intend to keep the source code up-to-date with bug fixes and compatibility changes to track new Coq releases. *)

%\index{graphical interfaces to Coq}%Coqを生産的に使うには優れたグラフィカルインターフェースが必要不可欠でしょう。筆者はEmacsの%\index{Proof General}%{{http://proofgeneral.inf.ed.ac.uk/}Proof General}モードを使っています。Proof GeneralはCoqの他にもいくつかの証明支援系をサポートしています。Coqチームによって開発されているスタンドアローンの%\index{CoqIDE}%CoqIDEプログラムもあります。著者は同じエディタの中で認証付きプログラミングと証明を他の作業を両方行えることを好みます。本書の最初でCoqの使い方を紹介する際にはProof Generalの手順を明示的に参照しますが、本書のほとんどはインターフェースに依存しないので、もしCoqIDEを使いたければそちらを使っても構いません。CoqIDEのバージョン8.4以下で本書のソースを実行する際に生じる一つの問題は、始めた証明をキャンセルするときに用いるCoqの[Abort]や#<span class="inlinecode"><span class="id" type="keyword">#%\coqdockw{%Restart%}%#</span></span>#コマンドがサポートされていないことです。これらのコマンドを現実の、完了した開発に残すのは良くないでしょうが、著者はこれらのコマンドを証明を設計するときのユーザの思考プロセスをたどるソースコードを書くのに役立つと考えます。
*)

(** ** Reading This Book *)

(**
(**
For experts in functional programming or formal methods, learning to use Coq is not hard, in a sense.  The Coq manual%~\cite{CoqManual}%, the textbook by Bertot and Cast%\'%eran%~\cite{CoqArt}%, and Pierce et al.'s %\emph{%Software Foundations%}\footnote{\url{http://www.cis.upenn.edu/~bcpierce/sf/}}% have helped many people become productive Coq users.  However, I believe that the best ways to manage significant Coq developments are far from settled.  In this book, I mean to propose my own techniques, and, rather than treating them as advanced material for a final chapter or two, I employ them from the very beginning.  After a first chapter showing off what can be done with dependent types, I retreat into simpler programming styles for the first part of the book.  I adopt the other main thrust of the book, Ltac proof automation, more or less from the very start of the technical exposition.

Some readers have suggested that I give multiple recommended reading orders in this introduction, targeted at people with different levels of Coq expertise.  It is certainly true that Part I of the book devotes significant space to basic concepts that most Coq users already know quite well.  However, as I am introducing these concepts, I am also developing my preferred automated proof style, so I think even the chapters on basics are worth reading for experienced Coq hackers.

Readers with no prior Coq experience can ignore the preceding discussion!  I hope that my heavy reliance on proof automation early on will seem like the most natural way to go, such that you may wonder why others are spending so much time entering sequences of proof steps manually.

Coq is a very complex system, with many different commands driven more by pragmatic concerns than by any overarching aesthetic principle.  When I use some construct for the first time, I try to give a one-sentence intuition for what it accomplishes, but I leave the details to the Coq reference manual%~\cite{CoqManual}%.  I expect that readers interested in complete understanding will be consulting that manual frequently; in that sense, this book is not meant to be completely standalone.  I often use constructs in code snippets without first introducing them at all, but explanations should always follow in the prose paragraphs immediately after the offending snippets.

Previous versions of the book included some suggested exercises at the ends of chapters.  Since then, I have decided to remove the exercises and focus on the main book exposition.  A database of exercises proposed by various readers of the book is #<a href="http://adam.chlipala.net/cpdt/ex/">#available on the Web#</a>#%\footnote{\url{http://adam.chlipala.net/cpdt/ex/}}%.  I do want to suggest, though, that the best way to learn Coq is to get started applying it in a real project, rather than focusing on artificial exercises. *)
*)
(**
関数型プログラミングか形式手法の熟練者には、ある意味でCoqの使い方を学ぶことは難しくありません。Coqのマニュアル%~\cite{CoqManual}%やBertot and Cast%\'%eran%~\cite{CoqArt}%、Pierceらの %\emph{%Software Foundations%}\footnote{\url{http://www.cis.upenn.edu/~bcpierce/sf/}}%は生産的にCoqを使うのに役立ちます。しかし、著者は重大なCoq開発をなし遂げる最良の方法は慣れることでは決してないと考えます。本書では、著者のテクニックを提示し、それらを最後の一、二章の発展的な道具として扱うのではなく、始めからそれらを使うつもりです。最初の章で依存型で何ができるかを見せた後、本書の第一部に対してよりシンプルなプログラミングスタイルへ方向転換します。また、本書の他の主眼として、Ltacによる証明の自動化をほとんど初歩から技術的に説明します。

読者は著者がCoqの異なる熟練度の人々に合わせて読む順番を与えることを提案しているかもしれません。本書の第一部ではほとんどのCoqユーザは既によく知っている基礎概念に多くの説明を捧げているのは事実です。しかし、それらの概念を導入するにあたって著者の好む自動化された証明のスタイルを展開するので、基礎の章も経験のあるCoqハッカーにとって価値があると思います。

Coqの経験がない読者は前述の議論を無視して構いません！　読者がなぜ他がマニュアル的に証明のステップの列を入力するのに多くの時間を費すのか疑問を持つくらいに、著者の早くからの証明の自動化への強い信頼が最も自然な方法と思えることを望みます。

Coqはとえも複雑なシステムで、美しい原理を追求することより実用的な懸念から導出されたコマンドがたくさんあります。何か構造物(* construct *)を始めて使うときは、それが何を成し遂げるかの一文での直感的説明を与えますが、詳細はCoqのリファレンスマニュアル%~\cite{CoqManual}%に譲ります。完璧な理解を求める読者はリファレンスマニュアルを頻繁に参照することでしょう。この意味では、本書は完全にはスタンドアローンになるようには書かれていません。しばしばコードの中で構造物を先に説明することなしに使うことがありますが、説明はいつもそのコードの直後の段落に置かれるでしょう。

本書の前のバージョンでは章の終わりに演習問題が含まれていました。それから、演習問題をなくして解説に焦点を当てることに決めました。本書のさまざまな読者に向けた演習問題のデータベースは#<a href="http://adam.chlipala.net/cpdt/ex/">#Webで利用できます#</a>#%\footnote{\url{http://adam.chlipala.net/cpdt/ex/}}%。しかし、Coqを学ぶための最良の方法は、人工的な演習問題を解くことよりもCoqを実際のプロジェクトに応用し始めることだと著者は提案します。
*)

(** ** On the Tactic Library *)

(**
(**
To make it possible to start from fancy proof automation, rather than working up to it, I have included with the book source a library of _tactics_, or programs that find proofs, since the built-in Coq tactics do not support a high enough level of automation.  I use these tactics even from the first chapter with code examples.

Some readers have asked about the pragmatics of using this tactic library in their own developments.  My position there is that this tactic library was designed with the specific examples of the book in mind; I do not recommend using it in other settings.  Part III should impart the necessary skills to reimplement these tactics and beyond.  One generally deals with undecidable problems in interactive theorem proving, so there can be no tactic that solves all goals, though the %\index{tactics!crush}%[crush] tactic that we will meet soon may sometimes feel like that!  There are still very useful tricks found in the implementations of [crush] and its cousins, so it may be useful to examine the commented source file <<CpdtTactics.v>>.  I implement a new tactic library for each new project, since each project involves a different mix of undecidable theories where a different set of heuristics turns out to work well; and that is what I recommend others do, too.
*)
*)
(**
Coqにあらかじめあるタクティクは十分高レベルな自動化をサポートしていないので、高機能な自動証明から始めるために、それらに取り組むよりも(* this can be more natural *)、本書のソースに証明を探すプログラムである＿タクティク＿のライブラリを含めました。これらのタクティクは最初の章からすでにコード例と共に用います。

このタクティクライブラリを開発で使うことについて何人かの読者に尋ねられたことがあります。著者としては、このタクティクライブラリは本書の特定の例と共に設計したつもりなので、他の場面で使うことは推奨しません。第三部でこれらのタクティクを再実装し、またそれを越えるのに十分な技術について添えます。一般に対話的定理証明では決定不可能な問題も扱われるので、すべてのゴールを解くようなタクティクはないかもしれません。(すぐに出てくる%\index{tactics!crush}%[crush]タクティクは時々そのようなものだと感じるかもしれませんが！)[crush]やその兄弟のタクティクの実装にはとても便利な秘訣があるので、コメント付きのソースファイル<<CpdtTactics.v>>を調べてみるのも有益かもしれません。著者は新しいプロジェクトごとに新しいタクティクライブラリを実装しています。各プロジェクトは異なる決定不可能な理論の組み合わせを含んでいて、異なる種類のヒューリスティクスがうまくいくからです。そして皆さんにもそれを勧めます。
*)

(** ** Installation and Emacs Set-Up *)

(**
(**
At the start of the next chapter, I assume that you have installed Coq and Proof General.  The code in this book is tested with Coq versions 8.4pl6, 8.5pl3, and 8.6.  Though parts may work with other versions, it is expected that the book source will fail to build with _earlier_ versions.

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
*)
(**
次の章の最初では、皆さんがCoqとProof Generalをインストールした状態であることを仮定します。本書のコードはCoqバージョン8.4pl6、8.5pl3、8.6でテストされています。部分的には他のバージョンで動くかもしれませんが、本書のソースはより以前のバージョンではビルドに失敗すると予想されます。

%\index{Proof General|(}%次の章でソースを処理するためにProof Generalの設定をするには、以下のシンプルなステップが必要です。

%\begin{enumerate}%#<ol>#

%\item %#<li>#以下からソースを取得
%\begin{center}\url{http://adam.chlipala.net/cpdt/cpdt.tgz}\end{center}%#<blockquote><tt><a href="http://adam.chlipala.net/cpdt/cpdt.tgz">http://adam.chlipala.net/cpdt/cpdt.tgz</a></tt></blockquote></li>#

%\item %#<li>#tarballをディレクトリ<<DIR>>に展開#</li>#

%\item %#<li>#<<DIR>>内で<<make>>を実行 (マルチコアがあるなら、それを使うために<<-j>>フラグを付けることが望まれます)#</li>#

%\item %#<li>#Coqの対話的トップレベルを与える<<coqtop>>プログラムのコマンドライン引数をProof Generalに渡す際にはいくつか小さい困った問題があります。たくさんのソースファイルに共有されるであろう設定を追加する方法の一つは、custom variable settingを%\index{.emacs file@\texttt{.emacs} file}%<<.emacs>>ファイルに以下のように追加することです：
<<
(custom-set-variables
  ...
  '(coq-prog-args '("-R" "DIR/src" "Cpdt"))
  ...
)
>>

ここで見せた特別な引数は本書のコードのための選択です。省略されているのは皆さんが既に設定しているかもしれないEmacsカスタマイズです。<<.emacs>>ファイルに、一つを除いて<<custom-set-variables>>ブロックにコメントアウトした複数の代替のフラグを保存しておくと便利かもしれません。

あるいは、設定を適用したいソースファイルのディレクトリ内の%\index{.dir-locals.el file@\texttt{.dir-locals.el} file}%<<.dir-locals.el>>ファイルを使うことで、Proof Generalの設定はディレクトリごとに指定できます。以下が本書のソースに使えるような設定ファイルの例です。CoqをEmacsサポートモードで開始するための引数を含める必要があることに注意してください。
<<
((coq-mode . ((coq-prog-args . ("-emacs-U" "-R" "DIR/src" "Cpdt")))))
>>
 #</li>#

#</ol>#%\end{enumerate}%

本書の各章はコメント付きのCoqソースファイルから生成されています。Proof Generalでそれらをロードしてステップ毎に実行できます。Coqバイナリ<<coqtop>>をコマンドライン引数<<-R DIR/src Cpdt>>を必ずつけて実行してください。Proof Generalを正しくインストールしたならば、CoqモードはEmacs内で<<.v>>バッファに入ったときに自動で始まり、<<.emacs>>設定の上記のアドバイスは<<coqtop>>に適切な引数がEmacsにより渡されることを保証するでしょう。

Proof Generalでは、Coqが実行されたバッファの一部は青の背景などでハイライトされます。Coqのソースファイルをステップ毎に実行するには、実行したい場所にカーソルを置いて C-C C-RET を押します。これは、ハイライトされた領域の外側でも内側でも、通常のステップ毎のコーディングのために使えます。
%\index{Proof General|)}% *)

(** %\section{Chapter Source Files}

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

% *)

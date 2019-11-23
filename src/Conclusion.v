(* Copyright (c) 2012, Adam Chlipala
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\addcontentsline{toc}{chapter}{結論}\chapter*{結論}% *)

(**
(** I have designed this book to present the key ideas needed to get started with productive use of Coq.  Many people have learned to use Coq through a variety of resources, yet there is a distinct lack of agreement on structuring principles and techniques for easing the evolution of Coq developments over time.  Here I have emphasized two unusual techniques: programming with dependent types and proving with scripted proof automation.  I have also tried to present other material following my own take on how to keep Coq code beautiful and scalable.

   Part of the attraction of Coq and similar tools is that their logical foundations are small.  A few pages of %\LaTeX{}%#LaTeX# code suffice to define CIC, Coq's logic, yet there do not seem to be any practical limits on which mathematical concepts may be encoded on top of this modest base.  At the same time, the _pragmatic_ foundation of Coq is vast, encompassing tactics, libraries, and design patterns for programs, theorem statements, and proof scripts.  I hope the preceding chapters have given a sense of just how much there is to learn before it is possible to drive Coq with the same ease with which many readers write informal proofs!  The pay-off of this learning process is that many proofs, especially those with many details to check, become much easier to write than they are on paper.  Further, the truth of such theorems may be established with much greater confidence, even without reading proof details.

   As Coq has so many moving parts to catalogue mentally, I have not attempted to describe most of them here; nor have I attempted to give exhaustive descriptions of the few I devote space to.  To those readers who have made it this far through the book, my advice is: read through the Coq manual, front to back, at some level of detail.  Get a sense for which bits of functionality are available.  Dig more into those categories that sound relevant to the developments you want to build, and keep the rest in mind in case they come in handy later.

   In a domain as rich as this one, the learning process never ends.  The Coq Club mailing list (linked from the Coq home page) is a great place to get involved in discussions of the latest improvements, or to ask questions about stumbling blocks that you encounter.  (I hope that this book will save you from needing to ask some of the most common questions!)  I believe the best way to learn is to get started using Coq to build some development that interests you.

   Good luck! *)
*)
(**
著者は、Coqの生産的な使い方から始めるために必要なキー・アイデアを提示するように本書をデザインしました。
Many people have learned to use Coq through a variety of resources, yet there is a distinct lack of agreement on structuring principles and techniques for easing the evolution of Coq developments over time.
たくさんの人は様々な資料を通してCoqの使い方を学んできましたが、体系的原理と、Coq開発の発展を容易にする技術との一致の明確な欠如がありました。
著者は二つの際立った技術を強調してきました。依存型を用いたプログラミングとスクリプトでの証明の自動化です。
また、Coqコードを美しくかつ拡張性を保つ方法についての個人的な意見に基く他の題材も提供することを試みました。

   Coqや類似したツールの魅力の一部は、それらの論理的基礎が小さいことです。
   Coqの論理、CICは数ページの %\LaTeX{}%#LaTeX# コードで定義できますが、どんな実用的な数学的概念もこの大きくない論理的基礎の上に表現されるように思えます。
   同時に、タクティク、ライブラリ、プログラム・定理の主張・証明スクリプトのデザインパターンを含む、Coqの実践的な基礎は莫大にあります。
   前のいくつかの章では、たくさんの読者が非形式的な証明を書くのと同じ手軽さでCoqを動かせるようになるまでにどのくらいのことを学ぶのかについての感覚を持ってもらえれば幸いです！
   この学習の見返りは、たくさんの証明、特に、確かめるべき詳細がたくさんある証明が、紙での証明よりもずっと簡単になることです。
   また、そのような定理の事実は、証明の詳細を読むことさえなく非常に強い自信を生むことかもしれません。

   Coqは全体像をつかむにはとてもたくさんの可動部分があるため、それらのほとんどはここでは説明しようとはしませんでしたし、説明を捧げた少ない部分の徹底的な説明も与えようとはしませんでした。
   To those readers who have made it this far through the book, my advice is: read through the Coq manual, front to back, at some level of detail.
   Get a sense for which bits of functionality are available.
   あなたの開発したいものに関係しそうな種類のものを掘り下げて、残りは後で便利になるように心に留めてください。

   これと同じくらい豊かな領域では、学習は終わることはありません。
   Coq Clubというメーリングリスト(Coqのホームページからリンクされています)は最新の改良の議論に参加したり、つまづいた点についての質問を聞くのによい場所です。
   (本書によっていくらかの最も頻繁に聞かれる質問をする必要を減らせることを願っています！)
   学ぶための最良の方法は、Coqを使ってあなたの興味のあるものを開発することだと強く思います。

   幸運を！ *)

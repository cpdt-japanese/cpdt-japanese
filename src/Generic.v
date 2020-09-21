(* Copyright (c) 2008-2010, 2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import String List.

Require Import Cpdt.CpdtTactics Cpdt.DepList.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(** printing ~> $\leadsto$ *)


(**
 (* %\chapter{Generic Programming}% *)
    %\chapter{総称的プログラミング}%
 *)

(**
 (* %\index{generic programming}% _Generic programming_ makes it possible to write functions that operate over different types of data.  %\index{parametric polymorphism}%Parametric polymorphism in ML and Haskell is one of the simplest examples.  ML-style %\index{module systems}%module systems%~\cite{modules}% and Haskell %\index{type classes}%type classes%~\cite{typeclasses}% are more flexible cases.  These language features are often not as powerful as we would like.  For instance, while Haskell includes a type class classifying those types whose values can be pretty-printed, per-type pretty-printing is usually either implemented manually or implemented via a %\index{deriving clauses}%[deriving] clause%~\cite{deriving}%, which triggers ad-hoc code generation.  Some clever encoding tricks have been used to achieve better within Haskell and other languages, but we can do%\index{datatype-generic programming}% _datatype-generic programming_ much more cleanly with dependent types.  Thanks to the expressive power of CIC, we need no special language support.

   Generic programming can often be very useful in Coq developments, so we devote this chapter to studying it.  In a proof assistant, there is the new possibility of generic proofs about generic programs, which we also devote some space to. *)

  %\index{そうしょうてきぷろぐらみんぐ@総称的プログラミング}%%\emph{総称的プログラミング}%はデータの異なる型にわたって動作する関数を書くことを可能にします。
  MLとHaskellでの%\index{ぱらめーたたそう@パラメータ多相}%パラメータ多相は最も単純な例の一つです。
  MLスタイルの %\index{もじゅーるしすてむ@モジュールシステム}%モジュールシステム%~\cite{modules}% とHaskellの %\index{かたくらす@型クラス}%型クラス%~\cite{typeclasses}% はより柔軟な事例です。
  これらの言語機能は私たちが望んでいるほど強力でないことがよくあります。
  例えば、Haskellには型の値をプリティプリント(整形印字)できるよう分類する型クラスが含まれますが、型ごとのプリティプリントは通常は、手動で実装するか%\index{derivingせつ@deriving節}%[deriving]節%~\cite{deriving}%を経由して(これはアドホックにコードを生成します)実装するかです。
  Haskellや他の言語ではよりうまく書くための多少の巧妙な符号化の技巧が利用されてきましたが、私たちは%\index{でーたがたについてのそうしょうてきなぷろぐらみんぐ@データ型について総称的なプログラミング}%%\emph{データ型について総称的な}%プログラミングをより明快に依存型とともに行なうことができます。
  CICの表現力のおかげで、特別な言語サポートは必要ありません。

  総称的プログラミングはCoqでの開発においてとても有用なので、この章ではこれを学ぶことに専念します。
  証明アシスタントにおいては、総称的プログラムにおける総称的な証明の新しい可能性があり、多少の紙面をこのために費やします。
 *)

(**
 (* * Reifying Datatype Definitions *)
    * データ型の定義を具体化する
  *)

(**
 (* The key to generic programming with dependent types is%\index{universe types}% _universe types_.  This concept should not be confused with the idea of _universes_ from the metatheory of CIC and related languages, which we will study in more detail in the next chapter.  Rather, the idea of universe types is to define inductive types that provide _syntactic representations_ of Coq types.  We cannot directly write CIC programs that do case analysis on types, but we _can_ case analyze on reified syntactic versions of those types.

   Thus, to begin, we must define a syntactic representation of some class of datatypes.  In this chapter, our running example will have to do with basic algebraic datatypes, of the kind found in ML and Haskell, but without additional bells and whistles like type parameters and mutually recursive definitions.

   The first step is to define a representation for constructors of our datatypes.  We use the [Record] command as a shorthand for defining an inductive type with a single constructor, plus projection functions for pulling out any of the named arguments to that constructor. *)

  依存型のある総称的プログラミングの秘訣は %\index{ゆにばーすたいぷ@ユニバースタイプ}%%\emph{ユニバースタイプ}%です。
  この概念は、CIC や、それに関係する言語のメタ理論からの%\emph{宇宙(ユニバース)}%のアイデアと混同されるべきではありません。それについては次の章でより詳しく学ぶことになるでしょう。
  むしろ、ユニバースタイプのアイデアは、Coqの型の%\emph{構文上の表現}%を提供ような、帰納型を定義するものです。
  型についての場合分けをするCICのプログラムを直接書くことはできませんが、これらの型を構文に具体化したものについてなら場合分けすることが%\emph{できます}%。

  よって、最初にデータ型のあるクラスの構文上の表現を定義しなければなりません。
  この章では、実行例は、MLやHaskellで見られるような基本的な代数的データ型を使用することになるでしょう。しかし、型パラメータや相互再帰的定義のような付加機能は無しです。
  (* 慣用表現: bells and whistles - おまけ、付加機能 *)

  最初の一歩はデータ型のコンストラクタに対する表現を定義することです。
  単一のコンストラクタをもつ帰納型を定義する簡潔な表現として [Record] コマンドを使います。
  その帰納型は、加えて、そのコンストラクタの名前付き引数を任意に取り出すための射影関数を持ちます。
 *)

(* EX: Define a reified representation of simple algebraic datatypes. *)

(* begin thide *)
Record constructor : Type := Con {
  nonrecursive : Type;
  recursive : nat
}.

(**
 (* The idea is that a constructor represented as [Con T n] has [n] arguments of the type that we are defining.  Additionally, all of the other, non-recursive arguments can be encoded in the type [T].  When there are no non-recursive arguments, [T] can be [unit].  When there are two non-recursive arguments, of types [A] and [B], [T] can be [A * B].  We can generalize to any number of arguments via tupling.

   With this definition, it is easy to define a datatype representation in terms of lists of constructors.  The intended meaning is that the datatype came from an inductive definition including exactly the constructors in the list. *)

  このアイデアは、[Con T n]として表現されたコンストラクタが[n]個の定義された型の引数を持つというものです。
  加えて、他のすべての再帰的でない引数は型[T]に符号化できます。
  再帰的でない引数が無い場合には、[T]としては[unit]を取れます。
  二つの再帰的でない引数、型[A]と[B]がある場合、[T]としては[A * B]を取れます。
  タプル化によって任意の数の引数へと一般化できます。

  この定義では、コンストラクタのリストにおいてデータ型の表現を容易に定義できます。
  趣旨としては、そのデータ型はそのリスト内のコンストラクタを正確に含んだ帰納的定義から生じるということです。
 *)

Definition datatype := list constructor.

(**
 (* Here are a few example encodings for some common types from the Coq standard library.  While our syntax type does not support type parameters directly, we can implement them at the meta level, via functions from types to [datatype]s. *)

 Coqの標準ライブラリから、いくつかのありふれた型の符号化の例をここで紹介します。
 構文の型は、型パラメータを直接はサポートしていませんが、型から [datatype]への関数によって、メタレベルでそれらを実装することができます。
 *)

Definition Empty_set_dt : datatype := nil.
Definition unit_dt : datatype := Con unit 0 :: nil.
Definition bool_dt : datatype := Con unit 0 :: Con unit 0 :: nil.
Definition nat_dt : datatype := Con unit 0 :: Con unit 1 :: nil.
Definition list_dt (A : Type) : datatype := Con unit 0 :: Con A 1 :: nil.

(**
 (* The type [Empty_set] has no constructors, so its representation is the empty list.  The type [unit] has one constructor with no arguments, so its one reified constructor indicates no non-recursive data and [0] recursive arguments.  The representation for [bool] just duplicates this single argumentless constructor.    We get from [bool] to [nat] by changing one of the constructors to indicate 1 recursive argument.  We get from [nat] to [list] by adding a non-recursive argument of a parameter type [A].

   As a further example, we can do the same encoding for a generic binary tree type. *)

  型[Empty_set]にはコンストラクタは無いので、その表現は空リストです。
  型[unit]は引数の無い一つのコンストラクタを持ち、その具体化されたコンストラクタは、再帰的でないデータを持たず、再帰的な引数は[0]であることを表わします。
  [bool]の表現は、引数の無い単一のコンストラクタをただ複製しています。
  [bool]から[nat]へは、コンストラクタの一つを、一つの再帰的引数を持つように変化させることで得られます。
  [nat]から[list]へは、パラメータ型[A]の再帰的でない引数を加えることで得られます。

  さらなる例として、総称的な二分木に対する同様の符号化を行なうことができます。
 *)

(* end thide *)

Section tree.
  Variable A : Type.

  Inductive tree : Type :=
  | Leaf : A -> tree
  | Node : tree -> tree -> tree.
End tree.

(* begin thide *)
Definition tree_dt (A : Type) : datatype := Con A 0 :: Con unit 2 :: nil.

(**
 (* Each datatype representation stands for a family of inductive types.  For a specific real datatype and a reputed representation for it, it is useful to define a type of _evidence_ that the datatype is compatible with the encoding. *)

 それぞれのデータ型の表現は帰納型の族をあらわします。
 特定の現実のデータ型とそれに対するいわゆる表現に対して、そのデータ型が符号化について互換性がある%\emph{証拠}%としての型を定義するのは便利です。
 *)

Section denote.
  Variable T : Type.
  (**
   (* This variable stands for the concrete datatype that we are interested in. *)

   この変数は注目している具体的なデータ型を表します。
   *)

  Definition constructorDenote (c : constructor) :=
    nonrecursive c -> ilist T (recursive c) -> T.
  (**
   (* We write that a constructor is represented as a function returning a [T].  Such a function takes two arguments, which pack together the non-recursive and recursive arguments of the constructor.  We represent a tuple of all recursive arguments using the length-indexed list type %\index{Gallina terms!ilist}%[ilist] that we met in Chapter 8. *)

   コンストラクタは[T]を返す関数として表現されると書きました。
   その関数は2つ引数を取り、 コンストラクタの、再帰的でないあるいは再帰的な引数を一緒にパックしています。
   8章で出てきた、長さでインデックスされたリスト型%\index{Gallinaこう@Gallina項!ilist}%[ilist]を使って、全ての再帰的な引数のタプルを表現します。
   *)

  Definition datatypeDenote := hlist constructorDenote.
  (**
   (* Finally, the evidence for type [T] is a %\index{Gallina terms!hlist}%heterogeneous list, including a constructor denotation for every constructor encoding in a datatype encoding.  Recall that, since we are inside a section binding [T] as a variable, [constructorDenote] is automatically parameterized by [T]. *)

   最後に、型[T] に対する証拠は%\index{Gallinaこう@Gallina項!hlist}%ヘテロリストです。データ型の符号化内のそれぞれのコンストラクタの符号化に対するコンストラクタの表示的意味を含みます。
   [T] を変数に束縛しているセクション内なので、[constructorDenote] は自動的に [T] によってパラメタ化されることを思い出しましょう。
   *)

End denote.
(* end thide *)

(**
 (* Some example pieces of evidence should help clarify the convention.  First, we define a helpful notation for constructor denotations.  %The ASCII \texttt{\textasciitilde{}>} from the notation will be rendered later as $\leadsto$.%  *)

 証拠のいくつかの例は約束事を明らかにするのに役立つはずです。
 最初にコンストラクタの表示的意味なための便利な記法を定義します。
 %アスキー文字 \texttt{\textasciitilde{}>} は後で $\leadsto$ としてレンダリングされます。%
 *)

Notation "[ v , r ~> x ]" := ((fun v r => x) : constructorDenote _ (Con _ _)).

(* begin thide *)
Definition Empty_set_den : datatypeDenote Empty_set Empty_set_dt :=
  HNil.
Definition unit_den : datatypeDenote unit unit_dt :=
  [_, _ ~> tt] ::: HNil.
Definition bool_den : datatypeDenote bool bool_dt :=
  [_, _ ~> true] ::: [_, _ ~> false] ::: HNil.
Definition nat_den : datatypeDenote nat nat_dt :=
  [_, _ ~> O] ::: [_, r ~> S (hd r)] ::: HNil.
Definition list_den (A : Type) : datatypeDenote (list A) (list_dt A) :=
  [_, _ ~> nil] ::: [x, r ~> x :: hd r] ::: HNil.
Definition tree_den (A : Type) : datatypeDenote (tree A) (tree_dt A) :=
  [v, _ ~> Leaf v] ::: [_, r ~> Node (hd r) (hd (tl r))] ::: HNil.
(* end thide *)

(**
 (* Recall that the [hd] and [tl] calls above operate on richly typed lists, where type indices tell us the lengths of lists, guaranteeing the safety of operations like [hd].  The type annotation attached to each definition provides enough information for Coq to infer list lengths at appropriate points. *)

 上記の [hd] と [tl] の呼び出しはリッチに型付けされたリストを操作することを思い出しましょう。型の添字でリストの長さがわかり、[hd]のように操作の安全性を保証します。
 各定義につけられた型注釈は Coq が適切な箇所でリストの長さを推論するのに十分な情報を提供します。
 *)


(**
 (* * Recursive Definitions *)
    * 再帰的定義
  *)

(* EX: Define a generic [size] function. *)

(**
 (* We built these encodings of datatypes to help us write datatype-generic recursive functions.  To do so, we will want a reified representation of a%\index{recursion schemes}% _recursion scheme_ for each type, similar to the [T_rect] principle generated automatically for an inductive definition of [T].  A clever reuse of [datatypeDenote] yields a short definition.  *)

 データ型について総称的な再帰関数を書くのに役立つようデータ型の符号化を構成しました。
 そのためには、それぞれの型についての%\index{さいきすきーむ@再帰スキーム}%%\emph{再帰スキーム}%を具体化した表現があるのが望ましいでしょう。その表現は[T]の帰納的定義について自動的に生成された[T_rect]の原理と類似のものです。
 [datatypeDenote]を巧妙に再利用することで短い定義を作りだします。
 *)

(* begin thide *)
Definition fixDenote (T : Type) (dt : datatype) :=
  forall (R : Type), datatypeDenote R dt -> (T -> R).

(**
 (* The idea of a recursion scheme is parameterized by a type and a reputed encoding of it.  The principle itself is polymorphic in a type [R], which is the return type of the recursive function that we mean to write.  The next argument is a heterogeneous list of one case of the recursive function definition for each datatype constructor.  The [datatypeDenote] function turns out to have just the right definition to express the type we need; a set of function cases is just like an alternate set of constructors where we replace the original type [T] with the function result type [R].  Given such a reified definition, a [fixDenote] invocation returns a function from [T] to [R], which is just what we wanted.

   We are ready to write some example functions now.  It will be useful to use one new function from the [DepList] library included in the book source. *)

 再帰スキームのアイデアは型と型のいわゆる符号化によってパラメータ化されています。
 その原理自体は型[R](記述しようとしている再帰関数の返り値の型)が多相的であることです。
 その次の論点は、各データ型のコンストラクタに対する再帰関数定義を一つのケースとしたものについての、ヘテロリストです。
 [datatypeDenote]関数が、必要な型をあらわす寸分たがわぬ定義を持つような生成を行ないます; 関数(による)ケースひと揃いは、もとの型[T]を関数の結果の型[R]に置き換えるような、まさしく代わりのコンストラクタひと揃いのようなものです。
 このような具体化された定義を考えると、[fixDenote]の実行は[T]から[R]への関数を返します。これが欲しかったものです。

 今や関数の例をいくつかを記述する準備ができました。
 本書のソースに含まれている[DepList]ライブラリの一つの新たな関数を利用するのが便利でしょう。
 *)

Check hmake.
(** %\vspace{-.15in}% [[
  hmake
     : forall (A : Type) (B : A -> Type),
       (forall x : A, B x) -> forall ls : list A, hlist B ls
       ]]

 (* The function [hmake] is a kind of [map] alternative that goes from a regular [list] to an [hlist].  We can use it to define a generic size function that counts the number of constructors used to build a value in a datatype. *)

 関数[hmake]は通常の[list]から[hlist]への、ある種の[map]の代わりのものです。
 データ型の値を組み立てる際に使われるコンストラクタの数を数える総称的なsize関数を定義するのに利用できます。
 *)

Definition size T dt (fx : fixDenote T dt) : T -> nat :=
  fx nat (hmake (B := constructorDenote nat) (fun _ _ r => foldr plus 1 r) dt).

(**
 (* Our definition is parameterized over a recursion scheme [fx].  We instantiate [fx] by passing it the function result type and a set of function cases, where we build the latter with [hmake].  The function argument to [hmake] takes three arguments: the representation of a constructor, its non-recursive arguments, and the results of recursive calls on all of its recursive arguments.  We only need the recursive call results here, so we call them [r] and bind the other two inputs with wildcards.  The actual case body is simple: we add together the recursive call results and increment the result by one (to account for the current constructor).  This [foldr] function is an [ilist]-specific version defined in the [DepList] module.

   It is instructive to build [fixDenote] values for our example types and see what specialized [size] functions result from them. *)

 私たちの定義は再帰スキーム[fx]においてパラーメータ化されます。
 関数の結果の型と関数ケースひと揃いを渡すことで[fx]をインスタンス化します。後者は[hmake]で構成します。
 [hmake]への関数引数は 3つです: コンストラクタの表現、再帰的でない引数、および再帰的な引数すべてにおける再帰呼び出しの結果です。
 再帰呼び出しの結果が必要なのはここだけなので、それらを[r]として他の2つの入力はワイルドカードに束縛します。
 実際のケースの本体は簡単です: 再帰呼び出しの結果を足しあわせてその結果を1増やします。(現在のコンストラクタを考慮します)
 この[foldr]関数は[DepList]モジュールで定義している[ilist]に特化した版です。

 例示した型について[fixDenote]の値を構成するのと、その特殊化された[size]関数の結果を見るのは、ためになります。
 *)

Definition Empty_set_fix : fixDenote Empty_set Empty_set_dt :=
  fun R _ emp => match emp with end.
Eval compute in size Empty_set_fix.
(** %\vspace{-.15in}% [[
     = fun emp : Empty_set => match emp return nat with
                              end
     : Empty_set -> nat
]]

 (* Despite all the fanciness of the generic [size] function, CIC's standard computation rules suffice to normalize the generic function specialization to exactly what we would have written manually. *)

 総称的な[size]関数が風変わりであるにもかかわらず、CICの標準的な計算規則は手書きで書いた総称的な関数の特殊化を正確に正規化するのには十分です。
 *)

Definition unit_fix : fixDenote unit unit_dt :=
  fun R cases _ => (hhd cases) tt INil.
Eval compute in size unit_fix.
(** %\vspace{-.15in}% [[
     = fun _ : unit => 1
     : unit -> nat
]]

 (* Again normalization gives us the natural function definition.  We see this pattern repeated for our other example types. *)

 さらに正規化は自然な関数定義を与えてくれます。
 このパターンは他の型の例でも繰り返しみることになるでしょう。
 *)

Definition bool_fix : fixDenote bool bool_dt :=
  fun R cases b => if b
    then (hhd cases) tt INil
    else (hhd (htl cases)) tt INil.
Eval compute in size bool_fix.
(** %\vspace{-.15in}% [[
     = fun b : bool => if b then 1 else 1
     : bool -> nat
]]
*)

Definition nat_fix : fixDenote nat nat_dt :=
  fun R cases => fix F (n : nat) : R :=
    match n with
      | O => (hhd cases) tt INil
      | S n' => (hhd (htl cases)) tt (ICons (F n') INil)
    end.

(**
 (* To peek at the [size] function for [nat], it is useful to avoid full computation, so that the recursive definition of addition is not expanded inline.  We can accomplish this with proper flags for the [cbv] reduction strategy. *)

 [nat]に対する[size]関数を見てみると、全体が計算されてしまうのを避けるために、加算の再帰的定義がインラインに展開されないことが役立っています。
 これは[cbv]簡約戦略に対する適切なフラグを利用することで得られます。
 *)

Eval cbv beta iota delta -[plus] in size nat_fix.
(** %\vspace{-.15in}% [[
     = fix F (n : nat) : nat := match n with
                                | 0 => 1
                                | S n' => F n' + 1
                                end
     : nat -> nat
]]
*)

Definition list_fix (A : Type) : fixDenote (list A) (list_dt A) :=
  fun R cases => fix F (ls : list A) : R :=
    match ls with
      | nil => (hhd cases) tt INil
      | x :: ls' => (hhd (htl cases)) x (ICons (F ls') INil)
    end.
Eval cbv beta iota delta -[plus] in fun A => size (@list_fix A).
(** %\vspace{-.15in}% [[
     = fun A : Type =>
       fix F (ls : list A) : nat :=
         match ls with
         | nil => 1
         | _ :: ls' => F ls' + 1
         end
     : forall A : Type, list A -> nat
]]
*)

Definition tree_fix (A : Type) : fixDenote (tree A) (tree_dt A) :=
  fun R cases => fix F (t : tree A) : R :=
    match t with
      | Leaf x => (hhd cases) x INil
      | Node t1 t2 => (hhd (htl cases)) tt (ICons (F t1) (ICons (F t2) INil))
    end.
Eval cbv beta iota delta -[plus] in fun A => size (@tree_fix A).
(** %\vspace{-.15in}% [[
     = fun A : Type =>
       fix F (t : tree A) : nat :=
         match t with
         | Leaf _ => 1
         | Node t1 t2 => F t1 + (F t2 + 1)
         end
     : forall A : Type, tree A -> n
]]
*)
(* end thide *)

(**
 (* As our examples show, even recursive datatypes are mapped to normal-looking size functions. *)

 例で見てきたように、再帰的データ型であっても普通に見えるサイズ関数へと対応付けられます。
 *)


(**
 (* ** Pretty-Printing *)
    ** プリティプリント
 *)

(**
 (* It is also useful to do generic pretty-printing of datatype values, rendering them as human-readable strings.  To do so, we will need a bit of metadata for each constructor.  Specifically, we need the name to print for the constructor and the function to use to render its non-recursive arguments.  Everything else can be done generically. *)

 データ型の値の総称的なプリティプリントを行なうのも便利です。値を人が読み取れる文字列へと整形します。
 そのためには、それぞれのコンストラクタに少しメタデータが必要です。
 具体的には、コンストラクタをプリントする名前と型の再帰的でない引数を整形するのに使用する関数が必要です。
 その他諸々は総称的に行なうことができます。
 *)

Record print_constructor (c : constructor) : Type := PI {
  printName : string;
  printNonrec : nonrecursive c -> string
}.

(**
 (* It is useful to define a shorthand for applying the constructor [PI].  By applying it explicitly to an unknown application of the constructor [Con], we help type inference work. *)

 コンストラクタ[PI]の適用の略記を定義すると便利です。
 まだわからないコンストラクタ[Con]の適用に対して明示的にこれを適用することが、型推論がうまくいく助けになります。
 *)

Notation "^" := (PI (Con _ _)).

(**
 (* As in earlier examples, we define the type of metadata for a datatype to be a heterogeneous list type collecting metadata for each constructor. *)

 先の例のように、データ型のためにメタデータの型を定義します。そのデータ型は、それぞれのコンストラクタに対するメタデータを集めるヘテロリストの型となるものです。
 *)

Definition print_datatype := hlist print_constructor.

(**
 (* We will be doing some string manipulation here, so we import the notations associated with strings. *)

 ここでは文字列の操作をいくつか行なっていく予定なので、文字列に関連するノーテーションをインポートします。
 *)

Local Open Scope string_scope.

(**
 (* Now it is easy to implement our generic printer, using another function from [DepList.] *)

 今となっては、[DepList]からのもう一つの関数を利用して、総称的なプリンタを実装するのは簡単です。
 *)

Check hmap.
(** %\vspace{-.15in}% [[
  hmap
     : forall (A : Type) (B1 B2 : A -> Type),
       (forall x : A, B1 x -> B2 x) ->
       forall ls : list A, hlist B1 ls -> hlist B2 ls
]]
*)

Definition print T dt (pr : print_datatype dt) (fx : fixDenote T dt) : T -> string :=
  fx string (hmap (B1 := print_constructor) (B2 := constructorDenote string)
    (fun _ pc x r => printName pc ++ "(" ++ printNonrec pc x
      ++ foldr (fun s acc => ", " ++ s ++ acc) ")" r) pr).

(**
 (* Some simple tests establish that [print] gets the job done. *)

 いくつかの簡潔なテストで、[print]で仕事が完了することを確認します。
 *)

Eval compute in print HNil Empty_set_fix.
(** %\vspace{-.15in}% [[
     = fun emp : Empty_set => match emp return string with
                              end
     : Empty_set -> string
     ]]
     *)

Eval compute in print (^ "tt" (fun _ => "") ::: HNil) unit_fix.
(** %\vspace{-.15in}% [[
     = fun _ : unit => "tt()"
     : unit -> string
   ]]
   *)

Eval compute in print (^ "true" (fun _ => "")
  ::: ^ "false" (fun _ => "")
  ::: HNil) bool_fix.
(** %\vspace{-.15in}% [[
   = fun b : bool => if b then "true()" else "false()"
   : bool -> string
   ]]
   *)

Definition print_nat := print (^ "O" (fun _ => "")
  ::: ^ "S" (fun _ => "")
  ::: HNil) nat_fix.
Eval cbv beta iota delta -[append] in print_nat.
(** %\vspace{-.15in}% [[
     = fix F (n : nat) : string :=
         match n with
         | 0%nat => "O" ++ "(" ++ "" ++ ")"
         | S n' => "S" ++ "(" ++ "" ++ ", " ++ F n' ++ ")"
         end
     : nat -> string
     ]]
     *)

Eval simpl in print_nat 0.
(** %\vspace{-.15in}% [[
     = "O()"
     : string
     ]]
     *)

Eval simpl in print_nat 1.
(** %\vspace{-.15in}% [[
     = "S(, O())"
     : string
     ]]
     *)

Eval simpl in print_nat 2.
(** %\vspace{-.15in}% [[
     = "S(, S(, O()))"
     : string
     ]]
     *)

Eval cbv beta iota delta -[append] in fun A (pr : A -> string) =>
  print (^ "nil" (fun _ => "")
  ::: ^ "cons" pr
  ::: HNil) (@list_fix A).
(** %\vspace{-.15in}% [[
     = fun (A : Type) (pr : A -> string) =>
       fix F (ls : list A) : string :=
         match ls with
         | nil => "nil" ++ "(" ++ "" ++ ")"
         | x :: ls' => "cons" ++ "(" ++ pr x ++ ", " ++ F ls' ++ ")"
         end
     : forall A : Type, (A -> string) -> list A -> string
     ]]
     *)

Eval cbv beta iota delta -[append] in fun A (pr : A -> string) =>
  print (^ "Leaf" pr
  ::: ^ "Node" (fun _ => "")
  ::: HNil) (@tree_fix A).
(** %\vspace{-.15in}% [[
     = fun (A : Type) (pr : A -> string) =>
       fix F (t : tree A) : string :=
         match t with
         | Leaf x => "Leaf" ++ "(" ++ pr x ++ ")"
         | Node t1 t2 =>
             "Node" ++ "(" ++ "" ++ ", " ++ F t1 ++ ", " ++ F t2 ++ ")"
         end
     : forall A : Type, (A -> string) -> tree A -> string
     ]]
     *)

(* begin hide *)
(* begin thide *)
Definition append' := append.
(* end thide *)
(* end hide *)

(**
 (* Some of these simplified terms seem overly complex because we have turned off simplification of calls to [append], which is what uses of the [++] operator desugar to.  Selective [++] simplification would combine adjacent string literals, yielding more or less the code we would write manually to implement this printing scheme. *)
 いくつかの簡約された項はあまりに複雑に見えます。なぜなら[append]の呼び出しに対する簡約をオフにしているからです。[append]は[++]演算子の脱糖先に利用します。
 選択的に[++]を簡約するなら、隣接した文字列リテラルは結合されますが、この印字方法を実装するのに手書きするコードが増減していたでしょう。
 *)


(** ** Mapping *)

(** By this point, we have developed enough machinery that it is old hat to define a generic function similar to the list [map] function. *)

Definition map T dt (dd : datatypeDenote T dt) (fx : fixDenote T dt) (f : T -> T)
  : T -> T :=
  fx T (hmap (B1 := constructorDenote T) (B2 := constructorDenote T)
    (fun _ c x r => f (c x r)) dd).

Eval compute in map Empty_set_den Empty_set_fix.
(** %\vspace{-.15in}% [[
     = fun (_ : Empty_set -> Empty_set) (emp : Empty_set) =>
       match emp return Empty_set with
       end
     : (Empty_set -> Empty_set) -> Empty_set -> Empty_set
     ]]
     *)

Eval compute in map unit_den unit_fix.
(** %\vspace{-.15in}% [[
     = fun (f : unit -> unit) (_ : unit) => f tt
     : (unit -> unit) -> unit -> unit
     ]]
     *)

Eval compute in map bool_den bool_fix.
(** %\vspace{-.15in}% [[
     = fun (f : bool -> bool) (b : bool) => if b then f true else f false
     : (bool -> bool) -> bool -> bool
     ]]
     *)

Eval compute in map nat_den nat_fix.
(** %\vspace{-.15in}% [[
     = fun f : nat -> nat =>
       fix F (n : nat) : nat :=
         match n with
         | 0%nat => f 0%nat
         | S n' => f (S (F n'))
         end
     : (nat -> nat) -> nat -> nat
     ]]
     *)

Eval compute in fun A => map (list_den A) (@list_fix A).
(** %\vspace{-.15in}% [[
     = fun (A : Type) (f : list A -> list A) =>
       fix F (ls : list A) : list A :=
         match ls with
         | nil => f nil
         | x :: ls' => f (x :: F ls')
         end
     : forall A : Type, (list A -> list A) -> list A -> list A
     ]]
     *)

Eval compute in fun A => map (tree_den A) (@tree_fix A).
(** %\vspace{-.15in}% [[
     = fun (A : Type) (f : tree A -> tree A) =>
       fix F (t : tree A) : tree A :=
         match t with
         | Leaf x => f (Leaf x)
         | Node t1 t2 => f (Node (F t1) (F t2))
         end
     : forall A : Type, (tree A -> tree A) -> tree A -> tree A
     ]]
     *)

(** These [map] functions are just as easy to use as those we write by hand.  Can you figure out the input-output pattern that [map_nat S] displays in these examples? *)

Definition map_nat := map nat_den nat_fix.
Eval simpl in map_nat S 0.
(** %\vspace{-.15in}% [[
     = 1%nat
     : nat
     ]]
     *)

Eval simpl in map_nat S 1.
(** %\vspace{-.15in}% [[
     = 3%nat
     : nat
     ]]
     *)

Eval simpl in map_nat S 2.
(** %\vspace{-.15in}% [[
     = 5%nat
     : nat
     ]]
     *)

(** We get [map_nat S n] = [2 * n + 1], because the mapping process adds an extra [S] at every level of the inductive tree that defines a natural, including at the last level, the [O] constructor. *)


(** * Proving Theorems about Recursive Definitions *)

(** We would like to be able to prove theorems about our generic functions.  To do so, we need to establish additional well-formedness properties that must hold of pieces of evidence. *)

Section ok.
  Variable T : Type.
  Variable dt : datatype.

  Variable dd : datatypeDenote T dt.
  Variable fx : fixDenote T dt.

  (** First, we characterize when a piece of evidence about a datatype is acceptable.  The basic idea is that the type [T] should really be an inductive type with the definition given by [dd].  Semantically, inductive types are characterized by the ability to do induction on them.  Therefore, we require that the usual induction principle is true, with respect to the constructors given in the encoding [dd]. *)

  Definition datatypeDenoteOk :=
    forall P : T -> Prop,
      (forall c (m : member c dt) (x : nonrecursive c) (r : ilist T (recursive c)),
        (forall i : fin (recursive c), P (get r i))
        -> P ((hget dd m) x r))
      -> forall v, P v.

  (** This definition can take a while to digest.  The quantifier over [m : member c dt] is considering each constructor in turn; like in normal induction principles, each constructor has an associated proof case.  The expression [hget dd m] then names the constructor we have selected.  After binding [m], we quantify over all possible arguments (encoded with [x] and [r]) to the constructor that [m] selects.  Within each specific case, we quantify further over [i : fin (recursive c)] to consider all of our induction hypotheses, one for each recursive argument of the current constructor.

     We have completed half the burden of defining side conditions.  The other half comes in characterizing when a recursion scheme [fx] is valid.  The natural condition is that [fx] behaves appropriately when applied to any constructor application. *)

  Definition fixDenoteOk :=
    forall (R : Type) (cases : datatypeDenote R dt)
      c (m : member c dt)
      (x : nonrecursive c) (r : ilist T (recursive c)),
      fx cases ((hget dd m) x r)
      = (hget cases m) x (imap (fx cases) r).

  (** As for [datatypeDenoteOk], we consider all constructors and all possible arguments to them by quantifying over [m], [x], and [r].  The lefthand side of the equality that follows shows a call to the recursive function on the specific constructor application that we selected.  The righthand side shows an application of the function case associated with constructor [m], applied to the non-recursive arguments and to appropriate recursive calls on the recursive arguments. *)

End ok.

(** We are now ready to prove that the [size] function we defined earlier always returns positive results.  First, we establish a simple lemma. *)

(* begin thide *)
Lemma foldr_plus : forall n (ils : ilist nat n),
  foldr plus 1 ils > 0.
  induction ils; crush.
Qed.
(* end thide *)

Theorem size_positive : forall T dt
  (dd : datatypeDenote T dt) (fx : fixDenote T dt)
  (dok : datatypeDenoteOk dd) (fok : fixDenoteOk dd fx)
  (v : T),
  size fx v > 0.
(* begin thide *)
  unfold size; intros.
  (** [[
  ============================
   fx nat
     (hmake
        (fun (x : constructor) (_ : nonrecursive x)
           (r : ilist nat (recursive x)) => foldr plus 1%nat r) dt) v > 0
    ]]
      
    Our goal is an inequality over a particular call to [size], with its definition expanded.  How can we proceed here?  We cannot use [induction] directly, because there is no way for Coq to know that [T] is an inductive type.  Instead, we need to use the induction principle encoded in our hypothesis [dok] of type [datatypeDenoteOk dd].  Let us try applying it directly.
    [[
  apply dok.
    ]]
%\vspace{-.3in}%
<<
Error: Impossible to unify "datatypeDenoteOk dd" with
 "fx nat
    (hmake
       (fun (x : constructor) (_ : nonrecursive x)
          (r : ilist nat (recursive x)) => foldr plus 1%nat r) dt) v > 0".
>>

    Matching the type of [dok] with the type of our conclusion requires more than simple first-order unification, so [apply] is not up to the challenge.  We can use the %\index{tactics!pattern}%[pattern] tactic to get our goal into a form that makes it apparent exactly what the induction hypothesis is. *)

  pattern v.
  (** %\vspace{-.15in}%[[
  ============================
   (fun t : T =>
    fx nat
      (hmake
         (fun (x : constructor) (_ : nonrecursive x)
            (r : ilist nat (recursive x)) => foldr plus 1%nat r) dt) t > 0) v
      ]]
      *)

  apply dok; crush.
  (** %\vspace{-.15in}%[[
  H : forall i : fin (recursive c),
      fx nat
        (hmake
           (fun (x : constructor) (_ : nonrecursive x)
              (r : ilist nat (recursive x)) => foldr plus 1%nat r) dt)
        (get r i) > 0
  ============================
   hget
     (hmake
        (fun (x0 : constructor) (_ : nonrecursive x0)
           (r0 : ilist nat (recursive x0)) => foldr plus 1%nat r0) dt) m x
     (imap
        (fx nat
           (hmake
              (fun (x0 : constructor) (_ : nonrecursive x0)
                 (r0 : ilist nat (recursive x0)) => 
               foldr plus 1%nat r0) dt)) r) > 0
    ]]

    An induction hypothesis [H] is generated, but we turn out not to need it for this example.  We can simplify the goal using a library theorem about the composition of [hget] and [hmake]. *)

  rewrite hget_hmake.
  (** %\vspace{-.15in}%[[
  ============================
   foldr plus 1%nat
     (imap
        (fx nat
           (hmake
              (fun (x0 : constructor) (_ : nonrecursive x0)
                 (r0 : ilist nat (recursive x0)) => 
               foldr plus 1%nat r0) dt)) r) > 0
    ]]

    The lemma we proved earlier finishes the proof. *)

  apply foldr_plus.

  (** Using hints, we can redo this proof in a nice automated form. *)

  Restart.

  Hint Rewrite hget_hmake.
  Hint Resolve foldr_plus.
 
  unfold size; intros; pattern v; apply dok; crush.
Qed.
(* end thide *)

(** It turned out that, in this example, we only needed to use induction degenerately as case analysis.  A more involved theorem may only be proved using induction hypotheses.  We will give its proof only in unautomated form and leave effective automation as an exercise for the motivated reader.

   In particular, it ought to be the case that generic [map] applied to an identity function is itself an identity function. *)

Theorem map_id : forall T dt
  (dd : datatypeDenote T dt) (fx : fixDenote T dt)
  (dok : datatypeDenoteOk dd) (fok : fixDenoteOk dd fx)
  (v : T),
  map dd fx (fun x => x) v = v.
(* begin thide *)
  (** Let us begin as we did in the last theorem, after adding another useful library equality as a hint. *)

  Hint Rewrite hget_hmap.

  unfold map; intros; pattern v; apply dok; crush.
  (** %\vspace{-.15in}%[[
  H : forall i : fin (recursive c),
      fx T
        (hmap
           (fun (x : constructor) (c : constructorDenote T x)
              (x0 : nonrecursive x) (r : ilist T (recursive x)) => 
            c x0 r) dd) (get r i) = get r i
  ============================
   hget dd m x
     (imap
        (fx T
           (hmap
              (fun (x0 : constructor) (c0 : constructorDenote T x0)
                 (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) =>
               c0 x1 r0) dd)) r) = hget dd m x r
    ]]

    Our goal is an equality whose two sides begin with the same function call and initial arguments.  We believe that the remaining arguments are in fact equal as well, and the [f_equal] tactic applies this reasoning step for us formally. *)

  f_equal.
  (** %\vspace{-.15in}%[[
  ============================
   imap
     (fx T
        (hmap
           (fun (x0 : constructor) (c0 : constructorDenote T x0)
              (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) =>
            c0 x1 r0) dd)) r = r
    ]]

    At this point, it is helpful to proceed by an inner induction on the heterogeneous list [r] of recursive call results.  We could arrive at a cleaner proof by breaking this step out into an explicit lemma, but here we will do the induction inline to save space.*)

  induction r; crush.

  (* begin hide *)
  (* begin thide *)
  Definition pred' := pred.
  (* end thide *)
  (* end hide *)

  (** The base case is discharged automatically, and the inductive case looks like this, where [H] is the outer IH (for induction over [T] values) and [IHr] is the inner IH (for induction over the recursive arguments).
     [[
  H : forall i : fin (S n),
      fx T
        (hmap
           (fun (x : constructor) (c : constructorDenote T x)
              (x0 : nonrecursive x) (r : ilist T (recursive x)) => 
            c x0 r) dd)
        (match i in (fin n') return ((fin (pred n') -> T) -> T) with
         | First n => fun _ : fin n -> T => a
         | Next n idx' => fun get_ls' : fin n -> T => get_ls' idx'
         end (get r)) =
      match i in (fin n') return ((fin (pred n') -> T) -> T) with
      | First n => fun _ : fin n -> T => a
      | Next n idx' => fun get_ls' : fin n -> T => get_ls' idx'
      end (get r)
  IHr : (forall i : fin n,
         fx T
           (hmap
              (fun (x : constructor) (c : constructorDenote T x)
                 (x0 : nonrecursive x) (r : ilist T (recursive x)) => 
               c x0 r) dd) (get r i) = get r i) ->
        imap
          (fx T
             (hmap
                (fun (x : constructor) (c : constructorDenote T x)
                   (x0 : nonrecursive x) (r : ilist T (recursive x)) =>
                 c x0 r) dd)) r = r
  ============================
   ICons
     (fx T
        (hmap
           (fun (x0 : constructor) (c0 : constructorDenote T x0)
              (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) =>
            c0 x1 r0) dd) a)
     (imap
        (fx T
           (hmap
              (fun (x0 : constructor) (c0 : constructorDenote T x0)
                 (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) =>
               c0 x1 r0) dd)) r) = ICons a r
    ]]

    We see another opportunity to apply [f_equal], this time to split our goal into two different equalities over corresponding arguments.  After that, the form of the first goal matches our outer induction hypothesis [H], when we give type inference some help by specifying the right quantifier instantiation. *)

  f_equal.
  apply (H First).
  (** %\vspace{-.15in}%[[
  ============================
   imap
     (fx T
        (hmap
           (fun (x0 : constructor) (c0 : constructorDenote T x0)
              (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) => 
            c0 x1 r0) dd)) r = r
    ]]

    Now the goal matches the inner IH [IHr]. *)

  apply IHr; crush.
  (** %\vspace{-.15in}%[[
  i : fin n
  ============================
   fx T
     (hmap
        (fun (x0 : constructor) (c0 : constructorDenote T x0)
           (x1 : nonrecursive x0) (r0 : ilist T (recursive x0)) => 
         c0 x1 r0) dd) (get r i) = get r i
    ]]

    We can finish the proof by applying the outer IH again, specialized to a different [fin] value. *)

  apply (H (Next i)).
Qed.
(* end thide *)

(** The proof involves complex subgoals, but, still, few steps are required, and then we may reuse our work across a variety of datatypes. *)

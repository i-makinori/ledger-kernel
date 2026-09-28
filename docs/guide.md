# Ledger Kernel 機能ガイド

README の「できること」で挙げた機能を、1つずつ詳しく説明する文書です。
README を読んで全体像を掴んでから、必要な節だけを読む使い方を想定しています。
コード例は `(in-package :ledger-kernel)` した REPL で実行する前提です。`*L*` には
ライブラリを読み込んだ台帳が入っているものとします（README の「動かしてみる」参照）。
1節の例はペアノ算術の台帳、7〜10節の例は ZF の台帳を想定しています。
4〜6節の例は、それぞれの節の中で台帳を作っています。

## 目次

1. `PROVE-TAUTOLOGY` で恒真式を自動証明する
2. 検証コストが気になったら: `ENABLE-DERIVED-ENTRY-MEMOIZATION`
3. 体系そのものをファイルで定義する: `.system` ファイル
4. 確定記述: `III.3` と `IOTA`
5. 存在除去規則: `EXISTS-ELIM`
6. 保存的拡張としての関数定義: `DEFINE-FUNCTION-BY-DESCRIPTION`
7. 定義された結合子: `00-connectives.system`
8. ZF 集合論: `zf-library/00-zf.system`
9. 空集合: `zf-library/01-empty-set.ledger`
10. 述語スキーマ変数「A(x)」: `07-quantifier-schemas.ledger`
11. Web UI
12. 設計上の細かな要点
13. 束縛変数の de Bruijn 表現（マシン B）

## 1. `PROVE-TAUTOLOGY` で恒真式を自動証明する

`.to`（→）と `.neg`（¬）だけで書いた式なら、恒真式かどうかを真理表でチェックし、
本当に恒真式ならその場で Hilbert 証明を自動生成して台帳に登録してくれます。

```lisp
;; パースの法則 ((A->B)->A)->A を自動証明
(defparameter *peirce* '(.to (.to (.to A B) A) A))
(setf *L* (prove-tautology *L* *peirce* 'th-peirce))

(check-k-proof '((0 (.to (.to (.to A B) A) A) :th (th-peirce))) *L*)
;=> T
```

`00-connectives.system` を読み込んでいれば、∧ `.and`・∨ `.or`・↔ `.iff` を含む
式もそのまま扱えます（展開形を通して FOLD／UNFOLD 公理で証明を組み立てます）。
また、`.to`/`.neg`/`.and`/`.or`/`.iff` 以外の部分論理式はすべて原子として扱うので、
`(.in v0 v1)` や `(.forall v0 A)` を含む式でも、命題論理の構造だけで成り立つもの
なら証明できます。

```lisp
(setf *L* (prove-tautology *L* '(.iff (.neg (.and A B)) (.or (.neg A) (.neg B))) 'th-de-morgan))
```

証明の途中で使う補助エントリは `NAME.T1`, `NAME.F1`, ..., `NAME.CONTRA` という
名前で台帳に登録されます（ファイルに書き出して読み戻せるよう、決定的な名前に
しています）。

恒真式でないものを渡すと、証明を作らずにその場でエラーになります（安全側）。

```lisp
(prove-tautology *L* '(.to A B) 'th-bad)
;=> ERROR: PROVE-TAUTOLOGY: (.TO A B) is FALSE under ((A . T) (B)) -- not a tautology, refusing.
```

途中経過を見たいときは、最後の引数に `LOG-CONFIG` を渡すと行ごとの accept/reject
が表示されます。

```lisp
(prove-tautology *L* *peirce* 'th-peirce2 (make-log-config :errors t :applications t))
```

## 2. 検証コストが気になったら: `ENABLE-DERIVED-ENTRY-MEMOIZATION`

このカーネルは `TH`/`TH-DED` の引用を一切キャッシュせず、
引用のたびに格納された証明を毎回ゼロから展開・再検証します（LCF流の
"always re-verify" を徹底するための、意図的な設計）。ただし「同じ補題を
何度も多重引用する」パターン（例えばケース分割タクティクのように、1階層
下がるごとに前段の結果を2回使う、といった構成）に対しては、これが階層の
深さに対して**指数的**なコストになります。

この再検証は本質的には `(そのエントリ, 具体化された束縛)` の組だけで決まる
純粋な計算（同じ組を渡せば必ず同じ結果になる）なので、そこだけを覚えておく
のは健全です -- 何が受理されるかを一切変えず、同じ計算を繰り返さないだけ
です。デフォルトはOFFで、通常の使用や `RUN-*-SELF-TESTS` は全部「毎回
ゼロから再検証」の元の挙動のままです。試したいときだけ:

```lisp
(enable-derived-entry-memoization)   ; 以後、(エントリ . 束縛) 単位でキャッシュ
;; ... 重い証明のチェックなど ...
(disable-derived-entry-memoization)  ; 元の挙動に戻す
```

命題論理だけで組んだ「1階層ごとに前段を2回引用する」塔（`.exists`も
量化子も一切登場しない）で試すと、OFFのままだと深さ16で0.15秒、深さ20は
2秒超え、深さ30台後半で現実的でなくなりますが、ONにすると深さ60（何も
しなければ 2^60 相当の作業量）でも一瞬で終わります。詳しくは
`src/k-proof.lisp` の「Optional memoization」節（`TRY-DERIVED-ENTRY` の
直前）と `tests/memoization-tests.lisp` の `TEST-DERIVED-ENTRY-MEMOIZATION` を
参照してください。

## 3. 体系そのものをファイルで定義する: `.system` ファイル

`.ledger` ファイルは、**すでに存在する体系**の上で**証明された定理**を記述
するものです。その体系そのもの（公理・推論規則・形成規則）は、`.system`
ファイルだけで定義されます。カーネルのLispソースに論理は埋め込まれていません
-- 別の体系を試したければ `.system` ファイルを書けば済みます。

`.system` ファイルの中身はただのデータです。公理は
`(名前 側条件 (追加引数パターン 結論パターン))`、推論規則は
`(名前 側条件 (前提パターン 追加引数パターン :=> 結論パターン))`、
形成規則も同じ形で書きます。読み込みには
`(bootstrap-kernel-from-spec-file PATH &key ledger)` を使い、`:ledger` を渡すと
その台帳の上に積み増します。

```lisp
;; 例: K/S だけの、.neg も量化子もない最小の含意論理を、Lispを一切
;; 書かずにファイルだけで定義する
(:wff-formation wff_to? ((wff? ?A) (wff? ?B)) (wff? (.to ?A ?B)))
(:irule MP ((wff? ?A) (wff? ?B)) (((.to ?A ?B) ?A) nil :=> ?B))
(:axiom K ((wff? ?A) (wff? ?B)) (nil (.to ?A (.to ?B ?A))))
(:axiom S-COMB ((wff? ?A) (wff? ?B) (wff? ?C))
  (nil (.to (.to ?A (.to ?B ?C)) (.to (.to ?A ?B) (.to ?A ?C)))))
```

```lisp
(defparameter *mini* (bootstrap-kernel-from-spec-file "demo.system"))
(check-k-proof '((0 (.to A (.to B A)) :axiom (K))) *mini*)
;=> T
;; K+S だけから A->A を（教科書通りSKKで）実際に導出できる
;; ... (5行のHilbert証明) ...
;; この体系には .NEG が一度も定義されていないので、本当に存在しない:
(judgement? 'wff? '(.neg A) *mini*)
;=> NIL
```

`hilbert-library/00-classical-fol-equality.system` + `00-peano-arithmetic.system`
は、このカーネルが標準で使っている体系（II.1-4/III.1-2/IV.1-4 + ペアノ算術）
を定義する `.system` ファイルです。

```lisp
(defparameter *L*
  (bootstrap-kernel-from-spec-file "hilbert-library/00-peano-arithmetic.system"
    :ledger (bootstrap-kernel-from-spec-file "hilbert-library/00-classical-fol-equality.system")))
```

**ここが `.ledger` ファイルと決定的に違う点です。** `.ledger` ファイルの
定理は読み込むたびに `CHECK-K-PROOF` が**独立に再検証**するので、壊れた
ファイルや悪意あるファイルは「読み込みに失敗する」以上のことができません
（本物でない定理を紛れ込ませることは原理的にできない）。`.system` ファイル
は違います。ここで定義されるのは `ORIGIN = :PRIMITIVE`（=無条件に信頼される)
エントリで、何と照合して確認するということが原理的にできません。つまり
`.system` ファイルを読み込むのは「検証」ではなく、**その作者を信頼する行為**
そのものです。矛盾した公理系（`A` とその否定が両方証明できてしまう、
など）を書いてしまえば、それを体系の内側から検出することは原理的にできま
せん（ゲーデルの第二不完全性定理そのものであって、このチェッカーの欠陥では
ありません）。

側条件・パターンの中では `wff?`/`var?`/`term?` および既存のメタ述語・メタ
構成子（`@subst`, `@subst-ok?`, `@not-free-in?`, `@not-free-in-dependencies?`
等）を名前で自由に使えます -- これらは固定された閉じたカタログで、
`.system` ファイルは「この語彙を組み合わせて新しい体系を組み立てる」ことは
できますが、**新しいメタ述語自体を追加することはできません**（それは
Lispソースレベルの拡張です）。それでも、命題論理の別の公理基底、様相
論理の `.box`/`.diamond` のような新しい結合子と規則、といったものはこの
仕組みだけで十分表現できるはずです。


## 4. 確定記述（definite description）: `III.3` と `IOTA`

「Aを満たすxが存在し、しかもそれは一意である」ときに、その唯一のxを直接
指し示す項 `(.iota x A)`（"the x such that A"）を用意しました。

これがなぜ簡単ではないか、という点から説明します。既存の `.forall`/
`.exists` は**WFFを作る**束縛子でしたが、`.iota` は**項を作る**束縛子です。
このカーネルでは束縛子が新しい種類の値（WFFではなくTERM）を作るということ
自体がここだけで、`BINDER-HEADS`（束縛変数を de Bruijn インデックスに直す
変換や、束縛子を開く処理が「この頭部は束縛子である」と認識するための
Lispソース側のリスト。13節）に `.IOTA` を追加するという、`.system` ファイルだけ
では完結しないLispソースレベルの変更が必要でした（既存の非束縛子な結合子・
関係はデータ駆動で拡張できるのに対し、束縛子の追加はこの一点だけ例外です）。

`IOTA` は**公理ではなく推論規則（IRULE）**です。MP/Genと同じく、証明中の
既存の行（プレミス）を引用する必要があるからです：

- **存在**: `(.exists x A)`
- **一意性**: `(.forall y (.forall z (.to A[y/x] (.to A[z/x] (.eq y z)))))`
  （カーネルの基本結合子に ∧ はないので、カリー化した形で書く: 「y も z も A を
  満たすなら y=z」）

この2つを両方引用して初めて、`A[(.iota x A)/x]`（iota項自体がAを満たす）
が結論できます。存在論のごまかしをしない — **具体的な証人を要求しない**
（非構成的な存在証明で構わない）一方で、**一意性が示せない限りIOTAは絶対に
適用できない**（=一意でない場合の「値」を勝手に決める、というような
junk-valueの規約は一切ない）というのが設計上の要点です。

存在証明を可能にするために、`III.3`（存在汎化、`A[t/x] -> exists x. A`）
があります。III.1（全称除去）の双対で、Gen（全称汎化）と違って自由変数
条件は不要（「特定の証人tがAを満たす」から「Aを満たす何かが存在する」への
移行は無条件に健全）です。ただし III.3 の引数は `(III.3 x A t)` の3つで、
III.1 の `(III.1 t)` と違って `x` と `A` も明示的に渡す必要があります。これ
は `MATCH-TEMPLATE` がパターンを左から右に処理する制約から来ています:
III.1 は `(.forall x A) -> A[t/x]` で、前件の `.forall` 構造から `x`/`A`
が先に構造的に確定してから後件の `@subst` が評価されますが、III.3 は
`A[t/x] -> exists x. A` で前件・後件が逆転しており、前件の `@subst` に
到達した時点では `x`/`A` がまだ未確定（後件の `.exists x A` でしか構造的
に確定しない）ため、Genの `x` 引数と同様に外から明示的に渡す設計にして
います。

具体例（`v1=v1` から `exists v0(v0=v1)` を経て `(.iota v0 (v0=v1)) = v1`
まで）:

```lisp
(defparameter *L* (bootstrap-kernel-from-spec-file "hilbert-library/00-classical-fol-equality.system"))
;; 存在: exists v0 (v0=v1)
(setf *L* (check-and-extend *L* 'th 'th-exists-v0-eq-v1
  '((0 (.eq v1 v1) :axiom (IV.1))
    (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))
    (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))))
;; 一意性: forall v2 forall v3 (v2=v1 -> (v3=v1 -> v2=v3))  (uniq-full。
;; 導出は 05-classical-logic.ledger の TH-RAA と同じ多段階の
;; deduction-theorem-direct 連鎖 -- 詳細は tests/iota-tests.lisp 参照)
;; ...
;; IOTA適用: (iota v0 (v0=v1)) = v1
(check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                  (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                  (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 1)))
                *L*)
;=> T
```

**補足**:

- `.iota x A` を使うたびに存在と一意性を引用し直すのが煩わしい場合は、
  `DEFINE-FUNCTION-BY-DESCRIPTION`（6節）で名前の付いた関数記号として定義できます。
- 存在からの除去方向の規則は `EXISTS-ELIM`（5節）です。
- 一意性が示せない場合の「値」についての規約（古典的な確定記述理論でよく
  ある total function 化のための junk value）は用意していません。単に
  IOTAが適用できないだけです。


## 5. 存在除去規則: `EXISTS-ELIM`

III.3（存在汎化）は `A[t/x] → ∃x.A` という**導入**方向の規則です。
`EXISTS-ELIM` はその逆——`∃x.A` という証明済みの事実から、実際に「その証人を仮に
名付けて」議論を進める**除去**方向の規則で、Mendelson の Rule C 相当の genuine な
存在除去規則です。

```lisp
;; ∃x.A と (A[w/x] -> C) の両方から C を結論する。w は:
;;   - A にも C にも自由に出現していない（除去した瞬間に消える「仮の名前」）
;;   - 現在開いている仮定（Γ）のどれにも自由に出現していない
;; という新鮮さ（freshness）条件を満たす必要があり、これらはすべて機械的に
;; 検査されます。
(check-k-proof '((0 (.exists v0 (.eq v0 v1)) :hyp nil)
                  (1 (.to (.eq v2 v1) (.eq v1 v1)) :hyp nil)   ; A[w/x] -> C, w=v2
                  (2 (.eq v1 v1) :ir (EXISTS-ELIM 0 1 v2)))
                *L*)
```

`.to ?Ac ?C` という2番目の前提パターンで `?Ac` を構造的にだけ束縛し、それが
本当に `A[w/x]` と等しいことを、束縛が全部揃った後の副条件 `@substitutes?` で
別途検査する、という2段構えになっています（内部のマッチングエンジンは「前提
パターンをすべて先に処理してから追加パラメータを処理する」という順序なので、
`w` がまだ未確定の段階で `A[w/x]` を前提パターンの中に埋め込むことはできない
——この制約を回避するための設計です）。

**注意点**: `w` として使える変数は呼び出し側が選ぶため、新鮮さの検査を通過する
変数を選ぶ責任は引用側にあります（これは Gen の `@not-free-in-dependencies?`
と全く同じ立て付けです）。


## 6. 保存的拡張としての関数定義: `DEFINE-FUNCTION-BY-DESCRIPTION`

`IOTA`（4節）は「存在して一意」という性質から `.iota x A` という**項**を作れる
ようにする規則でしたが、使うたびに existence/uniqueness 定理を毎回引用し直す
必要があり、`(.iota v0 (.eq v0 (+ v1 v1)))` のような式は読みにくく、名前も
付きません。`DEFINE-FUNCTION-BY-DESCRIPTION` は、この「存在して一意」という
性質から、代わりに**新しい関数記号そのもの**を1回だけ鋳造する定義機構です。

```lisp
;; 前提: 「すべてのxについて、y=x+xとなるyが存在する」(existence) と
;;       「そのyは一意である」(uniqueness) の両方をすでに証明済みとする。
(setf *L*
  (define-function-by-description *L* 'double
    '(v0)                                    ; 引数変数（1引数）
    'v1 'v2                                  ; 出力変数と、一意性用の2つめの変数
    '(.eq v1 (+ v0 v0))                      ; 定義性質 A(x,y) := y=x+x
    'th-double-existence 'th-double-uniqueness))

;; 以後 (double v0) は普通の項として使え、定義公理 DOUBLE-DEF を
;; 引用するだけで DOUBLE(x)=x+x が使える（IOTAを経由する必要がない）
(check-k-proof '((0 (.eq (double v0) (+ v0 v0)) :axiom (double-def))) *L*)
;=> T
```

内部では、渡された EXISTENCE/UNIQUENESS の定理名が実際に「期待した形の
existence/uniqueness 命題」を証明しているかどうかを、`check-k-proof` による
1行の `:th` 引用として再構成・再検証した上で、新しい項形成規則（n引数の関数
記号）と、無条件に `A(x1..xn, NAME(x1..xn))` を主張する定義公理を
`bootstrap-kernel-from-spec` 経由で鋳造します。

**正直な限界**: これは「existence+uniquenessが与えられればdefinition-by-
descriptionは保存的拡張である」というメタ定理そのものを本カーネル内で形式的に
証明しているわけではありません。あくまで、その前提（existence/uniqueness）が
本当に主張通りの形で証明済みであることを機械的に**チェック**した上で、
（メタ理論としては正しいと知られている）鋳造を実行しているだけです。この
チェックとメタ定理自体の証明との間のギャップは、`.system` ファイルを読み込む
ときの信頼と同じ種類のものです。

**`.ledger` ファイルへの保存**: 定義は、次のコマンドとして `.ledger` ファイルに
書けます（`write-ledger-to-file` もこの形で書き出します）。読み込むときは
`DEFINE-FUNCTION-BY-DESCRIPTION` そのものを呼び直すので、existence／uniqueness
の再チェックも毎回行われます。

```lisp
(:define-function-by-description NAME ARG-VARS Y-VAR Y2-VAR A-FORMULA
                                 EXISTENCE-NAME UNIQUENESS-NAME)
```

## 7. 定義された結合子: `hilbert-library/00-connectives.system`

カーネルの基本結合子は `.to`（→）と `.neg`（¬）だけです。∧・∨・↔・∃! は、
形成規則と、展開形と行き来する2つの定義公理（UNFOLD／FOLD）の組として
`.system` ファイルで定義しています。

| 記号 | 意味 | 展開形 | 定義公理 |
|---|---|---|---|
| `(.and A B)` | A ∧ B | `(.neg (.to A (.neg B)))` | `AND-UNFOLD` / `AND-FOLD` |
| `(.or A B)` | A ∨ B | `(.to (.neg A) B)` | `OR-UNFOLD` / `OR-FOLD` |
| `(.iff A B)` | A ↔ B | `(.and (.to A B) (.to B A))` | `IFF-UNFOLD` / `IFF-FOLD` |
| `(.exists1 x A)` | ∃!x A | `(.exists x (.and A (.forall u (.to A[u/x] (.eq u x)))))` | `EXISTS1-UNFOLD` / `EXISTS1-FOLD` |

`EXISTS1-*` の u は、x と異なり、A に自由出現せず、A の x に代入可能な任意の
変数です（引用する式の中で自分で選びます）。

カーネルの照合は字面どおりなので、`(.and A B)` と展開形は別の式として扱われます。
証明の中では、UNFOLD／FOLD の公理と MP で明示的に行き来します。

```lisp
;; ∧除去: (.and A B) ⊢ A
((0 (.and A B) :hyp nil)
 (1 (.to (.and A B) (.neg (.to A (.neg B)))) :axiom (and-unfold))
 (2 (.neg (.to A (.neg B))) :ir (MP 1 0))
 (3 (.to (.neg (.to A (.neg B))) A) :th (...))   ; PROVE-TAUTOLOGY で作った定理
 (4 A :ir (MP 3 2)))
```

**カーネルへの変更（1行）**: `.exists1` は変数を束縛するので、自由変数の判定や
代入でその変数を束縛変数として扱う必要があります。束縛子の一覧
（`src/ledger.lisp` の `BINDER-HEADS`）はカーネルのコードに固定されていて、
`.system` ファイルからは足せないため、ここに `.exists1` を1語追加しています。
形成規則と意味（定義公理）は、すべて `.system` ファイル側にあります。

∧ ∨ ↔ の基本補題は `hilbert-library/06-connectives.ledger` にまとめてあります
（`th-and-intro`, `th-and-elim-l/r`, `th-or-intro-l/r`, `th-or-elim`,
`th-iff-intro`, `th-iff-mp/mpr`, `th-iff-refl/sym/trans`, `th-not-and`,
`th-not-or`, `th-excluded-middle`, `th-contrapositive` など）。このファイルは
`tools/generate-connectives-ledger.lisp` が `PROVE-TAUTOLOGY` で生成したもので、
読み込むときには他の `.ledger` と同じく全証明が再検証されます。

∃! や量化子についての補題（∃!x P(x) → ∃x P(x) など）は、述語スキーマ変数を
使って `hilbert-library/07-quantifier-schemas.ledger` にまとめてあります
（10節）。

## 8. ZF 集合論: `zf-library/00-zf.system`

一階述語論理 + 等号の体系と、定義された結合子の上に、ZF 集合論（選択公理なし）を
積むための `.system` ファイルです。

```lisp
(defparameter *ZF*
  (bootstrap-kernel-from-spec-file
    "zf-library/00-zf.system"
    :ledger (bootstrap-kernel-from-spec-file
              "hilbert-library/00-connectives.system"
              :ledger (bootstrap-kernel-from-spec-file
                        "hilbert-library/00-classical-fol-equality.system"))))
```

**言語**: 新しく加わる記号は二項述語 `(.in s t)`（s ∈ t）だけです。∈ についての
等号の代入則は、任意の論理式についての図式である IV.2 がそのまま担います。

**公理**（引用名と内容）: ファイル中でも、∧ ∨ ↔ ∃! を `.and` `.or` `.iff`
`.exists1` で書いているので、教科書の形とほぼそのまま対応します。

| 引用名 | 内容 |
|---|---|
| `ZF-EXTENSIONALITY` | ∀x ∀y ( ∀z (z∈x ↔ z∈y) → x = y ) |
| `ZF-PAIRING` | ∀x ∀y ∃z ∀w ( w∈z ↔ (w = x ∨ w = y) ) |
| `ZF-UNION` | ∀x ∃y ∀z ( z∈y ↔ ∃w (w∈x ∧ z∈w) ) |
| `ZF-POWER-SET` | ∀x ∃y ∀z ( z∈y ↔ ∀w (w∈z → w∈x) ) |
| `ZF-INFINITY` | ∃x ( ∃y (y∈x ∧ ∀z ¬(z∈y)) ∧ ∀y (y∈x → ∃z (z∈x ∧ ∀w (w∈z ↔ (w∈y ∨ w = y)))) ) |
| `ZF-FOUNDATION` | ∀x ( ∃y (y∈x) → ∃y (y∈x ∧ ¬∃z (z∈y ∧ z∈x)) ) |
| `ZF-SEPARATION` | ∀x ∃y ∀z ( z∈y ↔ (z∈x ∧ φ) )　（y は φ に自由出現しない） |
| `ZF-REPLACEMENT` | ∀a ( ∀x (x∈a → ∃!y φ) → ∃b ∀x (x∈a → ∃y (y∈b ∧ φ)) )　（b は φ に自由出現しない） |

**変数の扱い**: 各公理の束縛変数はスキーマ変数（`?x` など）なので、証明中で
使っている任意の変数名でそのまま引用できます。その
代わり、束縛変数どうしが**互いに異なる**ことを側条件として要求します
（Metamath の distinct variable 条件に相当）。これがないと、たとえば外延性公理で
z := x とすると ∀x ∀y (∀x (x∈x ↔ x∈y) → x = y) という別の（健全でない）主張に
なってしまうためです。（13節の de Bruijn 表現では、パターンの束縛変数は照合の
たびに互いに異なる新しい変数で開かれるので、これらの側条件は常に満たされます。
それでも公理の意味を明示するために残しています。）

```lisp
;; 外延性公理を v3, v5, v4 で引用する
(check-k-proof '((0 (.forall v3 (.forall v5 (.to (.forall v4 (.iff (.in v4 v3) (.in v4 v5)))
                                                   (.eq v3 v5))))
                   :axiom (zf-extensionality)))
               *ZF*)
;=> T
```

`hilbert-library/` の `01`〜`03`, `05` の `.ledger`（命題論理・述語論理・等号・
古典論理の定理）は、この ZF 台帳の上にもそのまま積めます（`04` はペアノ算術用
なので対象外です）。

**注意**: `.system` ファイルなので、ここに書かれた公理はすべて `:PRIMITIVE`
（無条件に信頼される）です。公理の書き写しの正しさは、教科書どおりの形から
独立に組み立てた式で各公理を引用できること、および側条件に反する引用が拒否
されることを `tests/zf-tests.lisp` で確認しています。


## 9. 空集合: `zf-library/01-empty-set.ledger`

ZF の上に作った最初の定理ライブラリです。読み込み順は次のとおりです。

```lisp
(defparameter *ZF-EMPTY*
  (flet ((lib (f l) (read-ledger-from-file f :ledger l)))
    (lib "zf-library/01-empty-set.ledger"
     (lib "hilbert-library/06-connectives.ledger"
      (lib "hilbert-library/05-classical-logic.ledger"
       (lib "hilbert-library/03-equality-core.ledger"
        (lib "hilbert-library/02-predicate-core.ledger"
         (lib "hilbert-library/01-propositional-core.ledger"
          (bootstrap-kernel-from-spec-file "zf-library/00-zf.system"
           :ledger (bootstrap-kernel-from-spec-file "hilbert-library/00-connectives.system"
                    :ledger (bootstrap-kernel-from-spec-file
                             "hilbert-library/00-classical-fol-equality.system")))))))))))
```

| 名前 | 内容 |
|---|---|
| `th-zf-empty-exists` | ∃y ∀z ¬(z ∈ y)　（分出公理を φ := ¬(z = z) で使う） |
| `th-zf-empty-unique` | ∀y ∀y′ ( ∀z ¬(z ∈ y) → (∀z ¬(z ∈ y′) → y = y′) )　（外延性公理） |
| `empty` / `EMPTY-DEF` | 定数 ∅ を `(empty)` と書く。定義公理 ∀z ¬(z ∈ ∅) |
| `th-zf-not-in-empty` | ¬(x ∈ ∅) |

`(empty)` は `DEFINE-FUNCTION-BY-DESCRIPTION` で定義した0引数の関数記号です。
上の存在定理と一意性定理が、期待どおりの形をしていることが再チェックされた上で
定義されます。

```lisp
(check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty))) *ZF-EMPTY*)
;=> T
```


## 10. 述語スキーマ変数「A(x)」: `07-quantifier-schemas.ledger`

原子記号 A, B, ... は「任意の論理式」の代わりになりますが、変数 x に依存する
「A(x)」の代わりにはなりません。そこで、引数を取る**述語スキーマ記号**を宣言
できるようにしています。

```lisp
(:declare-predicate-schema-symbol p 1)   ; .ledger ファイルの中で
(declare-predicate-schema-symbol *L* 'p 1)  ; Lisp から
```

宣言すると、任意の項 t について `(p t)` が論理式になります。定理の中の `(p v0)` は
「v0 を含む任意の論理式」を表し、引用するときに具体的な論理式が代入されます。
`(p v0)` では v0 が自由変数として見えるので、Gen や EXISTS-ELIM の側条件も
正しく働きます。

**引用のしかた**: 引数が相異なる変数の箇所（`(.forall v0 (p v0))` など）から、
代入する論理式は自動で決まります。

```lisp
;; th-forall-elim: ∀x P(x) → P(v1)。P := (v0 ∈ v3) が自動で決まる
((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3)) :th (th-forall-elim)))
```

自動で決まらない場合や、定理の中の変数を置き換えたい場合は、引用の最後に
`:inst` で明示します。

```lisp
(th-forall-elim :inst ((v1 (empty))))            ; 変数 v1 を項 (empty) に置き換え
(th-forall-mono :inst ((p (v3) (.in v3 v1))       ; P := λv3. v3 ∈ v1
                       (q (v3) (.in v3 v2))))     ; Q := λv3. v3 ∈ v2
(th-exists1-exists :inst ((v4 v3)))               ; 補題内部の変数 v4 を v3 に
```

| `:inst` の要素 | 意味 |
|---|---|
| `(A 論理式)` | 原子記号 A にその論理式を代入 |
| `(P (x1 .. xn) 本体)` | 述語スキーマ P に λx1..xn. 本体 を代入 |
| `(v0 項)` | 定理の証明全体で変数 v0 をその項に置き換え |

**健全性の仕組み**: 引用されるたびに、定理の保存された証明に代入を施し、
(1) その証明の仮定と結論が、引用している行・前提と**完全に一致する**こと、
(2) 代入後の証明全体が**最初から再検証を通る**こと、の2つを確認します。
代入を見つける照合の処理は、正しい引用を見逃すことはあっても、誤った引用を
通すことはありません。照合をわざと壊しても誤った引用が通らないことを
テストで確認しています。変数の捕獲が起きる代入（たとえば、補題の内部で使って
いる証人変数 v4 を含む論理式を P に入れる）は、再検証で拒否されます。その場合は
`:inst` で補題内部の変数を別の名前に移せば使えます。

**収録している補題**（P, Q は1引数の述語スキーマ）:

| 名前 | 内容 |
|---|---|
| `th-forall-elim` | ∀x P(x) → P(t) |
| `th-exists-intro` | P(t) → ∃x P(x) |
| `th-forall-mono` | ∀x (P(x) → Q(x)) → (∀x P(x) → ∀x Q(x)) |
| `th-exists-mono` | ∀x (P(x) → Q(x)) → (∃x P(x) → ∃x Q(x)) |
| `th-exists1-exists` | ∃!x P(x) → ∃x P(x) |
| `th-exists1-unique` | ∃!x P(x) → (P(y) → (P(y′) → y = y′)) |

**後から定義した記号も使える**: 定理を引用して再検証するとき、公理・推論規則・
定理はその定理より前に登録されたものしか使えません（循環を防ぐため）。一方、
記号の宣言と形成規則（何が論理式・項か）は、後から追加されたものも見えます。
これにより、たとえば論理の補題を、後で定義した `(empty)` を含む論理式に対して
使えます。形成規則は「何が式か」を決めるだけで何も証明しないので、健全性には
影響しません。


## 11. Web UI（ブラウザで閲覧・検証する）

ライブラリの定義・公理・定理をブラウザで眺め、証明を表や証明図（横線の図）で
表示し、エディタに書いた証明をその場で検証できます。Web UI はカーネルの外側に
あり、台帳を読むことと `check-k-proof` を呼ぶことしかしません。

**必要なライブラリ**: Hunchentoot と yason（Quicklisp なら
`(ql:quickload '(:hunchentoot :yason))`、Debian/Ubuntu なら
`apt install cl-hunchentoot cl-yason`）。カーネル本体（`ledger-kernel`）は
これらに依存しません。

**起動**（リポジトリのルートで）:

```bash
sbcl --load tools/serve.lisp          # http://127.0.0.1:8080/
PORT=9000 sbcl --load tools/serve.lisp
```

REPL からなら:

```lisp
(asdf:load-system :ledger-kernel/web)
(ledger-kernel:start-web-server :port 8080)   ; 止めるときは (ledger-kernel:stop-web-server)
```

起動時に、各「世界」のライブラリを読み込みます（すべての証明が再検証されます）。

| 世界 | 内容 |
|---|---|
| ZF set theory | 一階述語論理 + 結合子 + ZF、hilbert-library 01〜03, 05〜07、zf-library 01 |
| Peano arithmetic | 一階述語論理 + ペアノ算術、hilbert-library 01〜05 |

**画面**:
- **ライブラリ**: 左の一覧（種類での絞り込み・検索、読み込んだファイルごとに
  区切り）から選ぶと、右に主張（前提 ⊢ 結論）と証明が出ます。証明は「表」
  （行ごとの式と根拠）と「証明図」（引用した行を横線の上に並べた図）で
  切り替えられます。証明図の横線をクリックするとその上を折りたたみ／展開できます。
- **リンクで辿る**: 規則名・定理名（証明図の横線の横、表の根拠欄、エディタの結果）と、
  式の中の記号（変数、∈ や → などの演算子、∅ などの定義された記号）はリンクに
  なっていて、クリックすると引用先・導入元のエントリが**新しいタブ**で開きます。
  開いた先でも同じように辿れるので、定義や補題を再帰的に遡れます。記号のリンク先は、
  変数・命題記号・述語スキーマならその宣言、演算子・述語・関数記号なら形成規則、
  `DEFINE-FUNCTION-BY-DESCRIPTION` で定義した記号（∅ など）なら定義公理です。
  URL は `#zf/345` のように世界とエントリ番号を含むので、そのまま共有できます。
- **依存関係**: 各エントリのページに、次の2つを表示します。
  - **依存している基礎**: その定理が最終的に依存している公理（読み込んだファイルごと）、
    定義（`DEFINE-FUNCTION-BY-DESCRIPTION` の定義公理）、推論規則。途中で演繹定理を
    メタ定理として信頼した定理（`th-ded`）を使っていれば、その旨も示します。定義は、
    その存在定理・一意性定理が依存しているものにも依存するものとして数えます
    （例: `¬(x ∈ ∅)` は ∅ の定義を通じて分出公理と外延性公理に依存）。
  - **このエントリを使っている定理**: 直接引用している定理の一覧と、間接的なものを
    含めた件数。途中の補題（`名前.t5`、`名前-s1` など）から使われている場合は、
    その補題を使っている定理として数えるので、件数が証明の内部構造で水増しされません。
- **エディタ**: 証明を S 式で書き「検証」（Ctrl+Enter）を押すと、選んでいる
  世界の台帳に対して検証します。受理された行・最初に拒否された行・未検証の行が
  色分けされ、表と証明図で確認できます。検証するだけで、台帳には何も追加しません。
  ライブラリで「エディタで開く」を押すと、その定理の証明が入ります。

**API**（すべて JSON）:

| メソッド | パス | 内容 |
|---|---|---|
| GET | `/api/worlds` | 世界の一覧 |
| GET | `/api/entries?world=zf` | 世界の全エントリ（要約） |
| GET | `/api/entry?world=zf&k=345` | 1つのエントリ（証明の各行、引用先を含む） |
| POST | `/api/check` | `{"world": "zf", "proof": "((0 ...) ...)"}` を検証 |

**安全性**: サーバーは既定で 127.0.0.1 にだけ接続を受け付けます。
`/api/check` は受け取った文字列を `*read-eval*` を切った状態で読み（`#.` による
コード実行はできません）、長さと検証時間（20秒）に上限を設けています。ただし
読み込みの際に記号が作られるので、外部に公開する場合はさらに制限を加えてください。

**テスト**: `(asdf:test-system :ledger-kernel/web)`（表示と API。HTTP は使いません）。


## 12. 設計上の細かな要点

- **エントリの種類**: `atomic-wff-symbol` / `variable-symbol` /
  `predicate-schema-symbol`（語彙）、`term?` /
  `wff?`（形成規則）、`irule`（推論規則, MP/Gen）、`axiom`、`th`（定理、
  閉じた証明）、`th-ded`（演繹定理を信頼して直接離脱で作った定理）。
- **`th-ded` の健全性**: `A ⊢ B` から `A → B` を作るとき、証明中に残っている
  他の未放棄の仮定（Γ）は、引用時にちゃんと citable な前提として要求されます
  （これを落とすと `(C→D)→D` のような偽の「定理」を認めてしまいます）。
- **削除した機能**: 以下は `src/` から外し、元のコード・テスト・復元手順とともに
  `backup/` に移しました（一覧は `backup/README.md`）。束縛変数の付け替えは
  `:inst ((v0 v1))` による引用時の置き換え（10節）で代替できます。
  - 束縛変数の付け替え: `backup/_backup_alpha-conversion.lisp`
  - 帰納的述語の定義機構: `backup/_backup_inductive.lisp`, `backup/_backup_meta-unused.lisp`
  - 証明を変換する演繹定理: `backup/_backup_deduction-transform.lisp`
  - 略記定義などの旧エントリ種別: `backup/_backup_ith-def-abbrev.lisp`
- **II.4 の位置づけ**: `II.1〜II.3`（Łukasiewicz の3公理）だけで古典論理として
  完全ですが、そこから ¬¬除去等を導く最短証明は数十ステップ級になるため、
  実用性を優先して `II.4`（ケース分割）を独立公理として追加しています。これは
  IV.3/IV.4 や P8-P10（導出不可能性を証明した上で追加）とは違い、「導出可能だが
  実際には導出していない」ことをコード中のコメントで明記しています。
- **`PROVE-TAUTOLOGY` の仕組み**: Kalmar の補題（各部分論理式について、その
  真理値に応じた符号付き形が、原子論理式の符号付き仮定から証明できる）を構造
  帰納法で構成し、`II.4` によるケース分割で全ての仮定を1つずつ消去して閉じた
  定理にする、という教科書的な完全性証明をそのままコードにしたものです。


## 13. 束縛変数の de Bruijn 表現（マシン B）

カーネルの内部では、束縛変数に名前がありません。束縛子は `(Q 本体)` の2要素で
書き、束縛変数の出現は `(:bv n)` で表します。n は、その出現から自分を束縛する
束縛子までに挟まっている束縛子の数（de Bruijn インデックス、最も近いものが 0）です。

| 書いた式 | カーネルの中 |
|---|---|
| `(.forall v0 (.forall v1 (.eq v0 v1)))` | `(.forall (.forall (.eq (:bv 1) (:bv 0))))` |
| `(.forall v3 (.forall v2 (.eq v3 v2)))` | 同上 |
| `(.exists v0 (.eq v0 v1))` | `(.exists (.eq (:bv 0) v1))` |

**何が変わるか**

- **α同値な式は同じ値です。** 仮定・結論の一致、MP の前件の一致、メモ化の鍵など、
  カーネルの比較はすべて束縛変数の付け替えを無視して行われます。
  `(.forall v0 P)` を仮定して `(.to (.forall v3 P) B)` と MP しても通ります。
- **代入は捕獲を起こしえません。** 束縛変数は記号ではないので、自由変数を項で
  置き換えるのは記号の単純な置き換えで済み、束縛子に捕まる記号がありません。
  そのため、名前付きの版では拒否していた「束縛変数の付け替えが必要な代入」も
  そのまま通ります。たとえば III.1 で
  `∀v1 ∃v0 ¬(v0 = v1) → ∃v2 ¬(v2 = v0)` は正しい例として受理され、捕獲された
  `→ ∃v0 ¬(v0 = v0)` は拒否されます。
- **自由変数は名前のままです。** 固定された任意の対象、証人、定理の引数などとして
  意味を持つので、付け替えません。

**いつ変換するか**

書かれた式は、カーネルに入るところで一度だけ変換します（`CHECK-K-PROOF`,
`CHECK-AND-EXTEND`, `CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT`, `JUDGEMENT?`）。
変換は冪等なので、すでに変換済みの式を渡しても何も変わりません。定理のエントリは、
引用に使う de Bruijn 形式を `ENTRY-PAYLOAD` に、書かれたままの文面を
`ENTRY-ORIGIN` に持ちます。`.ledger` への保存と Web UI の表示は後者
（`ENTRY-SOURCE-PAYLOAD`）を使うので、ファイルと画面の変数名は書いたときのまま
です。引用のときは、保存された証明をもう一度変換してから使います（変換済みなら
何も変わりません）。手で組み立てた台帳のエントリでも安全に引用できるように
するためです。

**束縛子を開く**

`.system` ファイルの規則は名前付きの束縛子で書かれています（III.1 なら
`(.to (.forall ?x ?A) (@subst ?x ?t ?A))`）。照合器は、パターン
`(.forall ?x ?A)` を式 `(.forall 本体)` に当てるとき、本体を**開きます**。
自分を指すインデックスを変数に置き換え、外を指すインデックスを1つ減らしてから、
`?A` と照合します。開くのに使う変数は、

- `?x` がすでに変数 v に束縛されていれば v（Gen の x）。このとき v が本体に
  現れてはいけません（`∀v2 (v1 = v1)` を `(gen 0 v1)` で導いたとは言えない）。
- そうでなければ、新しい変数 `%0`, `%1`, … のうち、その規則の適用に関わるどの式
  にも現れない最初のもの。

新しい変数は入力だけから決まります（入力に現れる `%n` のどれよりも大きい番号）。
カウンタのような隠れた状態は使わないので、同じ証明を何度検証し直しても、同じ
選択が繰り返されます。`%n` はどの台帳でも変数として扱われ、他の種類の記号として
宣言することはできません。

**束縛変数の名前は ?bV₁, ?bV₂, … にそろえる**

束縛変数は、公理・推論規則・形成規則・定義・定理のどれでも、`?BV1`, `?BV2`, …
（Bound Variable 1, 2, …）という名前で表示します。Web UI では `?bV₁` と表示します
（Lisp の読み込みは大文字と小文字を区別しないので、`?bv1` も `?BV1` も同じ記号
です。大文字・小文字を区別して記号を節約するのは今後の課題です）。

- **規則**（`.system` の公理・推論規則・形成規則）: 登録のときに付け替えます。
  番号は、その規則の中で束縛子の変数として最初に現れた順（形、続いて側条件）で、
  規則ごとに、形・側条件・追加引数の全体で一斉に付け替えます。書かれたときの名前は
  ORIGIN の `:SOURCE-NAMES` に残ります。
- **定理**: カーネルは束縛変数を名前なし（de Bruijn）で記録しているので、表示の
  ときに、式ごとに束縛子が現れた順に番号を振ります。
- **定義**（`DEFINE-FUNCTION-BY-DESCRIPTION` の定義公理）: パターンの中の具体的な
  変数の束縛子も、表示のときに同じ名前にします。

```
書いたとおり  (∃!?X ?A) → ∃?X (?A ∧ ∀?U (?A[?U/?X] → ?U = ?X))
登録される形  (∃!?bV₁ ?A) → ∃?bV₁ (?A ∧ ∀?bV₂ (?A[?bV₂/?bV₁] → ?bV₂ = ?bV₁))
定理の表示    ∀?bV₁ ∀?bV₂ ?bV₁ + ?bV₂ = ?bV₂ + ?bV₁
```

**束縛子の外に ?bVₙ は現れない**: 規則のパターン変数を `?BVn` にするのは、それが
束縛変数としてだけ使われている場合に限ります。つまり、形の中のすべての出現が、
束縛子の変数の位置、その束縛子の本体、または代入 `A[t/x]`（`@subst`,
`@substitutes?`）の変数の位置にある場合です。Gen の `?x`（一般化する変数を指定する
追加引数）や、III.3・P3 の `?x`（追加引数）のように自由な位置にも現れるものは、
規則の自由変数でもあるので名前のまま残します。`?BVn` を束縛子の外に置くのは
スコープ違反になるからです。側条件 `(var? ?x)` などは、規則の変数についての主張で
あって式の中の出現ではないので、数えません。

証明の中でも、束縛子の変数に `?bV1` のような名前を使えます（Web UI の「S式を
コピー」で写した証明は、そのまま検証を通ります）。束縛子の外に書いた `?bV1` は項では
ないので拒否されます。

`?A` や `?t` のように、それ以外のパターン変数は名前のままです。規則がすでに別の用途で
`?BVn` という名前を使っていると、付け替えで2つの変数が混ざるので、読み込みを
エラーで止めます。

**原子記号と述語スキーマ**

定理の中の原子記号 A は、周りで束縛された変数を含まない式しか表せません。
`A → ∀v0 A` という定理は、A := `(v1 = v1)` として `(v1 = v1) → ∀v3 (v1 = v1)`
には使えますが、`(v1 = v1) → ∀v1 (v1 = v1)` には使えません（A が v1 を捕獲する
ことになるため）。束縛変数に依存する式は、述語スキーマで `(p x)` と書きます
（10節）。定理を引用するとき、照合器は定理の側と引用する側の束縛子を同じ新しい
変数で開くので、`(p (:bv 0))` と `(.in (:bv 0) v1)` は `(p %n)` と `(.in %n v1)` として
照合され、p := λ%n. `(.in %n v1)` が見つかります。

**`@subst-ok?` は残してある**

de Bruijn 形式では、代入が捕獲を起こさないことは形から保証されます。それでも
`@subst-ok?` は毎回確かめます。確かめる内容は「代入する項と代入先の式が局所的に
閉じている（外を指すインデックスがない）こと」です。変換や束縛子を開く処理に
誤りがあった場合に、誤った代入を黙って通すのではなく、ここで拒否するためです。
同じ理由で、照合でパターン変数に束縛できるのは、局所的に閉じた式だけです。

**テスト**

`tests/debruijn-tests.lisp` が、変換とその逆、α同値な式の同一視、捕獲の起きない
代入、Gen の条件、新しい変数、原子記号による捕獲の拒否を確かめます。既存の
テストとライブラリ（`.ledger` 約 8700 行）は、そのまま回帰テストとして通ります。
名前付きの版から期待値を変えたテストは1つだけです。ZF の置換公理で y := x とした
式は、内側の束縛が外側を隠すので、φ = (y = y) とした正しい例とα同値になり、
受理されるようになりました（`tests/zf-tests.lisp`）。

# Ledger Kernel — 追記専用台帳による Hilbert 流証明検証系

Common Lisp で書かれた、自前実装のミニマルな Hilbert スタイル証明検証系（proof
checker）です。「証明可能である」(⊢) という関係を、メタな言明としてではなく、
**一度検証されたら二度と改変されない追記専用の台帳（ledger）の1エントリ**として
文字通り実装しています。すべての定理・公理・推論規則・命題変数・項は、この台帳の
エントリであり、後から引用（cite）されるたびに **キャッシュではなく毎回ゼロから
再検証** されます（LCF 的な "always re-verify" の徹底）。

現状で以下まで実装済みです。

- 命題論理の核（K, S, 対比・矛盾からの導出規則 = Łukasiewicz の古典3公理）
- 述語論理（∀, Gen, III.1/III.2）
- 演繹定理（Deduction Theorem）を**メタな事実として直接信頼する**離脱機構
  （証明を展開せずに `A ⊢ B` を `A → B` に変形する）
- 一階等号公理（反射・対称・推移・Leibniz代入）
- ペアノ算術（P1〜P10）と、それを使った帰納法による実証明（`∀x. 0+x=x`）
- 古典命題論理の完全性に必要な残りの補題（排中律相当のケース分割公理 II.4、
  ¬¬除去/導入、reductio、矛盾律）
- **`PROVE-TAUTOLOGY`**: 任意の古典命題論理の恒真式を、真理表判定→Kalmarの完全性
  定理の構成的証明→ケース分割による仮定除去、という手順で**自動的に証明・検証**
  するタクティク。∧ ∨ ↔ も展開形を通して扱い、`(.in v0 v1)` のような任意の
  論理式を原子として使える
- **`ALPHA-RENAME-ENTRY` / `ALPHA-RENAME-FORALL`**: 束縛変数・自由変数・命題変数
  （atomic-wff-symbol）のα変換相当の操作。カーネルは構造的に一致しないと引用を
  拒否する（自動でのα同値扱いはしない）ので、「同じ定理を別名の変数で使いたい」
  という場面のための、**再検証込みの明示的な**リネーム機構
- **`.system` ファイル**: 体系そのもの（形成規則・公理・推論規則）をLispソース
  ではなくデータ（ファイル）として定義する仕組み
- **III.3（存在汎化）と `IOTA`（確定記述 `.iota x A` = 「Aを満たすx」）**: 存在
  証明と一意性証明の両方を引用することで、`.iota x A` という項自体がAを満たす
  ことを結論する規則。具体的な証人を要求せず、非構成的な存在・一意性証明だけで
  成立する（詳細は下記セクション参照）
- **`DEFINE-INDUCTIVE-PREDICATE(S)`**: ペアノのP3（帰納法）が「ZERO/Sだけの2種類の
  構成子」専用にハードコードされていたのに対し、任意の導入節（基底節・再帰節）
  から、新しい帰納的述語のための形成規則・導入規則・帰納法の公理を**すべて
  データから自動生成する**汎用の仕組み。**n項関係**（複数引数の述語）と
  **相互再帰**（複数の述語を1つのグループとして同時に定義し、互いの導入節から
  参照し合う）の両方に対応済み（詳細は下記セクション参照）
- **`EXISTS-ELIM`**: `.exists` の genuine な除去規則（Mendelson の Rule C）。
  `∃x.A` と、新鮮な証人変数 `w` について `A[w/x] → C` の両方から `C` を結論する
  （`w` が `A`・`C`・現在開いている仮定のいずれにも自由に出現しないことを機械的
  に検査した上で）。III.3（存在汎化、導入方向）と対になる、除去方向の規則
  （詳細は下記セクション参照）
- **`DEFINE-FUNCTION-BY-DESCRIPTION`**: 「存在してかつ一意である」ことをすでに
  証明した性質から、新しい**関数記号**を保存拡張（conservative extension）
  として鋳造する定義機構。生成された関数は、呼び出すたびに `IOTA` を経由する
  必要がなく、定義公理を直接引用するだけで使える（詳細は下記セクション参照）
- **定義された結合子（`hilbert-library/00-connectives.system`）**: ∧ `.and`・
  ∨ `.or`・↔ `.iff`・∃! `.exists1` を、形成規則と FOLD/UNFOLD の定義公理の
  組として定義。`.exists1` は束縛子なので、カーネルの `BINDER-HEADS` にも
  1語追加している（詳細は下記セクション参照）
- **ZF 集合論（`zf-library/00-zf.system`）**: 所属関係 `.in`（∈）と、ZF の
  8公理（外延性・対・和集合・冪集合・無限・正則性・分出図式・置換図式）を
  `.system` ファイルとして定義。選択公理は含まない（詳細は下記セクション参照）
- **ZF の最初の定理ライブラリ（`zf-library/01-empty-set.ledger`）**: 空集合の
  存在と一意性を証明し、定数 ∅ `(empty)` を定義（詳細は下記セクション参照）

- **述語スキーマ変数「A(x)」**: `(:declare-predicate-schema-symbol p 1)` で宣言した
  `p` について、`(p v0)` を「x を含む任意の論理式」として定理に書ける。引用時に
  具体的な論理式が代入される（自動、または `:inst` で明示）。量化子・∃! の汎用
  補題を `hilbert-library/07-quantifier-schemas.ledger` に収録（詳細は下記
  セクション参照）

- **Web UI（`web/`）**: ブラウザでライブラリを閲覧し、証明を表・証明図で表示し、
  エディタで書いた証明を検証できる（詳細は下記「Web UI」参照）

406/406 の self-test が pass、コンパイル警告 0 の状態です。


## ファイル構成

```
ledger-kernel.asd                     ASDF システム定義（ledger-kernel / ledger-kernel/tests）
src/                                  カーネル本体（ASDF で読み込む順に並べています）
  package.lisp                        パッケージ定義と設計方針のメモ
  pattern.lisp                        §1   パターンマッチ
  treap.lisp                          §1.5 台帳の索引に使う永続 treap
  ledger.lisp                         §2   台帳そのもの（Sigma / Gamma の射影、記号の宣言）
  side-conditions.lisp                §3   側条件
  meta.lisp                           §4   メタ述語・メタ構成子（not-free-in, subst 等）
  judgement.lisp                      §5   JUDGEMENT?（中核の再帰チェッカ）
  k-proof.lisp                        §6   K-proof の検証と CHECK-AND-EXTEND
  bootstrap.lisp                      §7-8 原始 Hilbert 体系のブートストラップ
  persistence.lisp                    §10  台帳のコマンド列としての永続化
  deduction.lisp                      §11  演繹定理（@DEDUCTION / 直接離脱）
  tautology.lisp                      §15  PROVE-TAUTOLOGY（Kalmar の完全性定理）
  alpha-conversion.lisp               §16  α変換
  system-spec.lisp                    §18  体系そのものをファイルで定義する（.system）
  inductive.lisp                      §20  帰納的述語の一般定義
  function-definition.lisp            §22  DEFINE-FUNCTION-BY-DESCRIPTION
tests/                                self-test 一式（ledger-kernel/tests システム）
  framework.lisp                      EXPECT と集計、ライブラリのパス解決
  *-tests.lisp                        機能ごとのテスト（§9, §11-14, §15-22）
  run.lisp                            RUN-ALL-SELF-TESTS（全テストの実行と集計）
hilbert-library/
  00-classical-fol-equality.system    体系そのものの定義（公理・推論規則・形成規則）
  00-peano-arithmetic.system          体系定義の追加分（ペアノ算術の語彙・公理）
  00-connectives.system               体系定義の追加分（∧ ∨ ↔ ∃! の定義）
  01-propositional-core.ledger        命題論理の基本定理（th-identity, 仮説三段論法 等）
  02-predicate-core.ledger            述語論理の基本定理（forall の順序交換）
  03-equality-core.ledger             等号の基本定理
  04-peano-arithmetic.ledger          0+x=x の帰納法証明 など
  05-classical-logic.ledger           古典論理の完全性補題（ex-falso, ¬¬導入/除去, raa 等）
  06-connectives.ledger               ∧ ∨ ↔ の基本補題（導入・除去・対称・推移・ド・モルガン 等）
  07-quantifier-schemas.ledger        述語スキーマ P(x) についての量化子・∃! の補題
zf-library/
  00-zf.system                        ZF 集合論の公理系（00-classical-fol-equality と 00-connectives の上に積む）
  01-empty-set.ledger                 空集合の存在・一意性と、定数 (empty) の定義
tools/
  generate-connectives-ledger.lisp    06-connectives.ledger を PROVE-TAUTOLOGY で生成し直すスクリプト
  serve.lisp                          Web UI をコマンドラインから起動するスクリプト
web/                                  Web UI（ledger-kernel/web システム。カーネルの外側）
  render.lisp                         S式を教科書風の記法（∀ ∃ → ∧ ∈ ∅ …）で表示
  worlds.lisp                         表示する「世界」（ZF、ペアノ算術）の読み込み
  api.lisp                            エントリ・証明・検証結果を JSON 用のデータにする
  server.lisp                         Hunchentoot のルーティング
  static/                             画面（index.html, app.js, style.css）
  tests.lisp                          表示と API のテスト
```

`.system` ファイルと `.ledger` ファイルは似ているようで**信頼のされ方が根本的に違います**（下記「体系そのものをファイルで定義する」参照）。`.system` は体系の**土台**（公理・推論規則）を、`.ledger` は土台の上で**証明された定理**を記述します。

`.ledger` ファイルは "アセンブラ的" な平たいコマンド列で、`(bootstrap-kernel
...)` で作った素の台帳の上に、この順番でチェーンロードして使います
（01→02→03→04→05 の順。04 は算術を使うので `:arithmetic t` 付きでブートストラップ
する必要があります）。


## クイックスタート（SBCL REPL）

### 1. ASDF でロードする

リポジトリのルートで SBCL を起動します。

```bash
sbcl
```

```lisp
(require :asdf)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel)
```

リポジトリを `~/common-lisp/` 以下（または Quicklisp の `local-projects/` 以下）に
置いておけば、`asdf:load-asd` なしで `(asdf:load-system :ledger-kernel)`
（Quicklisp なら `(ql:quickload :ledger-kernel)`）だけで読み込めます。

カーネルをロードしただけでは self-test は走りません。テストは別システム
`ledger-kernel/tests` に分かれていて、次で実行します（下記「テストの実行」参照）。

```lisp
(asdf:test-system :ledger-kernel)
```

末尾に `293/293 self-tests passed.` と出れば正常です。

以降は `ledger-kernel` パッケージに入って作業すると楽です。

```lisp
(in-package :ledger-kernel)
```

### 2. ライブラリをチェーンロードする

```lisp
(defparameter *L*
  (let* ((l0 (bootstrap-kernel :arithmetic t))
         (l1 (read-ledger-from-file "hilbert-library/01-propositional-core.ledger" :ledger l0))
         (l2 (read-ledger-from-file "hilbert-library/02-predicate-core.ledger" :ledger l1))
         (l3 (read-ledger-from-file "hilbert-library/03-equality-core.ledger" :ledger l2))
         (l4 (read-ledger-from-file "hilbert-library/04-peano-arithmetic.ledger" :ledger l3))
         (l5 (read-ledger-from-file "hilbert-library/05-classical-logic.ledger" :ledger l4)))
    l5))
```

エントリ数を確認：

```lisp
(length (treap-values-below (ledger-all *L*) (ledger-bound *L*)))
;=> 69 (くらいの数)
```

### 3. 定理を引用して検証してみる

`check-k-proof` に「行番号 / 論理式 / 役割 / 根拠」の生の証明（raw-proof）を渡すと、
`*L*` に対して一行ずつ再検証してくれます。

```lisp
;; forall v0. 0+v0 = v0 を th-zero-plus-identity から引用できるか
(check-k-proof
 '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity)))
 *L*)
;=> T
```

### 4. `PROVE-TAUTOLOGY` で恒真式を自動証明する

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

### 5. `ALPHA-RENAME-ENTRY` で束縛変数を付け替える（v0 → v1 問題の解決）

このカーネルは式を**構造的に**（`equal` ベースで）照合するだけなので、
`(.forall v0 A)` と `(.forall v1 A)` はまったく別の式として扱われます。つまり
`th-zero-plus-identity` を `v1` で引用しようとすると、**定理として正しくても
必ず失敗**します（自動でのα同値変換はしていません）。

```lisp
;; v0 で証明された定理を v0 のまま引用 -- OK
(check-k-proof '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))) *L*)
;=> T

;; 同じ定理を v1 で引用しようとすると失敗する（束縛変数名が違うので別の式扱い）
(check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity))) *L*)
;=> NIL
```

これに対応するのが `ALPHA-RENAME-ENTRY` です。既存のエントリの証明を丸ごと
`OLD-SYM -> NEW-SYM` でリネームした候補を作り、**ゼロから再検証した上で**新しい
名前の下に登録し直します（リネーム自体は一切信用しません。捕獲やGenの新鮮さ
条件を壊すような不正なリネームは、通常のチェッカーがそのまま refuse します）。

```lisp
(setf *L* (alpha-rename-entry *L* 'th-zero-plus-identity 'th-zero-plus-identity-v1 'v0 'v1))

(check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity-v1))) *L*)
;=> T
```

`th-zero-plus-identity` の証明は内部で `th-zero-plus-step`（引数なしの
`:th-ded` 引用で、その帰納法の仮定にも `v0` が出てくる）を引用しているため、
このリネームは**推移的**に効きます -- `th-zero-plus-step` 側も自動的に
`v0->v1` でリネームされ、`|TH-ZERO-PLUS-STEP\|V0->V1|` のような名前で登録
されてから、それを引用するよう書き換えられます（共有されている依存先は一度
だけリネームされ、`OLD-SYM` が出てこない依存先はそのまま引用され続けます）。

`ALPHA-RENAME-ENTRY` は束縛変数だけでなく、自由変数や命題変数（`A`,`B`,...
のような atomic-wff-symbol）にも同じように使えます（`SUBSTITUTE-WFF` とは
違い、束縛位置の記号ごと問答無用でリネームするので、シャドーイングの回避には
使えません -- あくまで「特定の1つの記号をこの証明全体で徹底的に付け替える」
ための操作です）。

もう一つ、`ALPHA-RENAME-FORALL` は既存の証明をリネームするのではなく、
`(forall x. A) -> (forall y. A[x:=y])` という一般形の**リネーム用の補題**を
III.1 + Gen + MP からその場で組み立てます。MP で既存の `(forall x ...)` 定理
にぶつければ、その定理自体を作り直さずに `y` 版を得られます。

```lisp
(setf *L* (alpha-rename-forall *L* 'v0 'v1 '(.eq (+ zero v0) v0) 'th-forall-rename-v0-v1))

(check-k-proof
 '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))
   (1 (.to (.forall v0 (.eq (+ zero v0) v0)) (.forall v1 (.eq (+ zero v1) v1)))
      :th (th-forall-rename-v0-v1))
   (2 (.forall v1 (.eq (+ zero v1) v1)) :ir (MP 1 0)))
 *L*)
;=> T
```

（`.exists` は現状 formation 規則しかない -- 存在汎化/存在例化の公理がまだ
ない -- ため、`ALPHA-RENAME-FORALL` に対応する `ALPHA-RENAME-EXISTS` はまだ
ありません。ただし `ALPHA-RENAME-ENTRY` 自体は、証明の中に `.exists` が
出てくる場合でも問題なく使えます -- `.exists` について何か新しく証明する
わけではなく、既存の証明をそのまま再検証するだけだからです。）

### 6. 検証コストが気になったら: `ENABLE-DERIVED-ENTRY-MEMOIZATION`

このカーネルは `TH`/`ITH`/`TH-DED`/`DEF-ABBREV` の引用を一切キャッシュせず、
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

### 7. 体系そのものをファイルで定義する: `.system` ファイル

ここまでの `.ledger` ファイルは、**すでに存在する体系**（公理・推論規則が
固定された `bootstrap-kernel`）の上で**証明された定理**を記述するものでした。
一方で体系そのもの（公理・推論規則・形成規則）は、これまで
`src/bootstrap.lisp` の `BOOTSTRAP-KERNEL` 関数の中に直接 Lisp のリテラルと
して埋め込まれていました -- 別の体系を試したければ Lisp のソースを書き換える
しかなかった、ということです。

`BOOTSTRAP-KERNEL` の中身は、実はもう完全にただのデータです。公理は
`(名前 側条件 (追加引数パターン 結論パターン))`、推論規則は
`(名前 側条件 (前提パターン 追加引数パターン :=> 結論パターン))`、
形成規則も同じ形。これをそのままファイルに切り出したのが `.system` ファイル
です。

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
を丸ごと `.system` ファイルとして書き下したものです。`TEST-BOOTSTRAP-FROM-SPEC`
（Section 18）で、これをロードして作ったLedgerが `BOOTSTRAP-KERNEL` の
ハードコード版と**エントリ単位で完全に一致する**ことを確認しています。

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
エントリで、`BOOTSTRAP-KERNEL` 自身のハードコードされた公理と全く同じ扱い
です。何と照合して確認するということが原理的にできません。つまり
`.system` ファイルを読み込むのは「検証」ではなく、**その作者を信頼する行為**
そのものです（`BOOTSTRAP-KERNEL` のLispソースをそのまま信頼していたのと
全く同じ意味で）。矛盾した公理系（`A` とその否定が両方証明できてしまう、
など）を書いてしまえば、それを体系の内側から検出することは原理的にできま
せん（ゲーデルの第二不完全性定理そのものであって、このチェッカーの欠陥では
ありません）。

側条件・パターンの中では `wff?`/`var?`/`term?` および既存のメタ述語・メタ
構成子（`@subst`, `@subst-ok?`, `@not-free-in?`, `@not-free-in-dependencies?`
等）を名前で自由に使えます -- これらは固定された閉じたカタログで、
`.system` ファイルは「この語彙を組み合わせて新しい体系を組み立てる」ことは
できますが、**新しいメタ述語自体を追加することはできません**（それは今まで
通りLispソースレベルの拡張です）。それでも、命題論理の別の公理基底、様相
論理の `.box`/`.diamond` のような新しい結合子と規則、といったものはこの
仕組みだけで十分表現できるはずです。


### 8. 確定記述（definite description）: `III.3` と `IOTA`

「Aを満たすxが存在し、しかもそれは一意である」ときに、その唯一のxを直接
指し示す項 `(.iota x A)`（"the x such that A"）を用意しました。

これがなぜ簡単ではないか、という点から説明します。既存の `.forall`/
`.exists` は**WFFを作る**束縛子でしたが、`.iota` は**項を作る**束縛子です。
このカーネルでは束縛子が新しい種類の値（WFFではなくTERM）を作るということ
自体が初めてで、`BINDER-HEADS`（`FREE-VARS-WFF`/`SUBSTITUTE-WFF`/
`COUNT-BOUND-OCCURRENCES` が「この頭部は束縛子である」と認識するための
Lispソース側のリスト）に `.IOTA` を追加するという、`.system` ファイルだけ
では完結しないLispソースレベルの変更が必要でした（既存の非束縛子な結合子・
関係はデータ駆動で拡張できるのに対し、束縛子の追加はこの一点だけ例外です）。

`IOTA` は**公理ではなく推論規則（IRULE）**です。MP/Genと同じく、証明中の
既存の行（プレミス）を引用する必要があるからです：

- **存在**: `(.exists x A)`
- **一意性**: `(.forall y (.forall z (.to A[y/x] (.to A[z/x] (.eq y z)))))`
  （「AND」結合子が存在しないため、カリー化した形で書く: 「y も z も A を
  満たすなら y=z」）

この2つを両方引用して初めて、`A[(.iota x A)/x]`（iota項自体がAを満たす）
が結論できます。存在論のごまかしをしない — **具体的な証人を要求しない**
（非構成的な存在証明で構わない）一方で、**一意性が示せない限りIOTAは絶対に
適用できない**（=一意でない場合の「値」を勝手に決める、というような
junk-valueの規約は一切ない）というのが設計上の要点です。

存在証明を可能にするために、`III.3`（存在汎化、`A[t/x] -> exists x. A`）
も新設しました。III.1（全称除去）の双対で、Gen（全称汎化）と違って自由変数
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
(defparameter *L* (bootstrap-kernel))
;; 存在: exists v0 (v0=v1)
(setf *L* (check-and-extend *L* 'th 'th-exists-v0-eq-v1
  '((0 (.eq v1 v1) :axiom (IV.1))
    (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))
    (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))))
;; 一意性: forall v2 forall v3 (v2=v1 -> (v3=v1 -> v2=v3))  (uniq-full。
;; 導出は 05-classical-logic.ledger の TH-RAA と同じ多段階の
;; deduction-theorem-direct 連鎖 -- 詳細は tests/iota-tests.lisp（Section 19）参照)
;; ...
;; IOTA適用: (iota v0 (v0=v1)) = v1
(check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                  (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                  (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 1)))
                *L*)
;=> T
```

**まだできないこと**（正直に書いておきます）:

- 「`y := the x such that A(x)` として `y` を以後の証明で再利用可能な新しい
  名前にする」という一般的な**定義機構**にはなっていません。`.iota x A` を
  使うたびに、その都度、存在と一意性の証明を改めて引用する必要があります。
- 一意性が示せない場合の「値」についての規約（古典的な確定記述理論でよく
  ある total function 化のための junk value）は用意していません。単に
  IOTAが適用できないだけです。
- `.exists` に完全な除去規則（存在の証明からその証人を実際に取り出す
  instantiation）はまだありません。III.3 は導入方向のみです。


### 9. 帰納的な定義機構: `DEFINE-INDUCTIVE-PREDICATE`

ペアノのP3（帰納法の公理）は「ZERO と S、この2つの構成子だけから作られる領域」
専用に手書きされたものでした。しかも「すべての項がすでに自然数である」という
特殊事情（自然数以外の項が存在しない体系）に乗っかっているので、ZERO/S以外の
構成子を持つ**新しい帰納的述語**（偶数、素数、到達可能性、……）を定義したいと
思っても、P3をそのまま使い回すことはできません。

`DEFINE-INDUCTIVE-PREDICATE` は、これを一般化したものです。「基底節」と「再帰
節」のリストを渡すだけで、以下の3種類のエントリを**すべて自動生成**します。

1. 新しい述語の**形成規則**（`(EVEN ?x)` のようなWFFを作れるようにする）
2. 節ごとの**導入規則**: 引数を取らない基底節は公理として、既存の証明行を
   引用する必要がある再帰節は（MP/Genと同じ）IRULEとして
3. **帰納法の公理そのもの**: P3を一般のk個の節に拡張したもの

具体例（EVEN: 「zeroは偶数」「xが偶数ならS(S(x))も偶数」）:

```lisp
(defparameter *L*
  (define-inductive-predicate (bootstrap-kernel :arithmetic t) 'even
    '((nil nil zero)             ; EVEN(zero)
      ((?x) nil (S (S ?x))))))   ; EVEN(x) -> EVEN(S(S(x)))

;; 導入規則が使える
(check-k-proof '((0 (even zero) :axiom (even-intro-1))
                  (1 (even (S (S zero))) :ir (even-intro-2 0)))
                *L*)
;=> T

;; 帰納法の公理 EVEN-IND も生成されている（P3と全く同じ使い方: 基底の証明・
;; 再帰節の証明をGenで閉じてから、EVEN-INDにMPを2回適用する）
```

節の書き方は `(再帰変数リスト その他の変数リスト 結果の項)` という3つ組で、
再帰変数（例: `?x`）は「すでにこの述語を満たしていると分かっている項」を表し、
再帰節では自動的に「(述語 再帰変数)」という前提と、帰納法の仮定 `A[再帰変数/x]`
の両方が使えるようになります。再帰変数を持たない節は基底節（公理）になります。

**注意点**: `.system` ファイルと全く同じ信頼モデルです。ここで生成される
エントリはすべて `:PRIMITIVE`（無条件に信頼される）で、独立検証は一切されま
せん。「新しい帰納的述語を定義する」というのは「新しい公理を手で書き足す」の
と全く同じ重みの行為であり、書いた節同士が矛盾していないかを自動でチェック
する仕組みは（P1〜P10のときと同様）ありません。**書きやすくする**仕組みでは
ありますが、**安全にする**仕組みではないという点は正直に書いておきます。

#### 9.1 一般化: n項関係・相互再帰 — `DEFINE-INDUCTIVE-PREDICATES`

上の `DEFINE-INDUCTIVE-PREDICATE`（単数形）は「単項・自己再帰のみ」という
よくある特殊ケース向けの薄いラッパーです。裏側の `DEFINE-INDUCTIVE-PREDICATES`
（複数形）は、これを2つの軸で一般化した本体で、単数形の既存の呼び出し・
self-testはすべて変更なしでそのまま動きます（後方互換性はテスト済み）。

- **n項関係**: 述語は1引数である必要はありません。節の「結果」が単一の項では
  なく、宣言した ARITY 個ぶんのタプルになります（例: `SUMR(x,y,z)` = 「x+y=z」
  という3項関係を、`+` という関数記号を一切使わずに帰納的に定義できます）。
- **相互再帰**: 複数の述語を1つの **GROUP** として同時に定義できます。各節の
  再帰前提は「自分自身」だけでなく、GROUP内の**どの述語でも**参照でき、
  生成される帰納法の公理はGROUP全体の節から組み立てた**同じ前提列**を共有し
  つつ、結論だけが述語ごとに異なります。これにより、たとえば `EVEN` の帰納法
  の公理を引用するには `ODD` 側の帰納法の仮定も一緒に満たす必要がある、という
  **本物の相互帰納法**が成立します。

CLAUSEの形は `(REC-SPECS EXTRA-VARS RESULT-TERMS)` の3つ組に一般化されます。
`REC-SPECS` は `(述語名 変数1 ... 変数k)` のリスト（1個の再帰前提につき1つ）で、
述語名はGROUP内のどれでもよく、`RESULT-TERMS` は（単項なら要素数1の）タプルに
なります。GROUPは `(述語名 ARITY . 節リスト)` のリストです。

具体例1（相互再帰、EVEN/ODD を同時に定義）:

```lisp
(setf *L*
  (define-inductive-predicates (bootstrap-kernel :arithmetic t)
    '((even 1 (nil nil (zero))               ; EVEN(zero)
             (((odd ?x)) nil ((S ?x))))       ; ODD(x) -> EVEN(S(x))
      (odd 1 (((even ?x)) nil ((S ?x)))))))   ; EVEN(x) -> ODD(S(x))

;; ODD(S(zero)) は EVEN(zero) を引用して証明できる
(check-k-proof '((0 (even zero) :axiom (even-intro-1))
                  (1 (odd (S zero)) :ir (odd-intro-1 0)))
                *L*)
;=> T
```

具体例2（n項関係、`+` を使わずに加法のグラフ `SUMR(x,y,z)` を定義）:

```lisp
(setf *L*
  (define-inductive-predicates (bootstrap-kernel :arithmetic t)
    '((sumr 3 (nil (?x) (?x zero ?x))                        ; SUMR(x,0,x)
             (((sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z)))))))  ; SUMR(x,y,z) -> SUMR(x,S(y),S(z))
```

複数引数を一度に代入するために、`@subst`（1変数専用）とは別の
**`@substn`/`@substn-ok?`**（複数の変数・項の組を「同時に」代入する、ゲンシム
を経由した2段階置換によりキャプチャ相互干渉を避ける仕組み）という新しい
メタ構成子・メタ述語が追加されています。信頼モデル・限界は単数形の場合と
全く同じです。

#### 9.2 定義前の整合性検査 — `CHECK-INDUCTIVE-GROUP-WELL-FORMED`

`DEFINE-INDUCTIVE-PREDICATES` は、実は開発中に**本物のバグ**を1つ生みました。
EVEN/ODD の相互再帰の例を書いたとき、うっかり既存の（単項・自己再帰の）
`EVEN` と同じ名前を再利用してしまい、`EVEN-INTRO-2` という名前のIRULEが台帳に
**2つ**、別の中身のまま共存する状態になりました。台帳は名前でエントリを検索
するのではなく「その kind の全エントリを順に試して、名前が一致してかつパター
ンにもマッチする最初の1つ」を採用する仕組みなので、本来は拒否されるべき攻撃
証明（「相互再帰版のEVENの導入規則を、ODDではなくEVEN自身を引用して騙し通そ
うとする」）が、**たまたま先に定義されていた古いEVENのほうの規則にマッチして
しまい、こっそり通ってしまう**という事故が実際に起きました。

これを踏まえて、`DEFINE-INDUCTIVE-PREDICATES` は呼び出しの一番最初に
`CHECK-INDUCTIVE-GROUP-WELL-FORMED` を必ず通すようになっています。何かに
引っかかれば、何も鋳造せずに（all-or-nothing で）即座にエラーを送出します。
検査しているのは次の3系統です。

1. **名前の衝突**: これから鋳造しようとしている名前（各述語のWFF形成規則名、
   各節の導入規則名、各述語の帰納法公理名）が、台帳に**既存の**
   `TERM?`/`WFF?`/`AXIOM`/`IRULE` エントリとして1つでも既に存在していないか。
   上記の実際に起きた事故そのものを再現できないようにする検査です。
2. **形の妥当性**: GROUP内で述語名が重複していないか、ARITYが正の整数か、
   各REC-SPECが引用する述語名がGROUPの中に実在するか（タイポで存在しない
   述語や無関係な述語を指してしまうと、`ASSOC`が黙って`NIL`を返し、静かに
   間違った公理が生成されてしまいます）、REC-SPECの変数の個数が引用先の
   述語自身のARITYと一致しているか、各節のRESULT-TERMSの長さが自分自身の
   ARITYと一致しているか、REC-SPEC/EXTRA-VARの変数がすべて本物のスキーマ
   パターン変数（`?`で始まる）か。
3. **基礎付け（groundedness）**: GROUP内のすべての述語が、基底節から辿れる
   何らかの節の連鎖で実際に導出可能か（文脈自由文法で「その非終端記号が
   何か1つでも文字列を生成できるか」を判定するのと全く同じ、最小不動点の
   計算です）。基底節を1つも持たない自己再帰や、誰も土台にたどり着けない
   相互再帰の循環を検出します。これは**健全性の欠陥ではありません**——導出
   不能な述語についての帰納法公理は空虚に真（vacuously true）なので、生成
   された公理自体は正しいままです——が、ほぼ確実に書き間違いなので拒否
   しています。

**この検査がカバーしていないこと**: いわゆる「厳密な正値性（strict
positivity）」の検査は行っていませんが、これは手を抜いているのではなく、
このファイルの節の形式そのものが最初から厳密に正値であることを構造的に
保証しているためです（REC-SPECSは常に「述語適用を前提として要求する」だけ
で、RESULT-TERMSの中に否定形や高階の形でその述語自身を埋め込む方法が
そもそもありません）。つまり、この機構が非単調な演算子（最小不動点が
そもそも存在しないもの）を作ってしまう心配は構造的になく、ここで検査して
いるのは純粋に「定義そのものの書き間違い」だけです。


### 10. 存在除去規則: `EXISTS-ELIM`

III.3（存在汎化）は `A[t/x] → ∃x.A` という**導入**方向の規則でした。これまでの
体系には、その逆——`∃x.A` という証明済みの事実から、実際に「その証人を仮に
名付けて」議論を進める**除去**方向の規則がありませんでした。`EXISTS-ELIM` は
これを埋める、Mendelson の Rule C 相当の genuine な存在除去規則です。

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


### 11. 保存的拡張としての関数定義: `DEFINE-FUNCTION-BY-DESCRIPTION`

`IOTA`（8節）は「存在して一意」という性質から `.iota x A` という**項**を作れる
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

### 12. 定義された結合子: `hilbert-library/00-connectives.system`

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
（セクション 15）。

### 13. ZF 集合論: `zf-library/00-zf.system`

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
使っている任意の変数名でそのまま引用できます（`ALPHA-RENAME` は不要）。その
代わり、束縛変数どうしが**互いに異なる**ことを側条件として要求します
（Metamath の distinct variable 条件に相当）。これがないと、たとえば外延性公理で
z := x とすると ∀x ∀y (∀x (x∈x ↔ x∈y) → x = y) という別の（健全でない）主張に
なってしまうためです。

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


### 14. 空集合: `zf-library/01-empty-set.ledger`

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


### 15. 述語スキーマ変数「A(x)」: `07-quantifier-schemas.ledger`

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


## Web UI（ブラウザで閲覧・検証する）

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


## 式の書き方（S式記法）

論理式はすべて素の S 式です。読み込み時に Common Lisp リーダーが記号を大文字化
するので、`a` と書いても内部的には `A` になります（`hilbert-library/*.ledger`
はすべて小文字で書かれていますが同じ理由で問題ありません）。

| 記法 | 意味 |
|---|---|
| `(.to P Q)` | P → Q |
| `(.neg P)` | ¬P |
| `(.eq S T)` | S = T |
| `(.forall X P)` | ∀X. P |
| `(.exists X P)` | ∃X. P |
| `zero`, `(S X)`, `(+ X Y)`, `(* X Y)` | 0, X+1, X+Y, X×Y（`:arithmetic t` 時のみ形成規則あり） |
| `A`,`B`,`C`,... | 命題変数の原子記号（`bootstrap-kernel` のデフォルトで A〜H） |
| `v0`,`v1`,... | 個体変数 |


## 台帳への追加のしかた（新しい定理を作る）

大きく3つの入り口があります。

1. **`check-and-extend`** — 開いた仮定を持たない、閉じた（closed）証明をそのまま
   登録する。
   ```lisp
   (setf *L* (check-and-extend *L* 'th 'my-theorem raw-proof))
   ```
2. **`check-and-extend-by-deduction-direct`** — `Γ, H ⊢ Φ` の証明（`H` を仮定に
   含む）を渡すと、演繹定理を信頼して `Γ ⊢ (H → Φ)` として登録する。これが
   このカーネルの目玉機能で、`@deduction`（証明を展開して K/S だけで組み立て直す
   古典的な演繹定理の実装）を使うと行数が指数的に爆発するのを避けられます。
   ```lisp
   (setf *L* (check-and-extend-by-deduction-direct *L* 'my-lemma 'hyp-formula raw-proof))
   ```
3. **`prove-tautology`** — 上記参照。命題論理の恒真式なら丸ごと自動化できる。

いずれも内部で `check-k-proof` によるゼロからの再検証を必ず経ます。ここを迂回する
経路はありません。


## テストの実行

全テストをまとめて実行するには：

```lisp
(asdf:test-system :ledger-kernel)
```

コマンドラインからなら（リポジトリのルートで）：

```bash
sbcl --non-interactive \
     --eval '(require :asdf)' \
     --eval '(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))' \
     --eval '(asdf:test-system :ledger-kernel)'
```

各チェックが `[pass]`/`[FAIL]` の行を出力し、最後に `N/M self-tests passed.` と
集計を表示します。`[FAIL]` が1つでもあれば `asdf:test-system` はエラーで終了します。

個別のテスト群だけを実行したい場合は、`(asdf:load-system :ledger-kernel/tests)`
のあと `ledger-kernel` パッケージで次を呼びます。

```lisp
(run-self-tests)                       ; カーネル全体 + 算術
(run-classical-logic-self-tests)       ; 古典論理の補完的公理・補題
(run-tactics-self-tests)               ; PROVE-TAUTOLOGY
(run-alpha-conversion-self-tests)      ; ALPHA-RENAME-ENTRY / ALPHA-RENAME-FORALL
(run-derived-entry-memoization-self-tests) ; ENABLE-DERIVED-ENTRY-MEMOIZATION の差分検証
(run-bootstrap-from-spec-self-tests)   ; .system ファイルからのブートストラップの一致検証
(run-iota-self-tests)                  ; III.3 / IOTA（確定記述）
(run-inductive-definition-self-tests)  ; DEFINE-INDUCTIVE-PREDICATE(S)（単項・n項・相互再帰・整合性検査）
(run-exists-elim-self-tests)           ; EXISTS-ELIM（存在除去規則）
(run-function-definition-self-tests)   ; DEFINE-FUNCTION-BY-DESCRIPTION（保存的拡張）
(run-connectives-self-tests)           ; ∧ ∨ ↔ ∃!、PROVE-TAUTOLOGY の拡張、06-connectives.ledger
(run-zf-self-tests)                    ; ZF の公理系
(run-empty-set-self-tests)             ; 空集合、定義の保存と読み戻し
(run-predicate-schema-self-tests)      ; 述語スキーマ変数、:inst、07-quantifier-schemas.ledger
```

コードを変更したときは、必ず上のコマンドで **コンパイル警告 0** と
**`[FAIL]` 0** を確認する、という手順を踏んでください（このプロジェクト全体で徹底
している規約です）。


## 設計上の要点（読み手向け）

- **エントリの種類**: `atomic-wff-symbol` / `variable-symbol` /
  `predicate-schema-symbol`（語彙）、`term?` /
  `wff?`（形成規則）、`irule`（推論規則, MP/Gen）、`axiom`、`th` / `ith`（定理、
  閉じた証明）、`th-ded`（演繹定理直接離脱で作った定理）、`def-abbrev`（略記の
  定義）。
- **`th-ded` の健全性**: `A ⊢ B` から `A → B` を作るとき、証明中に残っている
  他の未放棄の仮定（Γ）は、引用時にちゃんと citable な前提として要求されます
  （これを落とすと `(C→D)→D` のような偽の「定理」を認めてしまう、というバグを
  開発中に一度捕まえて直しています）。
- **II.4 の位置づけ**: `II.1〜II.3`（Łukasiewicz の3公理）だけで古典論理として
  完全ですが、そこから ¬¬除去等を導く最短証明は数十ステップ級になるため、
  実用性を優先して `II.4`（ケース分割）を独立公理として追加しています。これは
  IV.3/IV.4 や P8-P10（導出不可能性を証明した上で追加）とは違い、「導出可能だが
  実際には導出していない」ことをコード中のコメントで明記しています。
- **`PROVE-TAUTOLOGY` の仕組み**: Kalmar の補題（各部分論理式について、その
  真理値に応じた符号付き形が、原子論理式の符号付き仮定から証明できる）を構造
  帰納法で構成し、`II.4` によるケース分割で全ての仮定を1つずつ消去して閉じた
  定理にする、という教科書的な完全性証明をそのままコードにしたものです。


## 既知の限界・今後の方向

- 現在扱えるのは一階述語論理 + 算術、および ZF 集合論の公理系と空集合まで。
  対・和集合・順序対・自然数などの ZF 定理ライブラリはまだありません。高階の量化
  （逆数学の RCA₀/WKL₀/ACA₀ 等の部分体系）もまだありません。
- ∧・∨・↔・∃! は定義された結合子なので、証明の中では展開形との行き来を
  UNFOLD／FOLD 公理で明示的に書く必要があります（`PROVE-TAUTOLOGY` は自動で
  行います）。
- 定理の中の束縛変数や補題内部の変数は、自動では付け替えられません。変数の
  衝突で引用が拒否されたときは、`:inst` で変数を置き換えて引用します。
- `PROVE-TAUTOLOGY` は命題論理の構造しか使いません。量化子を含む部分論理式は
  原子として扱うので、量化子の推論が必要な式は証明できません。
- ケース分割の再帰は原子論理式の数に対して指数的です（2^n 個の分岐を作るため）。
  atom 数が多い恒真式には向きません。
- `search.lisp`（探索ベースの補助タクティク、bounded forward-chaining）は
  実験段階で、実際に使われたのは手動導出＋カーネル検証の組み合わせです。
- `IOTA`/`III.3`（確定記述）は、`EXISTS-ELIM` の追加によって除去方向の規則も
  揃いましたが、一意でない場合の junk-value 規約（一意性が崩れたときに
  `.iota` が何を指すかの取り決め）はまだありません。また `EXISTS-ELIM` を
  引用するたびに新鮮な証人変数を手で選ぶ必要があり、これを自動選択する
  仕組みはありません。
- `DEFINE-INDUCTIVE-PREDICATES` は n項関係・相互再帰の両方に対応し、
  `CHECK-INDUCTIVE-GROUP-WELL-FORMED`（9.2節）によって名前の衝突・形の妥当性・
  基礎付け（groundedness）の3系統は定義前に機械的に検査されるようになりました。
  ただし、これは「定義そのものの書き間違い」を捕まえる検査であって、生成後の
  エントリはそれでも依然としてすべて `:PRIMITIVE`（無条件に信頼される）のまま
  です——このカーネルが独立に検証しているのは「この節から機械的にこの公理が
  正しく組み立てられているか」という**構文的な**整合性であって、「この体系
  全体が無矛盾か」という意味論的な主張そのものではありません（この区別は
  `.system` ファイルの信頼モデルと同じです）。
- `DEFINE-FUNCTION-BY-DESCRIPTION` は、existence/uniquenessの証明が実際に主張
  通りの形をしているかは機械的にチェックしますが、「existence+uniquenessから
  definition-by-descriptionが保存的拡張になる」というメタ定理自体をカーネル内
  で形式的に証明してはいません（11節の「正直な限界」参照）。
  また、書いた節同士の無矛盾性を自動でチェックする仕組みもありません
  （.systemファイルと同じく「書きやすくする」だけで「安全にする」ものでは
  ない、という点は本文中に明記した通りです）。

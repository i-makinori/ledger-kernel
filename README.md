# Ledger Kernel — 追記専用台帳による Hilbert 流証明検証系

Common Lisp で書かれた、自前実装の Hilbert 流の証明検証系（proof checker）です。
「証明可能である」（⊢）という関係を、**一度検証されたら二度と書き換えられない
追記専用の台帳（ledger）の1エントリ**として、文字通りに実装しています。

設計の芯は3つです。

- **追記専用の台帳**: 記号・形成規則・公理・推論規則・定理・定義は、すべて台帳の
  エントリです。エントリには登録順の番号 k が付き、証明は自分より前に登録された
  エントリしか引用できません（循環が起きません）。
- **毎回ゼロから再検証する**: 定理を引用するたびに、保存されている証明に代入を
  施して、最初から検証し直します（LCF 的な "always re-verify" の徹底）。
  「正しい証明に代入しても正しい」というメタ定理すら仮定しません。
- **体系はデータ**: 論理そのもの（公理・推論規則・形成規則）を `.system`
  ファイルとして書き、差し替えられます。命題論理・一階述語論理・等号・ペアノ算術・
  ZF 集合論は、どれもこの仕組みで定義しています。

- **束縛変数には名前がない**（マシン B）: カーネルの内部では、束縛変数を
  de Bruijn インデックスで表します。`∀v0 ∀v1 (v0 = v1)` は
  `(.forall (.forall (.eq (:bv 1) (:bv 0))))` になり、束縛変数の名前だけが違う
  （α同値な）式は文字通り同じ値です。自由変数は意味を持つので名前のまま残します。
  変換は証明が台帳に入るときに一度だけ行い、書かれたままの文面は表示と保存の
  ために別に残します。束縛変数の名前は、公理・規則・定義・定理のどれでも `?bV₁`, `?bV₂`, … に
  そろえて表示します（規則は登録時に付け替え、定理は表示時に番号を振る）。

ブラウザでライブラリを閲覧し、証明を証明図で眺め、書いた証明をその場で検証できる
Web UI も付いています。

> 各機能の詳しい説明は [docs/guide.md](docs/guide.md) にあります。


## できること

**論理と体系**
- 命題論理（Łukasiewicz の3公理 + 場合分け II.4）、一階述語論理（∀・∃、Gen、
  存在汎化 III.3、存在除去 `EXISTS-ELIM`）、等号（IV.1〜IV.4）
- 定義された結合子 ∧ ∨ ↔ ∃!（`00-connectives.system`）
- ペアノ算術（P1〜P10）と、その上の順序 ≤ ・ <（`00-peano-order.system`）
- ZF 集合論（外延性・対・和集合・冪集合・無限・正則性・分出図式・置換図式。
  選択公理なし）
- 確定記述 `(.iota x A)`（「A を満たすただ1つの x」）

**定義の仕組み**
- `DEFINE-FUNCTION-BY-DESCRIPTION`: 存在と一意性を証明済みの性質から、新しい
  関数記号を定義する（例: 空集合 ∅）
- 述語スキーマ変数「A(x)」: `(p v0)` を「x を含む任意の論理式」として定理に書き、
  引用時に具体的な式を代入する（自動、または `:inst` で明示）

**自動化**
- `PROVE-TAUTOLOGY`: 命題論理の恒真式を、Kalmar の完全性定理の構成に従って自動で
  証明する（∧ ∨ ↔ も扱い、任意の論理式を原子として使える）

どの道具が作った証明も、台帳に入る前に必ずカーネルが検証します。道具そのものは
信頼しなくて構いません。

**ライブラリと Web UI**
- 命題論理・述語論理・等号・古典論理・結合子・量化子の補題、ZF の空集合（存在・
  一意性・定義）
- 自然数論: 加法・乗法の交換律・結合律・分配律・簡約律（`08`）、順序の反射律・
  推移律・反対称律・全順序性、「0 か後者か」（`09`）、割り算の存在と一意性、商 `div-s`・
  余り `mod-s`・ゲーデルの β 関数 `beta` の定義（`10`）。すべて P1〜P10 から帰納法で証明
- Web UI: ライブラリの閲覧（式は教科書風の記法）、証明の表と証明図、記号や引用先への
  リンク、依存している公理と「この定理を使っている定理」の表示、ブラウザ上での
  証明の検証

テスト: カーネル 301 件、Web 41 件がすべて通り、コンパイル警告 0 の状態です。

カーネル（`src/`）はコメント込みで約 2000 行です。論理そのものはコードに書かず、
すべて `.system` ファイルに置いています。使われていない機能は `backup/` に、元の
コードと復元の手順を添えて退避してあります（[backup/README.md](backup/README.md)）。


## 動かしてみる

### 読み込みとテスト

必要なのは SBCL（他の Common Lisp 処理系でもおおむね動くはずです）と ASDF だけです。
リポジトリのルートで SBCL を起動します。

```lisp
(require :asdf)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel)
(asdf:test-system :ledger-kernel)      ; 最後に "301/301 self-tests passed." と出る
(in-package :ledger-kernel)
```

リポジトリを `~/common-lisp/` 以下（または Quicklisp の `local-projects/` 以下）に
置けば、`asdf:load-asd` なしで `(asdf:load-system :ledger-kernel)` だけで読み込めます。

### ライブラリを読み込む

体系（`.system`）の上に、定理のライブラリ（`.ledger`）を順番に積みます。
ZF 集合論の場合:

```lisp
(defun load-chain (files)
  (reduce (lambda (ledger file)
            (if (string= (pathname-type file) "system")
                (bootstrap-kernel-from-spec-file file :ledger ledger)
                (read-ledger-from-file file :ledger ledger)))
          files :initial-value nil))

(defparameter *L*
  (load-chain '("hilbert-library/00-classical-fol-equality.system"
                "hilbert-library/00-connectives.system"
                "zf-library/00-zf.system"
                "hilbert-library/01-propositional-core.ledger"
                "hilbert-library/02-predicate-core.ledger"
                "hilbert-library/03-equality-core.ledger"
                "hilbert-library/05-classical-logic.ledger"
                "hilbert-library/06-connectives.ledger"
                "hilbert-library/07-quantifier-schemas.ledger"
                "zf-library/01-empty-set.ledger")))
```

ペアノ算術なら、`00-classical-fol-equality.system`・`00-connectives.system`・
`00-peano-arithmetic.system`・`00-peano-order.system` の上に `01`〜`06`、`08`〜`10` を
積みます（Web UI の「Peano arithmetic」と同じ順です）。読み込むときに、すべての証明が
検証し直されます。

### 定理を引用する・証明を検証する

`check-k-proof` に証明を渡すと、台帳に対して1行ずつ検証し、通れば `T` を返します。

```lisp
;; 空集合には何も属さない: ¬(v0 ∈ ∅)
(check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty))) *L*)
;=> T

;; ∧ の除去（A ∧ B → A）を、集合の式に当てはめて使う
(check-k-proof '((0 (.and (.in v0 v1) (.in v0 v2)) :hyp nil)
                 (1 (.to (.and (.in v0 v1) (.in v0 v2)) (.in v0 v1)) :th (th-and-elim-l))
                 (2 (.in v0 v1) :ir (mp 1 0)))
               *L*)
;=> T
```

通らないときは `NIL` と、2つ目の値として最初に拒否された行の番号が返ります。

証明を定理として登録するには `check-and-extend` などを使います（下の「台帳を育てる」参照）。
命題論理の恒真式なら、自動で証明できます。

```lisp
(setf *L* (prove-tautology *L* '(.to (.or a b) (.or b a)) 'th-my-or-comm))
```

### Web UI

Hunchentoot と yason が必要です（Quicklisp なら `(ql:quickload '(:hunchentoot :yason))`、
Debian/Ubuntu なら `apt install cl-hunchentoot cl-yason`）。カーネル本体はこれらに
依存しません。

```bash
sbcl --load tools/serve.lisp          # http://127.0.0.1:8080/ を開く
```

「ZF 集合論」と「ペアノ算術」の2つの世界を切り替えて閲覧できます。証明は表と
証明図で表示でき、証明図の横線をクリックすると折りたたみ／展開、式の中の記号や
規則名をクリックすると引用先・導入元のエントリが新しいタブで開きます。各エントリの
ページには、依存している公理と、そのエントリを使っている定理も表示されます。
エディタで書いた証明は、選んだ世界の台帳に対して検証されます（台帳には追加しません）。
詳しくは [docs/guide.md](docs/guide.md) の Web UI の節を参照してください。

サーバーなしで見せたいときは、静的サイトとして書き出せます。

```bash
sbcl --non-interactive --load tools/export-static.lisp    # site/ に書き出す（OUT=... で変更可）
```

`site/index.html` はそのままブラウザで開け（file:// でも動きます）、フォルダごと
GitHub Pages などの静的ホスティングに置けます。画面はサーバー版と同じで、サーバーが
返すはずの答えをすべて `site/data/*.js` に書き出してあります。書き出しの時点で全証明を
再検証しているので、載るのはカーネルが受理したものだけです。閲覧専用のため、
エディタでの検証はできません（証明の S 式はコピーできます）。


## 証明の書き方

### 1行の形

証明は行のリストです。1行は `(番号 論理式 役割 根拠)` の4つ組です。

| 役割 | 根拠の形 | 意味 |
|---|---|---|
| `:hyp` | `nil` | 仮定を置く |
| `:axiom` | `(公理名 追加引数...)` | 公理のインスタンス。例: `(III.1 t)`、`(III.3 x A t)` |
| `:ir` | `(規則名 行番号... 追加引数...)` | 推論規則の適用。例: `(mp 1 0)`、`(gen 3 v0)`、`(exists-elim 2 7 v3)` |
| `:th`, `:th-ded` | `(定理名 行番号... [:inst 束縛])` | 定理の引用。行番号は、その定理が要求する前提を証明した行 |

`(mp 1 0)` は「1行目の `A → B` と0行目の `A` から `B`」です。定理の引用では、
定理の中の原子記号 A, B, … や述語スキーマ P(x) に何を代入するかは、ふつう自動で
決まります。決まらないときや、定理の中の変数を置き換えたいときは、`:inst` で明示します。

```lisp
(th-forall-elim :inst ((v1 (empty))))          ; 変数 v1 を項 (empty) に置き換える
(th-forall-mono :inst ((p (v3) (.in v3 v1))))  ; 述語スキーマ P に λv3. v3 ∈ v1 を代入
(th-and-elim-l  :inst ((a (.in v0 v1))))       ; 原子記号 A に論理式を代入
```

### 式の書き方

論理式は S 式で書きます。読み込み時に記号は大文字化されるので、`a` と `A` は同じです。

| S 式 | 意味 | S 式 | 意味 |
|---|---|---|---|
| `(.to A B)` | A → B | `(.forall x A)` | ∀x A |
| `(.neg A)` | ¬A | `(.exists x A)` | ∃x A |
| `(.and A B)` | A ∧ B | `(.exists1 x A)` | ∃!x A |
| `(.or A B)` | A ∨ B | `(.iota x A)` | ιx A（A を満たすただ1つの x） |
| `(.iff A B)` | A ↔ B | `(.eq s t)` | s = t |
| `(.in s t)` | s ∈ t（ZF） | `(empty)` | ∅（ZF） |
| `zero`, `(S t)`, `(+ s t)`, `(* s t)` | 0, S(t), s+t, s·t（ペアノ算術） | `(p t)` | 述語スキーマ P(t) |
| `a`, `b`, `c`, … | 命題記号（任意の論理式の代わり） | `v0`, `v1`, … | 個体変数 |

束縛変数の名前は自由に選べます。`(.forall v0 (.eq v0 v0))` と
`(.forall v3 (.eq v3 v3))` はカーネルの中では同じ式なので、どちらで書いても同じ
定理・同じ規則に一致します（詳しくは [docs/guide.md](docs/guide.md) の13節）。

`.and` `.or` `.iff` `.exists1` は `00-connectives.system` で定義された結合子です。
展開形（例: A ∧ B は ¬(A → ¬B)）とは別の式として扱われ、証明の中では定義公理
`AND-UNFOLD` / `AND-FOLD` などで行き来します。


## 台帳を育てる

| 関数 | 登録されるもの |
|---|---|
| `check-and-extend` | 閉じた証明を、定理（`th`）として登録する |
| `check-and-extend-by-deduction-direct` | 仮定 H を含む証明 Γ, H ⊢ Φ を、演繹定理により Γ ⊢ H → Φ として登録する（`th-ded`） |
| `prove-tautology` | 命題論理の恒真式を自動で証明して登録する |
| `define-function-by-description` | 存在・一意性の定理から、関数記号とその定義公理を追加する |
| `declare-atomic-wff-symbol`, `declare-variable-symbol`, `declare-predicate-schema-symbol` | 新しい記号を宣言する |

台帳は `write-ledger-to-file` でコマンド列として保存でき、`read-ledger-from-file`
で読み戻せます。`.ledger` ファイルはこのコマンド列そのもので、手で書くこともできます。
読み込むときは、全コマンドが上の関数を通って検証し直されます。


## ライブラリ

| ファイル | 内容 |
|---|---|
| `hilbert-library/00-classical-fol-equality.system` | 一階述語論理と等号の体系（形成規則、MP・Gen・IOTA・EXISTS-ELIM、II.1〜4、III.1〜3、IV.1〜4） |
| `hilbert-library/00-connectives.system` | ∧ ∨ ↔ ∃! の形成規則と定義公理 |
| `hilbert-library/00-peano-arithmetic.system` | ペアノ算術の語彙と公理 P1〜P10 |
| `hilbert-library/00-peano-order.system` | 順序 ≤ ・ < の定義（s ≤ t :⇔ ∃z s + z = t、s < t :⇔ S s ≤ t） |
| `hilbert-library/01-propositional-core.ledger` | 恒等律、仮言三段論法、前件の入れ替え |
| `hilbert-library/02-predicate-core.ledger` | ∀ の順序交換 |
| `hilbert-library/03-equality-core.ledger` | 等号の反射律・推移律 |
| `hilbert-library/04-peano-arithmetic.ledger` | 0 + x = x（帰納法による証明） |
| `hilbert-library/05-classical-logic.ledger` | ex falso、二重否定の導入・除去、背理法 など |
| `hilbert-library/06-connectives.ledger` | ∧ ∨ ↔ の基本補題（導入・除去・対称・推移・ド・モルガン・排中律 など。`tools/generate-connectives-ledger.lisp` で生成） |
| `hilbert-library/07-quantifier-schemas.ledger` | P(x) についての量化子の補題（∀除去、∃導入、単調性、∃! → ∃、∃! の一意性） |
| `hilbert-library/08-arithmetic.ledger` | 加法・乗法の交換律・結合律・分配律・簡約律、0 と 1 の性質（`tools/generate-arithmetic-ledger.lisp` で生成） |
| `hilbert-library/09-order.ledger` | ≤ の反射律・推移律・反対称律・全順序性、x ≤ Sx、0 か後者か、x + y = 0 → y = 0（同上） |
| `hilbert-library/10-division.ledger` | S b による割り算の存在と一意性、商 `div-s(a,b)`・余り `mod-s(a,b)`・β 関数 `beta(c,d,i)` = c mod (1+(i+1)d) の定義（同上） |
| `zf-library/00-zf.system` | ZF の公理系 |
| `zf-library/01-empty-set.ledger` | 空集合の存在・一意性、∅ の定義、¬(x ∈ ∅) |

読み込み順は、`.system` → `01`, `02`, `03`, `05`, `06`, `07` → `zf-library/01` です
（「ライブラリを読み込む」の例のとおり）。

`08`〜`10` の法則は、束縛専用の変数 x1, x2, x3 で全称閉包した形で登録されています
（例: `th-add-comm` は ∀x1 ∀x2 (x1 + x2 = x2 + x1)）。使うときは引用してから III.1 で
好きな項を代入します。代入する項に x1〜x3 が現れないので、変数の捕獲は起きません。


## 何を信頼しているか（信頼モデル）

形式検証の結果を信じるには、「何を検証していて、何を無条件に信頼しているか」を
知っておく必要があります。

**検証していること**
- すべての定理は、登録時に検証され、引用されるたびに代入後の証明全体が再検証
  されます。引用時には、代入後の証明の仮定と結論が、引用している行・前提と完全に
  一致することも確かめます。そのため、代入を探す照合の処理が誤っていても、誤った
  引用は通りません（照合をわざと壊したテストで確認しています）。
- 証明が引用できるのは、自分より前に登録された公理・規則・定理だけです。記号と
  形成規則（何が式か）だけは、後から追加されたものも見えます。これにより、
  論理の補題を後で定義した記号（∅ など）に対して使えます。形成規則は何も証明
  しないので、健全性には影響しません。
- `.ledger` / `.system` ファイルはデータとしてだけ読み込みます（`#.(...)` による
  コード実行はできません）。`.ledger` ファイルが壊れていても書き換えられていても、
  起こりうるのは「読み込みに失敗する」ことだけです。
- `PROVE-TAUTOLOGY` などの道具が作った証明も、登録前に必ず検証されます。

**無条件に信頼しているもの**
- **カーネルのコード**: 照合、自由変数や代入可能性の判定（メタ述語）、再検証の
  ロジック、そして書かれた式を de Bruijn 形式に直す変換（`src/debruijn.lisp`）。
  束縛子の一覧（`.forall` `.exists` `.iota` `.exists1`）もカーネルに固定されて
  います。代入は束縛変数を捕獲しようがない形で行いますが、`@subst-ok?` は
  残してあり、変換や束縛子の展開に誤りがあれば、そこで検出して拒否します。
- **`.system` ファイルの内容**: 公理・推論規則・形成規則は、読み込めばそのまま
  信頼されます（`:PRIMITIVE`）。II.4 は II.1〜II.3 から導出可能ですが、公理として
  置いています。公理系の無矛盾性は、体系の内側からは確かめられません
  （ゲーデルの第二不完全性定理）。
- **演繹定理**: `th-ded` の定理は、演繹定理をメタ定理として信頼して登録されて
  います（Gen の制約は検査しています）。証明の中で他の定理を引用している場合への
  拡張の論証は `src/deduction.lisp` に書いてあります（機械的な検証はしていません）。Web UI の「依存している基礎」に、この
  信頼を使ったかどうかが表示されます。
- **定義の保存性**: `DEFINE-FUNCTION-BY-DESCRIPTION` は存在・一意性の定理を
  再チェックしますが、「それなら定義は保存拡張になる」というメタ定理そのものは
  信頼しています。

**保証していないこと**
- 同じ Lisp イメージの中での保護はありません。`ledger-append` は公開されていて、
  関数も再定義できます。信頼の根拠は「ファイルから読み直せば、すべて検証し直される」
  ことにあります。
- カーネルのコードそのものを独立に検証する手段（別実装の検証器や仕様書）は、
  まだありません。


## ファイル構成

```
ledger-kernel.asd        ASDF システム定義（ledger-kernel / ledger-kernel/tests /
                         ledger-kernel/web / ledger-kernel/web/tests）
src/                     カーネル本体
  package.lisp           パッケージ定義と設計方針
  pattern.lisp           パターン照合と、定理の代入（述語スキーマを含む）
  treap.lisp             台帳の索引に使う永続 treap
  ledger.lisp            台帳、記号の宣言、束縛子の一覧
  debruijn.lisp          束縛変数の de Bruijn 表現（変換、束縛子の展開と閉包、新しい変数）
  side-conditions.lisp   側条件
  meta.lisp              メタ述語・メタ構成子（自由変数、代入 など）
  judgement.lisp         形成規則の判定（JUDGEMENT?）
  k-proof.lisp           証明の検証（CHECK-K-PROOF）と登録（CHECK-AND-EXTEND）
  persistence.lisp       台帳の保存と読み込み
  deduction.lisp         演繹定理による登録（th-ded）
  tautology.lisp         PROVE-TAUTOLOGY
  system-spec.lisp       .system ファイルの読み込み
  function-definition.lisp  DEFINE-FUNCTION-BY-DESCRIPTION
tests/                   カーネルのテスト（ledger-kernel/tests）
hilbert-library/         論理とペアノ算術の体系・ライブラリ
zf-library/              ZF 集合論の体系・ライブラリ
web/                     Web UI（ledger-kernel/web。カーネルの外側）
  render.lisp            式を教科書風の記法で表示
  worlds.lisp            表示する世界（ZF、ペアノ算術）
  deps.lisp              引用関係（依存している公理、使っている定理）
  api.lisp, server.lisp  JSON API と Hunchentoot のルーティング
  static-export.lisp     静的サイトとして書き出す
  static/                画面（HTML / JS / CSS）
  tests.lisp             表示と API のテスト
tools/
  serve.lisp                        Web UI を起動する
  export-static.lisp                Web UI を静的サイトとして書き出す
  generate-connectives-ledger.lisp  06-connectives.ledger を生成し直す
  generate-arithmetic-ledger.lisp   08-arithmetic / 09-order / 10-division を生成し直す
docs/guide.md            機能ごとの詳しい説明
backup/                  カーネルから外した機能（元のコードと復元の手順。読み込まれない）
```


## テスト

```bash
sbcl --non-interactive \
     --eval '(require :asdf)' \
     --eval '(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))' \
     --eval '(asdf:test-system :ledger-kernel)'        # カーネル（301 件）
```

Web UI のテストは `(asdf:test-system :ledger-kernel/web)` です（41 件。HTTP は使いません）。
各チェックが `[pass]` / `[FAIL]` を出力し、最後に集計を表示します。`[FAIL]` が
1つでもあると `asdf:test-system` はエラーになります。

テストには、誤った証明が拒否されることを確かめる「攻撃」のテストが多く含まれて
います（変数の捕獲、側条件の違反、演繹定理の誤用、ファイルへのコードの埋め込み、
照合の故障 など）。コードを変更したときは、**`[FAIL]` 0** と **コンパイル警告 0** を
確認してください。個別のテスト群は、`(asdf:load-system :ledger-kernel/tests)` の
あと `(run-zf-self-tests)` のように呼べます（一覧は `tests/run.lisp`）。


## 既知の限界と今後

- **ライブラリが小さい**: ZF は空集合まで。対・和集合・順序対・自然数などはこれから
  です。集合論を書きやすくするクラス記法（`{x ∣ φ}`）もまだありません。
- **証明を書く手間**: 生の Hilbert 証明は長くなります。結合子の展開形との行き来は
  明示的に書く必要があり、変数が衝突したときは `:inst` で手で付け替えます。
  `EXISTS-ELIM` の証人変数も手で選びます。高水準の証明の書き方や、中置記法での
  入力は、これからの課題です。
- **自動化の範囲**: `PROVE-TAUTOLOGY` は命題論理の構造しか使わず、原子の数に対して
  指数的です。
- **確定記述**: 一意でない場合の `.iota` の値の規約（junk value）はありません。
- **原子記号は束縛変数に依存できない**: 定理の中の原子記号 A は、周りで束縛された
  変数を含まない式しか表せません（束縛変数に名前がないので、捕獲が起こりえない）。
  束縛変数に依存する式は、述語スキーマ `(p x)` で書きます。現在のライブラリは
  すべてこの形で書かれていて、変更なしで通ります。
- **速度**: 束縛子を開くたびに式をたどるため、ペアノ算術のライブラリの読み込みは
  名前付きの版の約 1.5 倍の時間がかかります。
- **信頼の範囲**: 上の「信頼モデル」のとおり。独立な検証器（あるいは Metamath
  形式への書き出し）は今後の課題です。
- **Web UI**: 検証はできますが、証明を定理として登録する機能はまだありません。
  `/api/check` は読み込みの際に記号を作るので、外部に公開するには追加の制限が必要です。

# deploy/ — Ledger のお試しサーバーを VPS で公開する

ブラウザでライブラリを閲覧し、エディタで書いた証明をその場で検証できるサーバーを、
nginx の後ろに置いて公開するための設定例です。サーバーは台帳に何も書き込みません
（閲覧と検証だけ）。

| ファイル | 置き場所 | 内容 |
|---|---|---|
| `ledger_server.service` | `/etc/systemd/system/` | SBCL でサーバーを常駐させる systemd ユニット |
| `ledger_server.conf` | `/etc/nginx/conf.d/` | サブドメインから `127.0.0.1:35938` への転送と、検証 API の頻度制限 |

ユーザー名 `centos`、置き場所 `/home/centos/public/ledger-kernel`、ポート `35938`、
サブドメイン `ledger.rndiis.com` は例です。環境に合わせて書き換えてください。

## 手順

1. **SBCL を入れる**（CentOS / Rocky / Alma なら EPEL から）

   ```bash
   sudo dnf install epel-release && sudo dnf install sbcl
   ```

2. **Quicklisp で Hunchentoot と yason を入れる**（初回だけ）

   ```bash
   curl -O https://beta.quicklisp.org/quicklisp.lisp
   sbcl --load quicklisp.lisp \
        --eval '(quicklisp-quickstart:install)' \
        --eval '(ql:add-to-init-file)' \
        --eval '(ql:quickload (list :hunchentoot :yason))' --quit
   ```

   `ql:add-to-init-file` で `~/.sbclrc` から Quicklisp が読み込まれるようになり、
   `tools/serve.lisp` はそれを使って両方を読み込みます。

3. **リポジトリを置く**

   ```bash
   mkdir -p ~/public && cd ~/public
   git clone <リポジトリの URL> ledger-kernel     # private なら deploy key などで
   ```

4. **手元で起動を確かめる**

   ```bash
   cd ~/public/ledger-kernel
   PORT=35938 LEDGER_CHECK_TIMEOUT=5 sbcl --load tools/serve.lisp
   # 別の端末で
   curl -s http://127.0.0.1:35938/api/worlds
   ```

   起動には 10 秒ほどかかります（全ライブラリの全証明を検証し直すため）。

5. **systemd に登録する**（`ledger_server.service` の先頭のコメントのとおり）

   ```bash
   sudo cp deploy/ledger_server.service /etc/systemd/system/
   sudo systemctl daemon-reload
   sudo systemctl enable --now ledger_server
   sudo systemctl status ledger_server
   ```

6. **nginx と証明書**

   ```bash
   sudo cp deploy/ledger_server.conf /etc/nginx/conf.d/
   sudo nginx -t && sudo systemctl reload nginx
   sudo certbot --nginx -d ledger.rndiis.com
   ```

   SELinux が有効な場合、nginx から任意のポートへの転送には
   `sudo setsebool -P httpd_can_network_connect 1` が必要です（既存のサービスで
   すでに設定済みなら不要）。

## 公開にあたっての制限

サーバー側（`tools/serve.lisp` の環境変数、`web/server.lisp`）:

- 送られた証明は `web/safe-read.lisp` で読みます。Lisp の `read` は使わず、
  既存の記号だけを受け付け、新しい記号を作りません。`#.` などの読み取りマクロ、
  文字列、200 段を超える入れ子は拒否します。
- 1 件の検証は `LEDGER_CHECK_TIMEOUT` 秒（例では 5 秒）で打ち切ります。
- 同時に走る検証は `LEDGER_MAX_CHECKS` 件（例では 2 件）までで、それを超えた
  要求にはすぐに 503 を返します。
- 要求の本文は 256 KB まで。スタックを使い切るような入力も、エラーとして
  答えてサーバーは動き続けます。
- 検証結果のキャッシュ（メモ化）は無効のままです（上限なく育つため）。

nginx 側（`ledger_server.conf`）: 検証 API は 1 アドレスあたり毎分 20 件まで
（瞬間的に 5 件まで）。

systemd 側（`ledger_server.service`）: Lisp のヒープは 512 MB、プロセスの
メモリは 768 MB まで。リポジトリは読み取り専用で、落ちたら 5 秒後に再起動します。

## 更新

```bash
cd ~/public/ledger-kernel && git pull
sudo systemctl restart ledger_server
```

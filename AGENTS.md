# AGENTS

## 環境構築

`elan` がい
以下のコマンドで elan をインストールします。OS に応じて適切なコマンドを使用してください。

```bash
# Unix 系 OS の場合
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

```bash
# Windows の場合
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

以下のコマンドで `elan` が使えるか確認します。

```bash
elan --version
```

このプロジェクトでは Mathlib を使用しているので、以下のコマンドで Mathlib のビルド済みキャッシュを取得します。

```bash
# プロジェクトのルートディレクトリで実行
lake exe cache get
```

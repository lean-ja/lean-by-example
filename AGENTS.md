# AGENTS.md

このファイルは、OpenAI Codex などの AI エージェントに向けた指示を記述したファイルです。

## 環境構築

### elan のインストール

Lean のバージョンマネージャーである [elan](https://github.com/leanprover/elan) をインストールします。

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

インストール後、elan にパスを通します：

```bash
source ~/.elan/env
```

### Mathlib キャッシュの取得

このプロジェクトは [Mathlib](https://github.com/leanprover-community/mathlib4) に依存しています。ビルドを高速化するため、以下のコマンドでビルド済みキャッシュを取得してください。`lean-toolchain` で指定されたツールチェーンは、`lake` コマンドの初回実行時に elan によって自動的にインストールされます。

```bash
lake exe cache get!
```

### プロジェクトのビルド

```bash
lake build
```

## Git の設定

コミットを行う際は、以下の名前とメールアドレスを使用してください：

```bash
git config user.name "codex"
git config user.email "codex@openai.com"
```

# AGENTS

## 環境構築について

このリポジトリのための開発環境のセットアップの際は、以下を実行してください。

```bash
#!/bin/bash

# スクリプトをエラー時に中断
set -e

# 必要なディレクトリ・変数の設定
USER_NAME=${USER:-vscode}
HOME_DIR="/home/$USER_NAME"
export HOME="$HOME_DIR"
export PATH="$HOME_DIR/.elan/bin:$HOME_DIR/.cargo/bin:$PATH"

# 必要な依存のインストール（curl など）
echo "[1/6] Installing dependencies..."
sudo apt get update
sudo apt get install -y curl build-essential

# elan のインストール
echo "[2/6] Installing elan..."
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# Rust のインストール
echo "[3/6] Installing Rust..."
RUST_VERSION=stable
curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain ${RUST_VERSION}

# PATH の確認
echo "[4/6] Ensuring PATH is updated..."
echo 'export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"' >> "$HOME/.bashrc"

# mdBook とプラグインのインストール
echo "[5/6] Installing mdBook and plugins..."
cargo install --version 0.4.35 mdbook
cargo install --version 1.18.0 mdbook-admonish

echo "[6/6] Setup completed successfully!"
```

上記の内容を実行したら、`lake run build` コマンドと `lake exe cache get` コマンドを実行してください。
これにより、それぞれ markdown ファイルの生成と Mathlib のキャッシュ取得が行われます。

## コメントについて

* 変更箇所には日本語で変更の意図を丁寧にコメントしてください。
* 特に、関数やクラス、構造体には必ずドキュメントコメントを付けてください。
* 意図のわからない具体的な数字（マジックナンバー）がないように説明を補ってください。

## スタイルについて

* 再利用可能な処理は積極的に関数に切り出してください。

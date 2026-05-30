---
name: setup
description: このリポジトリの実装のために環境構築を新規に行うときに使う。
---

# 環境構築

このリポジトリの実装のために環境構築を新規に行うときに使う。
ローカルで作業している場合は、既に環境構築が完了しているはずなので使用しない。

## git と curl のインストール

git と curl がインストールされていることを確認します。

```bash
git --version
curl --version
```

インストールされていなければインストールしてください。

## elan のインストール

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

## Mathlib のキャッシュの取得

このプロジェクトでは Mathlib を使用しているので、以下のコマンドで Mathlib のビルド済みキャッシュを取得します。

```bash
# プロジェクトのルートディレクトリで実行
lake exe cache get
```

## mdbook のインストール

出力された HTML を確認する必要が生じた場合は、mdbook をインストールします。
`.devcontainer/Dockerfile` を参考にしてインストールしてください。

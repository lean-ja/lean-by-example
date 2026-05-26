---
name: codex-git-identity
description: Codex が git commit コマンドを実行するときに、専用の Git author/committer 名とメールアドレスを使うように指示する。
---

# Codex Git Identity

Codex が `git commit` を実行する前に、コミットの author/committer が Codex 用の Git identity になるよう確認する。終わったら元に戻す。

## 基本方針

- まず repo-local の Git 設定を使う。
- グローバル設定は、ユーザーが明示的に依頼しない限り変更しない。

## 手順

1. 後で戻すときのために現在の git config を確認する。
   ```powershell
   git config --global user.name
   git config --global user.email
   ```

2. Codex 用の認証情報に設定する。
   ```powershell
   git config user.name Codex
   git config user.email codex@openai.com
   ```

3. 通常通りコミットする。

4. コミット後、元の設定に戻す。

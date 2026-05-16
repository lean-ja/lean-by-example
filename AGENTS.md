# codex 向けの指示

## 環境構築

以下のコマンドで elan をインストールし、その後PATHを通してください。

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

## git config の一時的変更

コミットを指示された場合、`git config` を一時的に変更して、コミットの著者を codex にしてください。
コミット後に、必ず元に戻してください。

# README

これは、Lean(正確には elan, lake, lean) のインストール手順を検証するための Dockerfile です。

## 使い方

Dockerfile をビルドしてイメージを作成するには、以下のコマンドを実行します。

```bash
docker build \
  --file Docker/Dockerfile.xxx \
  --tag install-lean:xxx .
```

ビルドしたイメージを使ってコンテナを起動し、中に入ってコマンドを実行するには以下を実行します。

```bash
docker run --rm -it install-lean:xxx bash
```

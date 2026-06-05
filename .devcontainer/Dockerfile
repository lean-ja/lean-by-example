FROM mcr.microsoft.com/devcontainers/base:jammy

# SEO メタ情報の補正スクリプトを実行するために Node.js をインストール
RUN apt-get update && \
  apt-get install -y --no-install-recommends ca-certificates curl gnupg && \
  curl -fsSL https://deb.nodesource.com/gpgkey/nodesource-repo.gpg.key | gpg --dearmor -o /usr/share/keyrings/nodesource.gpg && \
  echo "deb [signed-by=/usr/share/keyrings/nodesource.gpg] https://deb.nodesource.com/node_22.x nodistro main" > /etc/apt/sources.list.d/nodesource.list && \
  apt-get update && \
  apt-get install -y --no-install-recommends nodejs && \
  rm -rf /var/lib/apt/lists/*

# ユーザの追加
USER vscode
WORKDIR /home/vscode
ENV HOME=/home/vscode

# elan のインストトール
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# elan のパスを通す
ENV PATH="${HOME}/.elan/bin:${PATH}"

# Rust のインストール
ENV RUST_VERSION=stable
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain ${RUST_VERSION}

# cargo 等にパスを通す
ENV PATH="${HOME}/.cargo/bin:${PATH}"

# mdbook と mdbook のプラグインのインストール
RUN cargo install --version 0.4.48 mdbook && \
  cargo install --version 1.18.0 mdbook-admonish

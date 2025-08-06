FROM mcr.microsoft.com/devcontainers/base:jammy

# ユーザの追加
USER vscode
WORKDIR /home/vscode
ENV HOME=/home/vscode

# elan のインストトール
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# elan のパスを通す
ENV PATH="/home/vscode/.elan/bin:${PATH}"

# Rust のインストール
ENV RUST_VERSION=stable
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain ${RUST_VERSION}

# cargo 等にパスを通す
ENV PATH=$PATH:$HOME/.cargo/bin

# mdbook と mdbook のプラグインのインストール
RUN cargo install --version 0.4.40 mdbook && \
  cargo install --version 1.18.0 mdbook-admonish

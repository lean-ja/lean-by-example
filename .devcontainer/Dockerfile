FROM mcr.microsoft.com/devcontainers/base:jammy

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

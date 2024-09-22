/**
 * lean4 のコードブロック内に、Lean 4 web playground へジャンプするボタンを追加する
 */
function blockPlay() {
  const array = Array.from(document.querySelectorAll(".language-lean"));
  for (const code_block of array) {
    const pre_block = code_block.parentElement;

    // lean4 web editor へのリンクを生成する
    const escaped_code = encodeURIComponent(code_block.textContent);
    const url = `https://live.lean-lang.org/#code=${escaped_code}`;

    // ボタンを生成する
    const buttons = pre_block.querySelector(".buttons");
    const leanWebButton = document.createElement("button");
    leanWebButton.className = "fa fa-external-link lean-web-button";
    leanWebButton.hidden = true;
    leanWebButton.title = "Run on lean4 playground";
    leanWebButton.setAttribute("aria-label", leanWebButton.title);

    // ボタンを挿入する
    buttons.insertBefore(leanWebButton, buttons.firstChild);

    // ボタンをクリックしたときに、lean4 web editor を開く
    leanWebButton.addEventListener("click", (e) => {
      open(url);
    });
  }
}

blockPlay();

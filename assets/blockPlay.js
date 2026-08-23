/**
 * lean4 のコードブロック内に、Lean 4 web playground へジャンプするボタンを追加する
 */
function blockPlay() {
  const array = Array.from(document.querySelectorAll(".language-lean"));
  for (const codeBlock of array) {
    const preBlock = codeBlock.closest("pre");
    if (!preBlock) continue;

    const playIconTemplate = document.querySelector("#fa-play");
    if (!playIconTemplate) continue;

    // lean4 web editor へのリンクを生成する
    const escapedCode = encodeURIComponent(codeBlock.textContent);
    const url = `https://live.lean-lang.org/#code=${escapedCode}`;

    // ボタンを生成する
    let buttons = preBlock.querySelector(".buttons");
    if (!buttons) {
      buttons = document.createElement("div");
      buttons.className = "buttons";
      preBlock.insertBefore(buttons, preBlock.firstChild);
    }

    const leanWebButton = document.createElement("button");
    leanWebButton.type = "button";
    leanWebButton.className = "lean-web-button";
    leanWebButton.title = "Run on Lean 4 playground";
    leanWebButton.setAttribute("aria-label", leanWebButton.title);
    leanWebButton.appendChild(playIconTemplate.content.cloneNode(true));

    // ボタンを挿入する
    buttons.insertBefore(leanWebButton, buttons.firstChild);

    // ボタンをクリックしたときに、lean4 web editor を開く
    leanWebButton.addEventListener("click", () => {
      window.open(url, "_blank", "noopener");
    });
  }
}

blockPlay();

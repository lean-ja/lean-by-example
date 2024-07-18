Array.from(document.querySelectorAll(".language-lean")).forEach(function (code_block) {
  let pre_block = code_block.parentElement;

  // lean4 web editor へのリンクを生成する
  let escaped_code = encodeURIComponent(code_block.textContent);
  let url = `https://live.lean-lang.org/#code=${escaped_code}`;

  // ボタンを生成する
  let buttons = pre_block.querySelector(".buttons");
  let leanWebButton = document.createElement('button');
  leanWebButton.className = 'fa fa-external-link lean-web-button';
  leanWebButton.hidden = true;
  leanWebButton.title = 'Run on lean4 playground';
  leanWebButton.setAttribute('aria-label', leanWebButton.title);

  // ボタンを挿入する
  buttons.insertBefore(leanWebButton, buttons.firstChild);

  // ボタンをクリックしたときに、lean4 web editor を開く
  leanWebButton.addEventListener('click', function (e) {
    open(url);
  });
});

/**
 * mdbook の "Suggest an edit" ボタンを改造し、
 * lean4 web editor へのリンクにしてしまう
 */

// 編集ボタンのアイコン部分の `i` 要素
const editButtonIcon = document.querySelector('#git-edit-button');
editButtonIcon.className = 'fa fa-play';

// 編集ボタンを表す `a` 要素
const editButtonLink = editButtonIcon.parentElement;
editButtonLink.title = 'Run on Lean 4 playground';
editButtonLink.ariaLabel = editButtonLink.title;

// 拡張子が `.md` になっているので `.lean` に修正する
editButtonLink.href = editButtonLink.href.replace(/\.md$/, '.lean');

// Lean ファイルがあるのは `src` ではなく `Examples` ディレクトリ
editButtonLink.href = editButtonLink.href.replace('/src/', '/Examples/');

// ボタンをクリックしたときに以下を実行
editButtonLink.addEventListener('click', async function (e) {
  // デフォルトの挙動をキャンセル
  e.preventDefault();

  fetch(editButtonLink.href)
    .then(response => response.text())
    .then(body => {
      const escaped_code = encodeURIComponent(body);
      const url = `https://live.lean-lang.org/#code=${escaped_code}`;
      open(url);
    });
});

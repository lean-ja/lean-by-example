/**
 * mdbook の "Suggest an edit" ボタンを改造し、
 * lean4 web editor へのリンクにしてしまう
 *
 * 一瞬元のアイコンが表示されるのを防ぐためにHTML側で上書きを行っていることに注意
 */
function filePlay() {
  // 編集ボタンのアイコン部分の `i` 要素
  const editButtonIcon = document.querySelector("#lean-play-button");

  // 編集ボタンを表す `a` 要素
  const editButtonLink = editButtonIcon.parentElement;

  // 拡張子が `.md` になっているので `.lean` に修正する
  editButtonLink.href = editButtonLink.href.replace(/\.md$/, ".lean");

  // Lean ファイルがあるのは `booksrc` ではなく `Examples` ディレクトリ
  editButtonLink.href = editButtonLink.href.replace("/booksrc/", "/Examples/");

  // 演習問題のファイルのみ、`Examples` ディレクトリではなくて `Exercise` ディレクトリにある
  editButtonLink.href = editButtonLink.href.replace(
    "/Examples/Exercise/",
    "/Exercise/",
  );

  // URL を書き換える
  fetch(editButtonLink.href)
    .then((response) => response.text())
    .then((body) => {
      const escaped_code = encodeURIComponent(body);
      const url = `https://live.lean-lang.org/#code=${escaped_code}`;
      editButtonLink.href = url;
    });
}

filePlay();

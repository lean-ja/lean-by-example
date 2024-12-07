/**
 * mdbook の "Suggest an edit" ボタンを改造し、
 * lean4 web editor へのリンクにしてしまう
 *
 * 一瞬元のアイコンが表示されるのを防ぐためにHTML側で上書きを行っていることに注意
 */
function filePlay() {
  // ボタンのアイコン部分の `i` 要素
  const playButtonIcon = document.querySelector("#lean-play-button");

  // ボタンを表す `a` 要素
  const playButtonLink = playButtonIcon.parentElement;

  // 拡張子が `.md` になっているので `.lean` に修正する
  playButtonLink.href = playButtonLink.href.replace(/\.md$/, ".lean");

  // Lean ファイルがあるのは `booksrc` ではなく `LeanByExample` ディレクトリ
  playButtonLink.href = playButtonLink.href.replace(
    "/booksrc/",
    "/LeanByExample/",
  );

  // URL を書き換える
  fetch(playButtonLink.href)
    .then((response) => response.text())
    .then((body) => {
      const escaped_code = encodeURIComponent(body);
      const url = `https://live.lean-lang.org/#code=${escaped_code}`;
      playButtonLink.href = url;
    });
}

filePlay();

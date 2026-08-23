/**
 * mdbook の "Suggest an edit" ボタンを改造し、
 * lean4 web editor へのリンクにしてしまう
 *
 */
function filePlay() {
  const editButtonIcon = document.querySelector("#git-edit-button");
  const playIconTemplate = document.querySelector("#fa-play");
  if (!editButtonIcon || !playIconTemplate) return;

  // ボタンを表す `a` 要素
  const playButtonLink = editButtonIcon.closest("a");
  if (!playButtonLink) return;

  editButtonIcon.replaceWith(playIconTemplate.content.cloneNode(true));
  playButtonLink.title = "Run on Lean 4 playground";
  playButtonLink.ariaLabel = playButtonLink.title;
  playButtonLink.target = "_blank";
  playButtonLink.rel = "noopener";

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

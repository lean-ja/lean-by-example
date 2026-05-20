/**
 * サイドバー非表示ページの制御スクリプト
 *
 * SUMMARY.md の `# 付録` セクションに列挙されたページは、
 * HTMLとしては生成されるが、サイドバーには表示しない。
 * このスクリプトは、その `# 付録` セクションとその配下の項目を
 * サイドバーから取り除く。また、セクション直前の区切り線も合わせて非表示にする。
 */
document.addEventListener('DOMContentLoaded', function () {
  const chapterList = document.querySelector('ol.chapter');
  if (!chapterList) return;

  const items = Array.from(chapterList.children);
  let inHiddenSection = false;

  for (let i = 0; i < items.length; i++) {
    const item = items[i];

    if (item.classList.contains('part-title')) {
      // 「付録」というパートタイトルに到達したら非表示モードに入る
      if (item.textContent.trim() === '付録') {
        inHiddenSection = true;
        // 直前のスペーサー（区切り線）も合わせて非表示にする
        if (i > 0 && items[i - 1].classList.contains('spacer')) {
          items[i - 1].style.display = 'none';
        }
      } else {
        // 別のパートタイトルが来たら非表示モードを終了する
        inHiddenSection = false;
      }
    }

    if (inHiddenSection) {
      item.style.display = 'none';
    }
  }
});

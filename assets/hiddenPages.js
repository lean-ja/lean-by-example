/**
 * サイドバー非表示ページの制御スクリプト
 *
 * `Extra/` 配下のページは、HTML としては生成されるが、
 * サイドバーには表示しない。
 * このスクリプトは、サイドバーにある `Extra/` 配下へのリンク項目を取り除く。
 */
document.addEventListener('DOMContentLoaded', function () {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  const links = sidebar.querySelectorAll(
    'ol.chapter li.chapter-item > a[href^="Extra/"], ol.chapter li.chapter-item > a[href*="/Extra/"]',
  );

  links.forEach(function (link) {
    const item = link.closest('li.chapter-item');
    if (item) {
      item.remove();
    }
  });
});

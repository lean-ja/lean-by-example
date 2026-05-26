/**
 * サイドバー非表示ページの制御スクリプト
 *
 * `EXTRA/` 配下のページは、HTML としては生成されるが、
 * サイドバーには表示しない。
 * このスクリプトは、サイドバーにある `EXTRA/` 配下へのリンク項目を取り除く。
 */
document.addEventListener('DOMContentLoaded', function () {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  const links = sidebar.querySelectorAll(
    'ol.chapter li.chapter-item > a[href^="EXTRA/"], ol.chapter li.chapter-item > a[href*="/EXTRA/"]',
  );

  links.forEach(function (link) {
    const item = link.closest('li.chapter-item');
    if (item) {
      item.remove();
    }
  });
});

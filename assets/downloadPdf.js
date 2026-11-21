/** mdBook の印刷ボタンを最新版 PDF のダウンロードリンクにする。 */
function downloadPdf() {
  const printButton = document.querySelector("#print-button")?.closest("a");
  if (!printButton) return;

  printButton.href =
    "https://github.com/lean-ja/lean-by-example/releases/download/latest/book.pdf";
  printButton.title = "最新版の PDF をダウンロード";
  printButton.ariaLabel = printButton.title;
  printButton.download = "book.pdf";
}

downloadPdf();

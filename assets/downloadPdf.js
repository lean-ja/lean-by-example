/** mdBook の印刷ボタンを、PDF の公開状況に応じて有効化・無効化する。 */
async function downloadPdf() {
  const printButton = document.querySelector("#print-button")?.closest("a");
  if (!printButton) return;

  // mdBook が生成したリンクを基準にすると、下位ページや 404 でも解決できる。
  const printUrl = printButton.href;

  // 確認中や取得失敗時も、元の印刷ページには移動させない。
  printButton.removeAttribute("href");
  printButton.removeAttribute("download");
  printButton.setAttribute("role", "link");
  printButton.setAttribute("aria-disabled", "true");
  printButton.tabIndex = 0;
  printButton.title = "ダウンロード可能なPDFがありません";
  printButton.ariaLabel = printButton.title;

  try {
    const response = await fetch(new URL("pdf.json", printUrl), {
      cache: "no-store",
    });
    if (!response.ok) return;

    const metadata = await response.json();
    if (!metadata.available || !/^[a-f0-9]{64}$/.test(metadata.sha256)) return;

    const pdfUrl = new URL("lean-by-example.pdf", printUrl);
    pdfUrl.searchParams.set("v", metadata.sha256);
    printButton.href = pdfUrl.href;
    printButton.download = "lean-by-example.pdf";
    printButton.removeAttribute("aria-disabled");
    printButton.title = "PDF をダウンロード";
    printButton.ariaLabel = printButton.title;
  } catch {
    // 公開済み PDF を確認できなければ、無効のままにする。
  }
}

downloadPdf();

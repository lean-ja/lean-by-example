document.addEventListener('DOMContentLoaded', function() {
  // サイトのベースURL（ローカル環境では動作させないため、固定URLを使用）
  const siteBaseUrl = "https://lean-ja.github.io/lean-by-example/";
  const summaryMdUrl = "https://raw.githubusercontent.com/lean-ja/lean-by-example/main/booksrc/SUMMARY.md";

  // キャッシュ用の変数
  let summaryLinks = null;

  // サイドバーの「ランダムページ」リンクを検索・設定
  const sidebarLinks = document.querySelectorAll('.sidebar-scrollbox a');
  let randomPageLink = null;

  // サイドバーから「ランダムページ」というテキストを持つリンクを探す
  for (const link of sidebarLinks) {
    if (link.textContent.trim() === 'ランダムページ') {
      randomPageLink = link;
      break;
    }
  }

  // ランダムページリンクが見つかった場合、クリックイベントを設定
  if (randomPageLink) {
    randomPageLink.href = 'javascript:void(0)'; // 通常のリンクとしての動作を無効化
    randomPageLink.addEventListener('click', goToRandomPage);
  }

  // ランダムページに移動する関数
  function goToRandomPage() {
    // キャッシュがあれば利用し、なければSUMMARY.mdからリンクを取得
    if (summaryLinks && summaryLinks.length > 0) {
      goToRandomLinkFromSummary(summaryLinks);
    } else {
      getSummaryLinks().then(links => {
        if (links && links.length > 0) {
          // リンクをキャッシュ
          summaryLinks = links;
          goToRandomLinkFromSummary(links);
        } else {
          console.error('SUMMARY.mdからリンクを取得できませんでした');
          // 本番サイトのインデックスページに移動
          window.location.href = siteBaseUrl;
        }
      });
    }
  }

  // SUMMARY.mdからリンクを取得する関数
  function getSummaryLinks() {
    return fetch(summaryMdUrl)
      .then(response => {
        if (!response.ok) {
          throw new Error(`SUMMARY.mdの取得に失敗しました: ${response.status}`);
        }
        return response.text();
      })
      .then(markdown => {
        // Markdownからリンクを抽出する正規表現
        const linkRegex = /\[([^\]]+)\]\(([^)]+)\)/g;
        let match;
        let links = [];

        // Markdownからすべてのリンクを抽出
        while ((match = linkRegex.exec(markdown)) !== null) {
          const linkText = match[1];
          const linkUrl = match[2];

          // 「ランダムページ」というリンク自体は除外
          if (linkText.trim() === 'ランダムページ') {
            continue;
          }

          try {
            // #で始まるアンカーリンクやhttpで始まる外部リンクは除外
            if (!linkUrl.startsWith('#') && !linkUrl.startsWith('http')) {
              // .mdの拡張子を.htmlに置換
              let processedUrl = linkUrl.replace(/\.md$/, '.html');

              // 先頭に/が付いている場合は除去
              if (processedUrl.startsWith('/')) {
                processedUrl = processedUrl.substring(1);
              }

              // README.htmlで終わるURLは除外
              if (processedUrl.endsWith('README.html') || processedUrl === 'README.html') {
                continue;
              }

              // 最終的に本番サイトのURLとして構築
              const fullUrl = siteBaseUrl + processedUrl;

              // 本番サイトのURLとしてリンクを追加
              links.push(fullUrl);
            }
          } catch (e) {
            console.warn('無効なURL:', linkUrl, e);
          }
        }

        // 有効なリンクだけをフィルタリング（localhost関連の除外は不要になった）
        const validLinks = links.filter(url => {
          return url &&
            !url.endsWith('print.html') &&
            !url.endsWith('404.html') &&
            !url.endsWith('SUMMARY.html') &&
            url !== siteBaseUrl;
        });

        console.log('SUMMARY.mdから抽出された有効なリンク:', validLinks);
        return validLinks;
      })
      .catch(error => {
        console.error('SUMMARY.mdの処理中にエラーが発生しました:', error);
        return [];
      });
  }

  // SUMMARY.mdから取得したリンクからランダムに選択して移動する関数
  function goToRandomLinkFromSummary(links) {
    if (!links || links.length === 0) {
      console.warn('有効なリンクが見つかりませんでした');
      window.location.href = siteBaseUrl;
      return;
    }

    // 現在のページのフルURLを取得
    const currentPage = window.location.href;

    // 現在のページを除外（完全なURLで比較）
    const otherLinks = links.filter(url => url !== currentPage);

    // 移動先の選択と遷移
    if (otherLinks.length > 0) {
      // 現在のページ以外のリンクがある場合
      const randomIndex = Math.floor(Math.random() * otherLinks.length);
      const selectedLink = otherLinks[randomIndex];

      // デバッグ情報
      console.log('選択されたリンク:', selectedLink);

      window.location.href = selectedLink;
    } else if (links.length > 0) {
      // 現在のページしかない場合（まれなケース）
      const randomIndex = Math.floor(Math.random() * links.length);
      const selectedLink = links[randomIndex];

      // デバッグ情報
      console.log('選択されたリンク(現在のページを含む):', selectedLink);

      window.location.href = selectedLink;
    } else {
      // リンクがない場合（エラー状態）
      window.location.href = siteBaseUrl;
    }
  }
});

document.addEventListener('DOMContentLoaded', function() {
  // 現在のベースURLを取得（ローカルでも動作するように）
  const baseUrl = window.location.origin + window.location.pathname.split('/').slice(0, -1).join('/') + '/';
  const summaryMdUrl = "https://raw.githubusercontent.com/lean-ja/lean-by-example/main/booksrc/SUMMARY.md";

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
    // まず現在のページからリンクを収集
    collectLinksFromCurrentPage()
      .then(links => {
        if (links.length > 0) {
          // 収集したリンクからランダムに選択して移動
          navigateToRandomPage(links);
        } else {
          // 現在のページからリンクが取得できなかった場合はSUMMARY.mdを試す
          collectLinksFromSummaryMd();
        }
      });
  }

  // 現在のページからリンクを収集する関数
  function collectLinksFromCurrentPage() {
    return new Promise((resolve) => {
      let links = [];

      // サイドバーからリンクを収集（MDBookのサイドバーナビゲーション）
      const sidebarLinks = Array.from(document.querySelectorAll('.sidebar-scrollbox a[href]'))
        .map(a => a.getAttribute('href')) // href属性の値を取得（相対パス）
        .filter(href => isValidPageUrl(href));
      links = [...links, ...sidebarLinks];

      // 章リンクからリンクを収集（MDBookのチャプターリンク）
      const chapterLinks = Array.from(document.querySelectorAll('.chapter a[href]'))
        .map(a => a.getAttribute('href'))
        .filter(href => isValidPageUrl(href));
      links = [...links, ...chapterLinks];

      // コンテンツ内のリンクも収集
      const contentLinks = Array.from(document.querySelectorAll('.content a[href]'))
        .map(a => a.getAttribute('href'))
        .filter(href => isValidPageUrl(href));
      links = [...links, ...contentLinks];

      // メニュー内のリンクを収集
      const menuLinks = Array.from(document.querySelectorAll('.menu-title a[href], .theme-popup a[href]'))
        .map(a => a.getAttribute('href'))
        .filter(href => isValidPageUrl(href));
      links = [...links, ...menuLinks];

      // ナビゲーションリンク（前/次のページ）を収集
      const navLinks = Array.from(document.querySelectorAll('.nav-chapters a[href]'))
        .map(a => a.getAttribute('href'))
        .filter(href => isValidPageUrl(href));
      links = [...links, ...navLinks];

      // リンクがあまりにも少ない場合は、ページにリンクが十分に読み込まれていない可能性があるため
      // トップページからリンクを取得
      if (links.length < 3) {
        collectLinksFromMainIndex().then(mainLinks => {
          resolve([...new Set([...links, ...mainLinks])]); // 重複を削除
        });
      } else {
        resolve([...new Set(links)]); // 重複を削除
      }
    });
  }

  // SUMMARY.mdからリンクを収集する関数
  function collectLinksFromSummaryMd() {
    fetch(summaryMdUrl)
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

          try {
            // #で始まるアンカーリンクは除外
            if (!linkUrl.startsWith('#')) {
              // .mdの拡張子を.htmlに置換
              let processedUrl = linkUrl.replace(/\.md$/, '.html');
              // 先頭に/が付いている場合は除去
              if (processedUrl.startsWith('/')) {
                processedUrl = processedUrl.substring(1);
              }
              links.push(processedUrl); // 相対パスのまま保持
            }
          } catch (e) {
            console.warn('無効なURL:', linkUrl);
          }
        }

        if (links.length > 0) {
          navigateToRandomPage(links);
        } else {
          // 最終手段：オンラインでMDBookのメイン目次を解析
          collectLinksFromMainIndex();
        }
      })
      .catch(error => {
        console.error('SUMMARY.mdの処理中にエラーが発生しました:', error);
        collectLinksFromMainIndex();
      });
  }

  // メインインデックスページからリンクを収集する関数（最終手段）
  function collectLinksFromMainIndex() {
    return new Promise((resolve) => {
      // インデックスページを取得（相対パスでアクセス）
      fetch('index.html')
        .then(response => response.text())
        .then(html => {
          const parser = new DOMParser();
          const doc = parser.parseFromString(html, 'text/html');

          let allLinks = [];

          // サイドバーリンクを収集
          const sidebarLinks = Array.from(doc.querySelectorAll('.sidebar-scrollbox a[href]'))
            .map(a => a.getAttribute('href')) // 相対パスを取得
            .filter(href => isValidPageUrl(href));
          allLinks = [...allLinks, ...sidebarLinks];

          // コンテンツリンクを収集
          const contentLinks = Array.from(doc.querySelectorAll('.content a[href]'))
            .map(a => a.getAttribute('href')) // 相対パスを取得
            .filter(href => isValidPageUrl(href));
          allLinks = [...allLinks, ...contentLinks];

          resolve([...new Set(allLinks)]); // 重複を削除
        })
        .catch(error => {
          console.error('メインインデックスの処理中にエラーが発生しました:', error);
          // エラー時は空の配列を返す
          resolve([]);
        });
    });
  }

  // 有効なページURLかチェックする関数
  function isValidPageUrl(url) {
    try {
      // 絶対URLと相対URLの両方に対応
      if (url.startsWith('http')) {
        // 絶対URLの場合
        const parsedUrl = new URL(url);
        // 同じオリジンかチェック
        return parsedUrl.origin === window.location.origin &&
               !url.includes('#') &&
               !url.endsWith('print.html') &&
               !url.endsWith('404.html') &&
               !url.endsWith('SUMMARY.html');
      } else {
        // 相対URLの場合
        return url &&
               !url.startsWith('#') &&
               !url.endsWith('print.html') &&
               !url.endsWith('404.html') &&
               !url.endsWith('SUMMARY.html') &&
               url !== './';
      }
    } catch (e) {
      return false;
    }
  }

  // ランダムに選択したページに移動する関数
  function navigateToRandomPage(links) {
    if (links.length) {
      // 重複を除去
      const uniqueLinks = [...new Set(links)];

      // 現在のページパスを取得（相対パスで比較できるように）
      const currentPath = window.location.pathname;
      const currentPage = currentPath.split('/').pop(); // ファイル名のみ取得

      // 現在のページを除外（相対パスで比較）
      const otherLinks = uniqueLinks.filter(url => {
        const urlPath = url.split('/').pop(); // URLのファイル名部分
        return urlPath !== currentPage;
      });

      // リンクがあれば、ランダムに選択して移動
      if (otherLinks.length > 0) {
        const randomIndex = Math.floor(Math.random() * otherLinks.length);
        window.location.href = otherLinks[randomIndex]; // 相対パスで移動
      } else if (uniqueLinks.length > 0) {
        // 他のページがなければ、現在のページを含むリストからランダム選択
        const randomIndex = Math.floor(Math.random() * uniqueLinks.length);
        window.location.href = uniqueLinks[randomIndex]; // 相対パスで移動
      } else {
        // リンクが一つも見つからない場合はインデックスページに移動
        window.location.href = 'index.html'; // 相対パスで移動
        console.warn('有効なリンクが見つからなかったため、トップページに移動します');
      }
    } else {
      // リンクが一つも見つからない場合はインデックスページに移動
      window.location.href = 'index.html'; // 相対パスで移動
      console.warn('有効なリンクが見つからなかったため、トップページに移動します');
    }
  }
});

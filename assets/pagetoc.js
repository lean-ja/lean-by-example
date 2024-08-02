"use strict";

/** クライアントの環境がPCかどうか判定する */
function isDesktop() {
  const userAgent = navigator.userAgent;
  const mobileRegex = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i;
  return !mobileRegex.test(userAgent);
}

/** 本体の処理 */
function pageToc() {
  function forEach(elems, fun) {
    Array.prototype.forEach.call(elems, fun);
  }

  function getPagetoc(){
    return document.getElementsByClassName("pagetoc")[0]
  }

  function getPagetocElems() {
    return getPagetoc().children;
  }

  function getHeaders(){
    return document.getElementsByClassName("header")
  }

  // Un-active everything when you click it
  function forPagetocElem(fun) {
    forEach(getPagetocElems(), fun);
  }

  function getRect(element) {
    return element.getBoundingClientRect();
  }

  function overflowTop(container, element) {
    return getRect(container).top - getRect(element).top;
  }

  function overflowBottom(container, element) {
    return getRect(container).bottom - getRect(element).bottom;
  }

  let activeHref = location.href;

  let updateFunction = function (elem = undefined) {
    let id = elem;

    if (!id && location.href != activeHref) {
      activeHref = location.href;
      forPagetocElem(function (el) {
        if (el.href === activeHref) {
          id = el;
        }
      });
    }

    if (!id) {
      let elements = getHeaders();
      let margin = window.innerHeight / 3;

      forEach(elements, function (el, i, arr) {
        if (!id && getRect(el).top >= 0) {
          if (getRect(el).top < margin) {
            id = el;
          } else {
            id = arr[Math.max(0, i - 1)];
          }
        }
        // a very long last section
        // its heading is over the screen
        if (!id && i == arr.length - 1) {
          id = el
        }
      });
    }

    forPagetocElem(function (el) {
      el.classList.remove("active");
    });

    if (!id) return;

    forPagetocElem(function (el) {
      if (id.href.localeCompare(el.href) == 0) {
        el.classList.add("active");
        let pagetoc = getPagetoc();
        if (overflowTop(pagetoc, el) > 0) {
          pagetoc.scrollTop = el.offsetTop;
        }
        if (overflowBottom(pagetoc, el) < 0) {
          pagetoc.scrollTop -= overflowBottom(pagetoc, el);
        }
      }
    });
  };

  let elements = getHeaders();

  if (elements.length > 2) {
    // Populate sidebar on load
    window.addEventListener("load", function () {
      let pagetoc = getPagetoc();
      let elements = getHeaders();
      forEach(elements, function (el) {
        let link = document.createElement("a");
        link.appendChild(document.createTextNode(el.text));
        link.href = el.hash;
        link.classList.add("pagetoc-" + el.parentElement.tagName);
        pagetoc.appendChild(link);
        link.onclick = function () {
          updateFunction(link);
        };
      });
      updateFunction();
    });

    // Handle active elements on scroll
    window.addEventListener("scroll", function () {
      updateFunction();
    });
  } else {
    document.getElementsByClassName("sidetoc")[0].remove();
  }
}

// DOMが完全に読み込まれた後に実行
document.addEventListener('DOMContentLoaded', function() {
  if (isDesktop()) {
      let style = document.createElement('style');

      let css = `
        :root {
          --toc-width: 270px;
          --center-content-toc-shift: calc(-1 * var(--toc-width) / 2);
        }

        .nav-chapters {
          /* adjust width of buttons that bring to the previous or the next page */
          min-width: 50px;
        }

        .previous {
          /*
          adjust the space between the left sidebar or the left side of the screen
          and the button that leads to the previous page
          */
          margin-left: var(--page-padding);
        }

        @media only screen {
          main {
            display: flex;
          }

          @media (max-width: 1179px) {
            .sidebar-hidden .sidetoc {
              display: none;
            }
          }

          @media (max-width: 1439px) {
            .sidebar-visible .sidetoc {
              display: none;
            }
          }

          @media (1180px <=width <=1439px) {
            .sidebar-hidden main {
              position: relative;
              left: var(--center-content-toc-shift);
            }
          }

          @media (1440px <=width <=1700px) {
            .sidebar-visible main {
              position: relative;
              left: var(--center-content-toc-shift);
            }
          }

          .content-wrap {
            overflow-y: auto;
            width: 100%;
          }

          .sidetoc {
            margin-top: 20px;
            margin-left: 10px;
            margin-right: auto;
          }

          .pagetoc {
            position: fixed;
            /* adjust TOC width */
            width: var(--toc-width);
            height: calc(100vh - var(--menu-bar-height) - 0.67em * 4);
            overflow: auto;
          }

          .pagetoc a {
            border-left: 1px solid var(--sidebar-bg);
            color: var(--fg) !important;
            display: block;
            padding-bottom: 5px;
            padding-top: 5px;
            padding-left: 10px;
            text-align: left;
            text-decoration: none;
          }

          .pagetoc a:hover,
          .pagetoc a.active {
            background: var(--sidebar-bg);
            color: var(--sidebar-fg) !important;
          }

          .pagetoc .active {
            background: var(--sidebar-bg);
            color: var(--sidebar-fg);
          }

          .pagetoc .pagetoc-H2 {
            padding-left: 20px;
          }

          .pagetoc .pagetoc-H3 {
            padding-left: 40px;
          }

          .pagetoc .pagetoc-H4 {
            padding-left: 60px;
          }
        }
        @media screen and (max-width: 769px), print {
          .sidetoc {
            display: none;
          }
        }
      `

      // スタイル要素にCSSを挿入
      if (style.styleSheet) {
          style.styleSheet.cssText = css;
      } else {
          style.appendChild(document.createTextNode(css));
      }

      // // スタイル要素をドキュメントの<head>に追加
      document.head.appendChild(style);

      // PCの場合に実行するコード
      pageToc();
  } else {
      // モバイルデバイスの場合のコード
      console.info('pagetoc does not run on a mobile device.');
  }
});

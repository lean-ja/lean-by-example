/* previous (next) chapter へ移動するボタンが chapter list と被ってしまい押しづらい。
荒っぽい修正としてこのボタンを削除してしまうことで対応 */
"use strict";

(function removeNav() {
  // nav-wide-wrapper クラスを持つ要素を取得する
  const navigationButtons = document.querySelector('nav.nav-wide-wrapper');

  // この要素が存在する場合、削除する
  if (navigationButtons) {
    navigationButtons.remove();
  }
})();

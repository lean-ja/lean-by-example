// `Mathlib4 Help`というテキストをアンカーとして持つ`a`要素のリンク先を書き換える
document.addEventListener('DOMContentLoaded', () => {
  const link = document.querySelector('a[href="Mathlib4Help.html"]');
  if (link) {
    link.href = 'https://seasawher.github.io/mathlib4-help/';
  }
});

import ProofWidgets

open ProofWidgets Jsx

-- Markdown と TeX を表示する
#html <MarkdownDisplay contents={"
  ## Riemann zeta function

  The Riemann zeta function is defined as
  $$
  \\zeta(s) = \\sum_{n=1}^∞ \\frac{1}{n^s}
  $$

  for $\\mathrm{Re} (s) > 0$.
"}/>

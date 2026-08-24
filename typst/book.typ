#let conf(
  title: none,
  subtitle: none,
  authors: (),
  keywords: (),
  date: none,
  abstract-title: none,
  abstract: none,
  thanks: none,
  cols: 1,
  margin: (x: 25mm, y: 20mm),
  paper: "a4",
  lang: "ja",
  region: "JP",
  font: ("Juisee",),
  fontsize: 10.5pt,
  mathfont: none,
  codefont: ("Juisee",),
  linestretch: 1,
  sectionnumbering: none,
  linkcolor: none,
  citecolor: none,
  filecolor: none,
  pagenumbering: "1",
  doc,
) = {
  set document(title: title)

  set page(
    paper: paper,
    margin: margin,
    numbering: pagenumbering,
  )

  set text(
    font: font,
    size: fontsize,
    lang: lang,
    region: region,
  )

  set par(
    justify: true,
    leading: linestretch * 0.65em,
  )

  // PDF 内外へのリンクを青色の文字と下線で示す
  let pdf-link-color = rgb("#0969da")
  show link: it => {
    set text(fill: pdf-link-color)
    show raw.where(block: false): set text(fill: pdf-link-color)
    underline(
      stroke: 0.6pt + pdf-link-color,
      offset: 2pt,
      it,
    )
  }
  set heading(numbering: sectionnumbering)
  set raw(
    syntaxes: "lean.sublime-syntax",
    theme: "lean-light.tmTheme",
  )
  show raw: set text(font: codefont) if codefont != none

  // Markdown のバックティックに相当するインラインコード
  show raw.where(block: false): set text(fill: rgb("#a9633b"))
  show raw.where(block: false): box.with(
    fill: rgb("#fcf9f6"),
    stroke: 0.5pt + rgb("#e9e0d8"),
    radius: 3pt,
    inset: (x: 3pt, y: 1pt),
    outset: (x: 1pt, y: 2pt),
  )

  // Markdown のコードフェンスに相当するブロックコード
  show raw.where(block: true): block.with(
    width: 100%,
    breakable: true,
    fill: rgb("#f6f8fa"),
    stroke: 0.5pt + rgb("#d0d7de"),
    radius: 5pt,
    inset: (x: 12pt, y: 10pt),
    above: 0.8em,
    below: 0.8em,
  )

  // Markdown の `>` に相当するブロック引用
  show quote.where(block: true): it => block(
    width: 100%,
    breakable: true,
    fill: luma(94%),
    stroke: 0.5pt + luma(82%),
    radius: 5pt,
    inset: (x: 12pt, y: 10pt),
    above: 0.8em,
    below: 0.8em,
  )[
    #it.body
    #if it.attribution != none {
      v(0.5em)
      align(right, text(size: 0.9em, style: "italic", it.attribution))
    }
  ]

  // Markdown の独自記法 `[!UNICODE]` に相当する Unicode 入力の補足
  let unicode-alert-color = rgb("#0969da")
  show <unicode-alert>: it => block(
    width: 100%,
    breakable: true,
    stroke: (left: 3pt + unicode-alert-color),
    inset: (left: 12pt, right: 0pt, y: 4pt),
    above: 0.8em,
    below: 0.8em,
  )[
    #block(breakable: false, sticky: true)[
      #grid(
        columns: (auto, auto),
        column-gutter: 10pt,
        align: center + horizon,
        box(
          width: 1.7em,
          height: 1.35em,
          stroke: 0.9pt + unicode-alert-color,
          radius: 3pt,
          align(
            center + horizon,
            text(
              fill: unicode-alert-color,
              size: 0.65em,
              weight: "bold",
            )[U+],
          ),
        ),
        text(fill: unicode-alert-color, weight: "bold")[Unicode の入力方法],
      )
    ]
    #v(0.2em)
    #it.body
  ]

  // x.y 形式の節見出しに下線と余白を加える。
  // mdbook-pandoc は単独ファイルの先頭見出しだけを目次対象にするため、
  // その見出し（outlined: true）の直前に限って改ページする。
  show heading.where(level: 2): it => {
    if it.outlined {
      pagebreak(weak: true)
    }
    block(
      width: 100%,
      breakable: false,
      sticky: true,
      inset: (bottom: 5pt),
      below: 1.1em,
      stroke: (bottom: 0.75pt + luma(65%)),
    )[#it]
  }

  // Markdown の `#` に相当する章見出しを新しいページから始める
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    it
  }

  // 目次を独立したページにする
  show outline: it => {
    pagebreak(weak: true)
    it
    pagebreak()
  }

  // 表紙
  if title != none {
    page(numbering: none)[
      #align(center)[
        #v(25%)
        #text(size: 24pt, weight: "bold")[#title]

        #if subtitle != none {
          parbreak()
          v(1em)
          text(size: 14pt)[#subtitle]
        }

        #if authors.len() > 0 {
          v(2em)
          for author in authors {
            author.name
            linebreak()
          }
        }

        #if date != none {
          v(1em)
          date
        }
      ]
    ]
    counter(page).update(1)
  }

  // 目次と本文は Pandoc 側からここへ渡される
  doc
}

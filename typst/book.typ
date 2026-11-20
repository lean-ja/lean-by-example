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
  font: ("Source Han Serif",),
  fontsize: 10.5pt,
  headingfont: ("Noto Sans JP",),
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
  let heading-blue = rgb("#174a78")
  let rule-blue = rgb("#8fb7d8")
  let footnote-red = rgb("#8b2635")

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
    // 長いインラインコードを含む日本語の行で、両端揃えによって
    // 字間が過度に引き伸ばされるのを防ぐ。
    justify: false,
    leading: linestretch * 0.70em,
  )

  // PDF 内外へのリンクを青色の文字と下線で示す
  let pdf-link-color = rgb("#0969da")
  show link: set text(fill: pdf-link-color)
  show link: it => {
    show raw.where(block: false): set text(fill: pdf-link-color)
    underline(
      stroke: 0.6pt + pdf-link-color,
      offset: 2pt,
      it,
    )
  }
  set heading(numbering: sectionnumbering)
  // 番号なしの前付けや本文中の小見出しは、そのまま番号なしにする。
  show heading.where(level: 1, outlined: true): set heading(numbering: "第1章")
  show heading.where(level: 2, outlined: true): set heading(numbering: "1.1")
  show heading: set text(font: headingfont, fill: heading-blue)
  // 本文中の参照番号と脚注欄の番号を暗い赤色にする。
  set footnote(numbering: n => text(fill: footnote-red, str(n)))
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
  let unicode-alert-color = rgb("#4f46e5")
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

  // 各項目は新しいページから始め、節番号を二重枠で囲む。
  // mdbook-pandoc は単独ファイルの先頭見出しだけを目次対象にする。
  show heading.where(level: 2, outlined: true): it => context {
    pagebreak(weak: true)
    if it.numbering == none {
      block(
        width: 100%,
        breakable: false,
        sticky: true,
        inset: (bottom: 5pt),
        below: 1.1em,
        stroke: (bottom: 0.75pt + rule-blue),
      )[#it]
    } else {
      block(
        width: 100%,
        breakable: false,
        sticky: true,
        below: 1.1em,
      )[
        #set text(weight: "bold", fill: heading-blue)
        #set par(justify: false)
        #grid(
          columns: (auto, 1fr),
          column-gutter: 8pt,
          align: left + top,
          box(
            stroke: 0.5pt + heading-blue,
            inset: 2pt,
            box(
              stroke: 0.5pt + heading-blue,
              inset: (x: 6pt, y: 2pt),
              numbering(it.numbering, ..counter(heading).at(it.location())),
            ),
          ),
          block(
            width: 100%,
            inset: (top: 4pt, bottom: 5pt),
            stroke: (bottom: 0.75pt + rule-blue),
            it.body,
          ),
        )
      ]
    }
  }

  // 章の冒頭は、左揃えの章番号と大きなタイトルを上下に配置する。
  show heading.where(level: 1): it => context {
    pagebreak(weak: true)
    if it.outlined and it.numbering != none {
      block(
        width: 100%,
        breakable: false,
        sticky: true,
        inset: (top: 5mm),
        below: 12mm,
      )[
        #set text(fill: heading-blue, weight: "bold")
        #set par(justify: false)
        #align(left)[
          #text(size: 22pt)[第#text(size: 36pt)[#counter(heading).at(it.location()).first()]章]
          #v(18mm)
          #text(size: 22pt)[#it.body]
        ]
      ]
    } else {
      it
    }
  }

  // SUMMARY の深さで変わる見出しレベルから、原稿内の ## と ### を区別する。
  show heading.where(outlined: false): it => context {
    let parents = query(heading.where(outlined: true).before(it.location()))
    let base-level = if parents.len() > 0 { parents.last().level } else { 1 }
    let source-level = it.level - base-level + 1

    if source-level == 2 {
      block(breakable: false, sticky: true)[
        #set par(justify: false)
        #grid(
          columns: (auto, 1fr),
          column-gutter: 0.5em,
          align: left + horizon,
          rect(width: 0.3em, height: 1em, fill: heading-blue, stroke: none),
          it.body,
        )
      ]
    } else if source-level == 3 {
      block(breakable: false, sticky: true, text(fill: black, it.body))
    } else {
      it
    }
  }

  // 目次を独立したページにする
  // 「第」と和欧文間隔の分だけ字下げし、章と節の数字をそろえる。
  set outline(indent: 1.375em)
  show outline: it => {
    set text(font: headingfont)
    show heading.where(level: 1, outlined: false): set block(
      width: 100%,
      breakable: false,
      sticky: true,
      inset: (bottom: 5pt),
      below: 1.1em,
      stroke: (bottom: 0.75pt + rule-blue),
    )
    set outline.entry(fill: repeat(gap: 0.08em)[#text(size: 0.6em)[.]])
    // 目次では下線を省き、章と節の書体・色で階層を示す。
    show outline.entry.where(level: 1): entry => {
      set text(size: 1.1em, fill: heading-blue)
      show link: set text(fill: heading-blue)
      show underline: underline => underline.body
      link(entry.element.location(), entry.indented(entry.prefix(), entry.inner()))
    }
    show outline.entry.where(level: 2): entry => {
      show link: set text(fill: black)
      show underline: underline => underline.body
      let prefix = if entry.element.numbering != none { [#entry.prefix()節] }
      link(entry.element.location(), entry.indented(prefix, entry.inner()))
    }
    pagebreak(weak: true)
    it
    pagebreak()
  }

  // 表紙
  if title != none {
    page(numbering: none)[
      #align(center)[
        #v(25%)
        #text(font: headingfont, size: 24pt, weight: "bold", fill: heading-blue)[#title]

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

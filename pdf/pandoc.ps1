# markdown ファイルがある場所へ移動
Set-Location -Path "src"
  # 入力ファイルのパスを指定
  $content = Get-Content -Path "SUMMARY.md"

  # リンク部分を抜き出すための正規表現
  $regex = [regex]::new("\]\((.*\.md)\)")

  # 抽出したリンクを保存するための配列
  $links = @()

  # 入力ファイルから内部リンクの部分を抽出する
  foreach ($line in $content) {
    if ($line -match $regex) {
      $match_part = [regex]::matches($line, $regex)
      $link = $match_part.Groups[1].Value
      # Write-Host $link
      $links += $link
    }
  }

  # pandoc コマンドを実行して .typ ファイルを得る
  pandoc @links `
    --from markdown `
    --to typst `
    --output "out.typ"

  # lib.typ ファイルの内容を out.typ ファイルの先頭に追加するために、
  # 一時ファイルを作成する
  Get-Content -Path "../pdf/lib.typ" -Raw -Encoding utf8 | Out-File -FilePath "tmp.typ"

  # out.typ ファイルの内容を tmp ファイルの末尾に追加する
  Get-Content -Path "out.typ" -Raw -Encoding utf8 | Out-File -FilePath "tmp.typ" -Append

  # 不要な一時ファイルを削除する
  Remove-Item -Path "out.typ"
  Rename-Item -Path "tmp.typ" -NewName "out.typ"

  # typst コマンドを実行して .pdf ファイルを得る
  typst compile --format pdf out.typ out.pdf

  # 生成したファイルを移動させる
  Move-Item -Path "out.pdf" -Destination "../pdf/out.pdf" -Force
Set-Location -Path ".."

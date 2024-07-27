
Set-Location -Path "src"

# 入力ファイルのパスを指定
$inputFilePath = "SUMMARY.md"

$content = Get-Content -Path $inputFilePath

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
  --output out.typ

# typst コマンドを実行して .pdf ファイルを得る
typst compile --format pdf out.typ out.pdf

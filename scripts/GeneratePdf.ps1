# book.toml を動的に書き換える
Get-Content -Path "book-pdf.toml" | Add-Content -Path "book.toml"

# mdbook build を実行するが、
# このとき mdbook-pdf というバックエンドが使われてPDFの生成が行われる
mdbook build

# 古いPDFがもしあれば削除する
Remove-Item -Path "book/pdf/LeanByExample.pdf" -Force -ErrorAction SilentlyContinue

# ファイル名を変更する
Rename-Item -Path "book/pdf/output.pdf" -NewName "LeanByExample.pdf"

# 書き換えられた book.toml を元に戻す
git checkout -- book.toml

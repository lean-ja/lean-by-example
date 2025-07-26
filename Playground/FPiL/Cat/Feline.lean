/- # feline

参考：<https://lean-lang.org/functional_programming_in_lean/Hello___-World___/Worked-Example___--cat/#Functional-Programming-in-Lean--Hello___-World___--Worked-Example___--cat>


-/

/-- バッファサイズ。単位はバイト（B）。
一度に１文字ずつ読み込むと非常に遅くなるので、
バッファを使って効率的に読み込む。
ここでは20KB（= 20 × 1024 B）を一度に読み込む。
-/
def bufsize : USize := 20 * 1024

open IO FS

/--
与えられたストリーム `stream` からデータをブロック単位で読み込み、
標準出力に書き出す関数。
ファイルの終端（EOF）に達するまで繰り返し処理を行う。
-/
def dump (stream : Stream) : IO Unit := do
  -- 最初のブロックを読み込む
  let mut buf ← stream.read bufsize

  -- ストリームがEOF(ファイル終端)に達するまで以下を繰り返す
  while ! buf.isEmpty do
    -- 標準出力ストリームを取得
    let stdout ← getStdout

    -- 読み込んだデータ（バッファ）を標準出力に書き込む
    stdout.write buf

    -- 次のブロックを読み込む
    buf ← stream.read bufsize

  -- 明示的に return（省略可能）
  return ()

/--
指定されたファイル名 `filename` を開き、読み取り用のストリームを生成する関数。
ファイルが存在しない場合はエラーメッセージを出力して `none` を返す。
ファイルが存在する場合は、対応する `Stream` を `some` で包んで返す。
-/
def fileStream (filename : System.FilePath) : IO (Option Stream) := do
  -- ファイルの存在を確認
  let fileExists ← filename.pathExists

  -- ファイルが存在しない場合
  if not fileExists then
    -- 標準エラー出力を取得してエラーメッセージを表示
    let stderr ← getStderr
    stderr.putStrLn s!"File not found: {filename}"
    return none

  -- ファイルが存在する場合は、読み取り用ハンドルを作成
  let handle ← Handle.mk filename Mode.read

  -- ハンドルからストリームを生成し、`some` に包んで返す
  return (some (Stream.ofHandle handle))

/--
`process` 関数は、コマンドライン引数で与えられたファイル名リストを処理し、
各ファイルまたは標準入力の内容を出力する。

- `exitCode` は現在の終了コード（0: 成功、1: 一部失敗）
- `args` は処理対象のファイル名リスト
-/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  -- 引数が空なら、これまでの exitCode を返して終了
  | [] => pure exitCode

  -- `"-"` は標準入力を意味する
  | "-" :: args =>
    -- 標準入力ストリームを取得
    let stdin ← IO.getStdin
    -- 標準入力を出力する
    dump stdin
    -- 残りの引数を再帰的に処理
    process exitCode args

  -- 通常のファイル名が与えられた場合
  | filename :: args =>
    -- ファイルを開いてストリームを取得（失敗する可能性がある）
    let stream ← fileStream ⟨filename⟩
    match stream with
    -- ファイルが開けなかった場合：終了コードを 1 にして続行
    | none =>
      process 1 args

    -- ファイルが開けた場合：その内容を出力し、exitCode はそのまま
    | some stream =>
      dump stream
      process exitCode args

/--
`main` 関数はプログラムのエントリーポイント。
このバージョンは `List String → IO UInt32` 型を持ち、C言語で言うところの
`int main(int argc, char **argv)` に相当します。
コマンドライン引数 `args` を受け取り、それに応じてプログラムの動作を決定します。

このプログラム（`feline`）は、引数が空のときは標準入力から読み込みを行い、
そうでない場合は、与えられたファイルや `"-"`（標準入力）を順に処理します。

`lean --run .\Playground\FPiL\Feline.lean .\Playground\FPiL\test_feline.txt` で実行できます。
-/
def main (args : List String) : IO UInt32 :=
  match args with
  -- 引数がない場合は標準入力から読み込むために ["-"] を処理
  | [] => process 0 ["-"]
  -- 引数がある場合はそのまま順に処理
  | _ =>  process 0 args

-- コマンドラインで実行する代わりにこうしても良い
-- #eval main [".\\Playground\\FPiL\\test_feline.txt"]

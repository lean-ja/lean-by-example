/- # check_failure
`#check_failure` は，エラーが起こった時に成功し，エラーが起こらなければ失敗するコマンドです．エラーが起こるコードを意図的に構成したいときに便利です．
-/

#check_failure 1 + "hello"

#check_failure (rfl : 1 = 2)

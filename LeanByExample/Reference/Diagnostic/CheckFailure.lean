/- # \#check_failure
`#check_failure` は、エラーが起こった時に成功し、エラーが起こらなければ失敗するコマンドです。エラーが起こるコードを意図的に構成したいときに便利です。
-/

-- 自然数と文字列を足すことはできない
#guard_msgs (drop warning) in --#
#check_failure 1 + "hello"

-- `1 = 2` を `rfl` で証明することはできない
#guard_msgs (drop warning) in --#
#check_failure (by rfl : 1 = 2)

-- `1 + 4 = 5` は `contradiction` では示せない
#guard_msgs (drop warning) in --#
#check_failure (by contradiction : 1 + 4 = 5)

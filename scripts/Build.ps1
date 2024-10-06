<# lake run build に相当するスクリプト

lake を介することで実行が遅くなってしまうので、
lake を介することなく実行ファイルを直接叩く。 #>

./.lake/packages/mk-exercise/.lake/build/bin/mk_exercise.exe Examples/Solution Exercise

./.lake/packages/mdgen/.lake/build/bin/mdgen.exe Exercise booksrc/Exercise
./.lake/packages/mdgen/.lake/build/bin/mdgen.exe Examples booksrc

mdbook build

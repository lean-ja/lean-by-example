# linarith

`linarith` は線形算術(linear arithmetic)を行うタクティクです．Fourier-Motzkin elimination を用いて，線形な(不)等式系から矛盾を導こうとします．一般に，ゴールが `False` でないときにはゴールの否定を仮定に加えることで，ゴールを閉じようとします．

```lean
{{#include ../Examples/Linarith.lean}}
```

/-!
# How large `Interval`'s results are

`Interval` carries no generator or constraint count: it is `inf`/`sup` at a
fixed ambient index, so every entrywise operation (`plus`, `linComb`, `mtimes`,
`mtimesIntervalMat`, `minkDiff`, `smul`, `recentre`, ...) keeps that index by its
very signature, `Interval α → Interval α → Interval α` or a fixed `Fin n`,
with no runtime-computed field left to state an equality about. Restating a
signature already visible at the call site is not what issue #5 asks for.

`matMul` and `matPow` are the two operations where a genuine count exists — the
shared/contraction dimension `matMul` sums over, and the iteration count
`matPow` recurses through — but both are already explicit arguments in the
signature (`n` and the exponent), not a quantity an operation *produces*. The
only way to say more about either is to count the scalar operations spent per
entry — a running cost, which is the other kind of claim and lives in `Complexity/Time/`,
asserted against a model rather than proved from a definition.

So there is nothing here that is both non-obvious and not a scalar-operation
count. This directory accordingly holds no theorems for `Interval`, only this
paragraph saying why.
-/

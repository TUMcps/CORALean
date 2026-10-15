module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.API

/-!
# What running `PolyZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**, never `rfl` against the definition.
`Complexity/Space/` is the other kind of claim: how large a *result* is, proved.

`Complexity/Space/Theorems/BilinHIsBigO.lean` proves a pairing's result carries `(h₁+1)(h₂+1)`
generators, and `bilinCost` says every one is computed, so `mul` and `quadMap`
are quadratic in a count that `plus` grows and only `reduce` brings down.
`compactCost` is quadratic for its own reason, a pairwise merge over exponent
columns. `bilinCost` and `mapCost` take one application's price as a parameter.

The relax family is counted at `Vec ℝ n`. `eDiffCost` and `eDriftCost` price
exponent arithmetic, comparisons and parities on `ℕ`, at unit. A relaxation
merges a named pair or group, but writes the whole relaxed set, so `h` and `q` enter its
count. `relaxExpGreedyCost` takes the selection's price as a parameter, `sel` being an argument
of the operation; `cartProd` and `dependent` only place data, and cost their writes.
Each count is monotone in the sizes it takes.
-/

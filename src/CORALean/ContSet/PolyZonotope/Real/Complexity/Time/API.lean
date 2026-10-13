import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Plus
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Map
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.LinComb
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Bilin
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Mul
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.QuadBilin
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Compact
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Reduce
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.CartProd
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.EDiff
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.EDrift
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxWidth
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxWidthMulti
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxWidthGroup
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxDrift
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpGroup
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxGreedy

/-!
# What running `PolyZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**, never `rfl` against the definition.
`Complexity/Space/` is the other kind of claim: how large a *result* is, proved.

`Complexity/Space/Bilin.lean` proves a pairing's result carries `(h₁+1)(h₂+1)`
generators, and `bilinCost` says every one is computed, so `mul` and `quadMap`
are quadratic in a count that `plus` grows and only `reduce` brings down.
`compactCost` is quadratic for its own reason, a pairwise merge over exponent
columns. `bilinCost` and `mapCost` take one application's price as a parameter.

The relax family is counted at `Vec ℝ n`. `eDiffCost` and `eDriftCost` price
exponent arithmetic, comparisons and parities on `ℕ`, at unit. No relaxation
depends on the generator count `h`: each merges a named pair or group, and what
it copies is free. `relaxExpGreedyCost` takes the selection's price as a
parameter, `sel` being an argument of the operation; `cartProd` only places data.
Each count is monotone in the sizes it takes.
-/

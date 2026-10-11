import CORALean.ContSet.PolyZonotope.Real.Cost.Plus
import CORALean.ContSet.PolyZonotope.Real.Cost.Map
import CORALean.ContSet.PolyZonotope.Real.Cost.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Cost.LinComb
import CORALean.ContSet.PolyZonotope.Real.Cost.Dependent
import CORALean.ContSet.PolyZonotope.Real.Cost.Bilin
import CORALean.ContSet.PolyZonotope.Real.Cost.Mul
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadBilin
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Cost.Compact
import CORALean.ContSet.PolyZonotope.Real.Cost.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Cost.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Cost.Reduce
import CORALean.ContSet.PolyZonotope.Real.Cost.CartProd
import CORALean.ContSet.PolyZonotope.Real.Cost.EDiff
import CORALean.ContSet.PolyZonotope.Real.Cost.EDrift
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxWidth
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxWidthMulti
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxWidthGroup
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxDrift
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpGroup
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxGreedy
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxGreedyBigO

/-!
# What running `PolyZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**, never `rfl` against the definition.
`Complexity/` is the other kind of claim: how large a *result* is, proved.

`Complexity/Bilin.lean` proves a pairing's result carries `(h₁+1)(h₂+1)`
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

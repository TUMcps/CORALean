module

public import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.InverseTrig
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `ProbZonotope.max`, over a floating-point scalar

CORA's `max(probZ, m)` and [1] eq. (3), `1 / ((2π)^{n/2} det(Σ)^{1/2}) · exp(-m²/2)`, rounded up
for every positive definite `Σ` of the covariance interval. `det(Σ)` is bounded below by `gⁿ`,
`g` a Gershgorin bound under every eigenvalue: the smallest diagonal lower end minus the row's
largest off-diagonal magnitudes, rounded down. `2π` is four times `acosDown 0`, under `π / 2`.
The denominator `√((2π g)ⁿ)` is rounded down, `exp(-m²/2)` up (`expUp`), and the quotient up.
`none` when `g`, `2π g` or the denominator is not certified positive: a covariance interval that
reaches a singular matrix has no finite bound. `Theorems.MaxLe` says the real `max` is under it.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max(probZ, m)`, rounded up, at fuel `p` (square roots, `acos`) and `k` (`exp`). -/
def ProbZonotope.max (P : ProbZonotope 𝕋 n) (m : 𝕋) (p k : ℕ) : Option 𝕋 :=
  let r : Fin n → 𝕋 := fun i => sumUp fun j =>                      -- Σ_{j ≠ i} |Σ_ij|, up
    if j = i then zero else maximum (absolute (P.cov.inf i j)) (absolute (P.cov.sup i j))
  let g : 𝕋 := minimumOver fun i => subDown (P.cov.inf i i) (r i)    -- ≤ every eigenvalue
  let h : 𝕋 := acosDown p k zero                                     -- ≤ π / 2
  let twoPi : 𝕋 := addDown (addDown h h) (addDown h h)               -- ≤ 2π
  let q : 𝕋 := mulDown twoPi g                                       -- ≤ 2π g
  let d : 𝕋 := sqrtDown p (powDown q n)                              -- ≤ (2π)^{n/2} det(Σ)^{1/2}
  let e : 𝕋 := expUp k (neg (half (maximum zero (mulDown m m))))     -- ≥ exp(-m²/2)
  if ltStrict zero g && le zero q && ltStrict zero d then some (divUp e d) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

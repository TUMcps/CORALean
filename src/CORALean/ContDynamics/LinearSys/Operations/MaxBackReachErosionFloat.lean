import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominalErr
import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# `Alg. 2` line 12 in floats: how much the erosion has to leave room for

Line 12 maps the hull by `e^{-A t_{k+1}}`. In floats the matrix is known to an interval `Φn` and
the product is rounded, so the mapped set `Φ̄ z`, `Φ̄` the lower matrix of the interval, is within
`d` of the exact `Φ z`, `Φ` the exact matrix, where in each coordinate
`|d| ≤ |Φ̄ - Φ| |z| + (rounding)`, `|Φ̄ - Φ|` at most the interval's width and `|z|` at most `ζ`.
The part of line 12 that is the subtracted `Z̲_U` adds its own `DU`. Both are carried back to the
set being mapped by `e^{A t_{k+1}}`, known to an interval `Ψ`, so the set must keep a distance
`Σ_k |Ψ|_{ik} (D + DU)_k` from the boundary of the exact one: this vector, rounded up. Line 10's
`Ẑ_W(τ_k)` is widened by it before line 11 erodes by it.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distance, per coordinate, the hull has to keep from the exact one's boundary: `Φn` and
`Ψ` bracket `e^{-A t_{k+1}}` and `e^{A t_{k+1}}`, the hull `H` is the set mapped, `ζ` bounds its
points and `DU` is the second summand's own distance after the map. -/
def LinearSys.maxBackReachErosionFloat (Φn Ψ : Interval (Mat 𝕋 n n)) (H : ConZonotope 𝕋 (Vec 𝕋 n))
    (ζ DU : Vec 𝕋 n) : Vec 𝕋 n :=
  let W : Mat 𝕋 n n := fun i k => subUp (Φn.sup i k) (Φn.inf i k)   -- |Φ̄ - Φ|, entrywise
  let ε := ConZonotope.mtimesNominalErr Φn.inf H                    -- rounding of Φ̄ z
  let D : Vec 𝕋 n := fun i => addUp (dotUp (W i) ζ) (ε i)           -- |Φ̄ z - Φ z| plus rounding
  let DD : Vec 𝕋 n := fun i => addUp (D i) (DU i)                   -- with the second summand's
  fun i => dotUp (Ψ.magnitudeMat i) DD                              -- carried back by e^{At}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

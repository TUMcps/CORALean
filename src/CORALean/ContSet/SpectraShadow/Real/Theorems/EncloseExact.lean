import CORALean.ContSet.SpectraShadow.Real.Instances
import CORALean.ContSet.SpectraShadow.Real.Theorems.ConvHullExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.OrExact
import CORALean.ContSet.ContSet.Operations.Enclose

/-!
# `enclose` of a spectrahedral shadow is exactly the convex hull of `S` and `M S ⊕ S₂`

CORA's `enclose(SpS, M, SpSplus)` is `convHull(SpS, M*SpS + SpSplus)` (`@spectraShadow/enclose.m`),
which is the generic `ContSet.enclose` at the instances a shadow has: `mtimes` and `plus` are exact,
and `linComb` is the convex hull `convHull_` (the `LinComb` instance in `Instances.lean`). So the
set is the documented one, `{a x₁ + (1 - a) x₂ | x₁ ∈ SpS, x₂ ∈ M SpS + SpSplus, a ∈ [0, 1]}`,
with equality. There is none of the `M*Splus` slip of `@capsule/enclose.m` and
`@ellipsoid/enclose.m`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.enclose_exact (S : SpectraShadow (Vec ℝ n)) (M : Mat ℝ n n)
    (Splus : SpectraShadow (Vec ℝ n)) :
    ContSet.construct (ContSet.enclose (S := fun n => SpectraShadow (Vec ℝ n)) (𝕋 := ℝ) S M Splus)
      = convexHull ℝ (S.construct ∪ ((M *ᵥ ·) '' S.construct + Splus.construct)) := by
  show (S.convHull_ ((SpectraShadow.mtimes M S).plus Splus)).construct = _
  rw [SpectraShadow.convHull_exact, ← SpectraShadow.plus_exact, ← SpectraShadow.mtimes_exact]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

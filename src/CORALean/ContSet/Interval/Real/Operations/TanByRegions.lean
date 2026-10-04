import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `Interval.tanByRegions`

The tangent of `[lo, hi]` as [1, Eq. 14] evaluates it: both bounds reduced into `[0, π)` modulo
the tangent's period `π`, `[0, π)` cut into `R_t1 = [0, π/2)` and `R_t2 = [π/2, π)`, and cases by
the regions of the reduced bounds and whether they swapped. `none` is `]-∞, ∞[`, `some (a, b)` the
interval `[a, b]`.

The printed cases leave one combination out, `z̲ ∈ R_t2` and `z̅ ∈ R_t1`: the range wraps past a
multiple of `π`, where the tangent is continuous and rising, and its range is
`[tan z̲, tan z̅]`. That branch is supplied here, as CORA's `@interval/tan` header lists it
(`inf >= pi/2` and `sup <= pi/2`).

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.tanByRegions (lo hi : ℝ) : Option (ℝ × ℝ) :=
  let z_lo := lo - Real.pi * ⌊lo / Real.pi⌋  -- `mod(x̲, π)`
  let z_hi := hi - Real.pi * ⌊hi / Real.pi⌋  -- `mod(x̅, π)`
  let R₁ := Set.Ico 0 (Real.pi / 2)  -- `R_t1`
  let R₂ := Set.Ico (Real.pi / 2) Real.pi  -- `R_t2`
  if Real.pi ≤ hi - lo ∨ (z_lo ∈ R₁ ∧ z_hi ∈ R₁ ∧ z_hi < z_lo) ∨
      (z_lo ∈ R₂ ∧ z_hi ∈ R₂ ∧ z_hi < z_lo) ∨ (z_lo ∈ R₁ ∧ z_hi ∈ R₂) then
    none
  else if (z_lo ∈ R₁ ∧ z_hi ∈ R₁ ∧ z_lo ≤ z_hi) ∨ (z_lo ∈ R₂ ∧ z_hi ∈ R₂ ∧ z_lo ≤ z_hi) then
    some (Real.tan z_lo, Real.tan z_hi)
  else
    some (Real.tan z_lo, Real.tan z_hi)  -- `z̲ ∈ R_t2`, `z̅ ∈ R_t1`: not printed, CORA's

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# `Interval.cotByRegions`

The cotangent of `[lo, hi]` as [1, Eq. 15] evaluates it: both bounds reduced into `[0, π)`
modulo the period `π`, and, the cotangent falling on all of `(0, π)`, two cases: `]-∞, ∞[`
(`none`) when the range is at least a period wide or the reduced bounds swapped, otherwise
`[cot z̅, cot z̲]` (`some`). CORA has no `@interval/cot`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.cotByRegions (lo hi : ℝ) : Option (ℝ × ℝ) :=
  let z_lo := lo - Real.pi * ⌊lo / Real.pi⌋  -- `mod(x̲, π)`
  let z_hi := hi - Real.pi * ⌊hi / Real.pi⌋  -- `mod(x̅, π)`
  if Real.pi ≤ hi - lo ∨ z_hi < z_lo then
    none
  else
    some (Real.cot z_hi, Real.cot z_lo)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.cosByRegions`

The cosine of `[lo, hi]` as [1, Eq. 13] evaluates it: both bounds reduced into `[0, 2π)` by
[1, Eq. 11], `[0, 2π)` cut into the two monotone regions `R_c1 = [0, π)`, `R_c2 = [π, 2π)`, and
six cases by the regions of the reduced bounds and whether they swapped (`y̲ > y̅`). The result is
the pair `(inf, sup)`; the cases are the printed ones in the printed order, the last,
`R_c1`, `R_c1`, `y̲ ≤ y̅`, being what is left. CORA's `@interval/cos` computes the same range
another way (`Interval.cos`, through `Interval.maxCos`).

## Inputs
* `lo` – lower end
* `hi` – upper end

## Output
* range of the cosine over `[lo, hi]`, by regions

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.cosByRegions (lo hi : ℝ) : Interval ℝ :=
  let y_lo := lo - 2 * Real.pi * ⌊lo / (2 * Real.pi)⌋  -- (11)
  let y_hi := hi - 2 * Real.pi * ⌊hi / (2 * Real.pi)⌋  -- (11)
  let R₁ := Set.Ico 0 Real.pi  -- `R_c1`
  let R₂ := Set.Ico Real.pi (2 * Real.pi)  -- `R_c2`
  if 2 * Real.pi ≤ hi - lo ∨ (y_lo ∈ R₁ ∧ y_hi ∈ R₁ ∧ y_hi < y_lo) ∨
      (y_lo ∈ R₂ ∧ y_hi ∈ R₂ ∧ y_hi < y_lo) then
    ⟨-1, 1⟩
  else if y_lo ∈ R₂ ∧ y_hi ∈ R₂ ∧ y_lo ≤ y_hi then
    ⟨Real.cos y_lo, Real.cos y_hi⟩
  else if y_lo ∈ R₂ ∧ y_hi ∈ R₁ then
    ⟨min (Real.cos y_lo) (Real.cos y_hi), 1⟩
  else if y_lo ∈ R₁ ∧ y_hi ∈ R₂ then
    ⟨-1, max (Real.cos y_lo) (Real.cos y_hi)⟩
  else
    ⟨Real.cos y_hi, Real.cos y_lo⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.sinByRegions`

The sine of `[lo, hi]` as [1, Eq. 12] evaluates it: both bounds reduced into `[0, 2π)` by
[1, Eq. 11], `[0, 2π)` cut into the three monotone regions `R_s1 = [0, π/2)`,
`R_s2 = [π/2, 3π/2)`, `R_s3 = [3π/2, 2π)`, and twelve cases by the regions of the reduced bounds
and whether they swapped (`y̲ > y̅`, the range wrapping past `2π`). The result is the pair
`(inf, sup)`; the cases are the printed ones in the printed order, the last, `R_s2`, `R_s2`,
`y̲ ≤ y̅`, being what is left. CORA's `@interval/sin` computes `cos(I - π/2)` instead
(`Interval.sin`).

## Inputs
* `lo` – lower end
* `hi` – upper end

## Output
* range of the sine over `[lo, hi]`, by regions

## References

* [1] [M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16.
      3rd International Workshop on Applied Verification for Continuous and Hybrid Systems,
      2017.](../../../../../../references/2017/althoff-arch-interval-arithmetic.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sinByRegions (lo hi : ℝ) : Interval ℝ :=
  let y_lo := lo - 2 * Real.pi * ⌊lo / (2 * Real.pi)⌋  -- (11)
  let y_hi := hi - 2 * Real.pi * ⌊hi / (2 * Real.pi)⌋  -- (11)
  let R₁ := Set.Ico 0 (Real.pi / 2)  -- `R_s1`
  let R₂ := Set.Ico (Real.pi / 2) (3 * Real.pi / 2)  -- `R_s2`
  let R₃ := Set.Ico (3 * Real.pi / 2) (2 * Real.pi)  -- `R_s3`
  if 2 * Real.pi ≤ hi - lo ∨ (y_lo ∈ R₁ ∧ y_hi ∈ R₁ ∧ y_hi < y_lo) ∨ (y_lo ∈ R₁ ∧ y_hi ∈ R₃) ∨
      (y_lo ∈ R₂ ∧ y_hi ∈ R₂ ∧ y_hi < y_lo) ∨ (y_lo ∈ R₃ ∧ y_hi ∈ R₃ ∧ y_hi < y_lo) then
    ⟨-1, 1⟩
  else if (y_lo ∈ R₁ ∧ y_hi ∈ R₁ ∧ y_lo ≤ y_hi) ∨ (y_lo ∈ R₃ ∧ y_hi ∈ R₁) ∨
      (y_lo ∈ R₃ ∧ y_hi ∈ R₃ ∧ y_lo ≤ y_hi) then
    ⟨Real.sin y_lo, Real.sin y_hi⟩
  else if (y_lo ∈ R₁ ∧ y_hi ∈ R₂) ∨ (y_lo ∈ R₃ ∧ y_hi ∈ R₂) then
    ⟨min (Real.sin y_lo) (Real.sin y_hi), 1⟩
  else if (y_lo ∈ R₂ ∧ y_hi ∈ R₁) ∨ (y_lo ∈ R₂ ∧ y_hi ∈ R₃) then
    ⟨-1, max (Real.sin y_lo) (Real.sin y_hi)⟩
  else
    ⟨Real.sin y_hi, Real.sin y_lo⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

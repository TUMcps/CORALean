module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

/-!
# The root of a Gaussian absolute moment

[1, Thm. 15 (accuracy)] writes its approximation constants with
`γ_k = (2^{k/2} / √π · Γ((k + 1)/2))^{1/k}` (Eq. 31), the `k`-th root of the `k`-th absolute
moment `E|g|^k` of a standard normal `g`; `integral_abs_inner_rpow_stdGaussian` proves that
it is that root. This file is the formula as printed, for `k > 0`; `γ₁ = √(2/π)`, `γ₂ = 1`.

## Inputs
* `k` – moment order

## Output
* the root of the Gaussian absolute moment of that order

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `γ_k = (2^{k/2} / √π · Γ((k + 1)/2))^{1/k}`, Eq. 31 of [1, Thm. 15 (accuracy)]. -/
noncomputable def gaussMomentRoot (k : ℝ) : ℝ :=
  (2 ^ (k / 2) / Real.sqrt Real.pi * Real.Gamma ((k + 1) / 2)) ^ (1 / k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

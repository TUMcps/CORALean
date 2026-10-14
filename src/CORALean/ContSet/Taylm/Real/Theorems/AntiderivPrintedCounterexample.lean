module

public import CORALean.ContSet.Taylm.Real.Operations.AntiderivPrinted
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The printed antiderivation fails to enclose

[1, Def. 3 (antiderivation)], eq. (2.7), as printed. In one variable on `[-1, 1]` at order `1`,
`f(x) = 1 + x²` has the Taylor model `P = 1`, `I = [0, 1]`. The printed rule gives `x` with the
remainder `([0, 0] + [0, 1])·2 = [0, 2]`, but `∫₀ˣ f = x + x³/3` is `x - 1/3` at `x = -1`, below
`x + 0`: for negative `x` the integral of a positive remainder is negative.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.antiderivPrinted_counterexample :
    ∃ (T : Taylm 1) (f : Vec ℝ 1 → ℝ), Continuous f ∧ T.Encloses f ∧
      ¬ (T.antiderivPrinted 0).Encloses fun t =>
        ∫ s in (0 : ℝ)..t 0, f (Function.update t 0 s) := by -- --- PROOF ---
  refine ⟨⟨[(1, 0)], 0, 1, 1⟩, fun t => 1 + t 0 ^ 2, by fun_prop, ?_, fun hE => ?_⟩
  · intro t ht
    have := abs_le.1 (ht 0)
    simp [Taylm.poly, Taylm.monomial_zero]
    exact ⟨by positivity, ht 0⟩
  · have := (hE (fun _ => -1) (fun _ => by simp)).1
    simp [Taylm.antiderivPrinted, Taylm.integrateTerms, Taylm.poly, Taylm.polyBounds,
      Taylm.degree, Taylm.monomial] at this
    norm_num [integral_pow] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

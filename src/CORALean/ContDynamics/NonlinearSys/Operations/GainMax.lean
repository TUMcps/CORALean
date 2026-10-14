module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `gainMax`: the gain of a step size, read off two boxes

Eq. (25) of [1]: `φ(Δt) = maxᵢ dᵢ(box(R_abs(ζ_δ Δt))) / dᵢ(box(R_abs(Δt)))`,
the largest share of its width any dimension of the set of abstraction errors
keeps when the step size is scaled down by `ζ_δ`. Line 6 of [1, Alg. 2] is this,
evaluated on the two error sets its line 5 computed.

The two diameter vectors are the caller's, exactly as `tuneAbstrOrder`'s are:
`d(box(R_abs(Δt)))` depends on whichever `Alg. 1` and whichever set
representation a caller runs, and all that happens here is the comparison.

The maximum runs over `List.finRange n` through the caller's `le` rather than
through `⨆`, since [1, Alg. 2] has to compute. `Gain.lean` beside it is the `⨆`
version, `[2, Def. 5]`'s gain over the *untruncated* error set — the quantity
the theory is stated about, and not one a step can evaluate. Folding from `0`
reports `0` in `n = 0` dimensions, where there is no ratio to take, and can
never win against a ratio of two non-negative widths.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ(Δt)` of eq. (25): the worst dimension's ratio of the two error widths,
picked out by the caller's `le`. -/
noncomputable def gainMax (le : ℝ → ℝ → Bool) (d dδ : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (fun φ i => if le φ (dδ i / d i) then dδ i / d i else φ) 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

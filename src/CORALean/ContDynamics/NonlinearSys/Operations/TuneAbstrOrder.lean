module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `tuneAbstrOrder`: the abstraction order for the next step

Line 13 of [1, Alg. 2], which is its §5.2, a two-step criterion. Eq. (46) first
asks whether the error sets of this step and of the last comparison differ
enough to be worth re-tuning at all — levelled by the gain `φ*`, the two steps
having had different step sizes. Only if they do does eq. (47) decide: the
order drops to `1` when every dimension that the linear abstraction gives a
positive width to is already within `ζ_K` of what the quadratic one gives, and
stands at `2` otherwise.

`d1` and `d2` are `d(box(R_abs))` at `κ = 1` and `κ = 2`, supplied: the
abstraction order enters this tree through whatever `abstrErr` a caller runs,
so the two evaluations are the caller's and the comparison is here. The
dimensions with `d_i(R_abs) = 0` are skipped through the caller's own `le`
rather than through a decidable `<` on ℝ, which is what keeps this runnable.

`κ = {1,2}` is [1]'s restriction for a linearization approach, and it is why no
search is needed: the criterion is a choice between two values.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 13: the abstraction order of the next step, from the two
error radii of eq. (46) and the two diameter vectors of eq. (47). -/
noncomputable def tuneAbstrOrder (le : ℝ → ℝ → Bool) (ζK φstar rabs rabsLast : ℝ)
    (d1 d2 : Fin n → ℝ) (κ : ℕ) : ℕ :=
  if le |φstar * rabs / rabsLast| (1 - ζK) then κ                -- 46. too close to re-tune
  else if ∀ i : Fin n, le (d1 i) 0 = true ∨ le ζK (d2 i / d1 i) = true
    then 1                                                       -- 47. quadratic wins too little
    else 2                                                       -- 47. it is worth its cost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

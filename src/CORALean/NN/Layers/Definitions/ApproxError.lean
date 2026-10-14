module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The approximation errors of a linear approximation

[1, Def. 6]: the approximation error of a linear approximation `p` of an activation `ϕ` within
`[l, u]` is the largest lower and upper distance between them, `e_low = min_{x ∈ [l,u]} ϕ(x) -
p(x)` and `e_up = max_{x ∈ [l,u]} ϕ(x) - p(x)`, so that `ϕ([l,u]) ⊆ p(x) ⊕ [e_low, e_up]`. Written
as the infimum and the supremum, which are the minimum and maximum for a continuous `ϕ` and `p`
and `l ≤ u`; `p` is any function here.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `min_{x ∈ [l,u]} ϕ(x) - p(x)`. -/
noncomputable def approxErrorLow (ϕ p : ℝ → ℝ) (l u : ℝ) : ℝ :=
  sInf ((fun x => ϕ x - p x) '' Set.Icc l u)

/-- `max_{x ∈ [l,u]} ϕ(x) - p(x)`. -/
noncomputable def approxErrorUp (ϕ p : ℝ → ℝ) (l u : ℝ) : ℝ :=
  sSup ((fun x => ϕ x - p x) '' Set.Icc l u)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The linear approximation of an activation function

[1, Def. 7]: within `[l, u]`, an activation `ϕ` is approximated by `p(x) = m x` with the slope of
the secant, `m = (ϕ(u) - ϕ(l)) / (u - l)`; the offset `d` does not affect the image enclosure and
is taken zero. It is the slope of DeepPoly's triangle relaxation. At `l = u` the division is by
zero, which is zero in Lean.

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

/-- `(ϕ(u) - ϕ(l)) / (u - l)`. -/
noncomputable def secantSlope (ϕ : ℝ → ℝ) (l u : ℝ) : ℝ := (ϕ u - ϕ l) / (u - l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

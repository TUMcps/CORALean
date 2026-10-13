module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# The derivative along a line through a point

For `F` differentiable at `p`, the derivative of `t ↦ F (p + (t - a) • v)` at `t = a` is `DF v`,
`DF` the derivative of `F` at `p`: the chain rule along a line. It is how the single-entry
derivatives of [1, Def. 3], a function with one entry set to `t`, become the derivative `DF` at a
direction.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A differentiable `F` has the derivative `DF v` along the line `t ↦ p + t v` at `0`. -/
theorem aux_hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (p v : E) (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun t : ℝ => F (p + t • v)) (fderiv ℝ F p v) 0 := by -- --- PROOF ---
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hF' : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt 0 hline


-- =======================================  MAIN THEOREM  ======================================= --

/-- Along the line through `p` in the direction `v`, the value at the parameter `t` is
the derivative at `t₀` shifted. -/
theorem deriv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (p v : E) (hF : DifferentiableAt ℝ F p) (a : ℝ) :
    deriv (fun t : ℝ => F (p + (t - a) • v)) a = fderiv ℝ F p v := by
  have h0 : HasDerivAt (fun t : ℝ => F (p + t • v)) (fderiv ℝ F p v) (a - a) := by
    rw [sub_self]; exact aux_hasDerivAt_line F p v hF
  exact (h0.comp_sub_const a a).deriv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

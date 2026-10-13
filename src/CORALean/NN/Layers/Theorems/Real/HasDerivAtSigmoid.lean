module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# The logistic function's derivative

`σ' t = σ t · σ (-t)`: the reciprocal's derivative, the two negations cancelling and
`e^t` being `(e^{-t})⁻¹`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem hasDerivAt_sigmoid (t : ℝ) : HasDerivAt sigmoid (sigmoidDeriv t) t := by -- --- PROOF ---
  have hEpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
  have hden : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * -1) t :=
    (hasDerivAt_neg t).exp
  have hinv := (hexp.const_add (1:ℝ)).inv (by exact hden)
  -- the two negations cancel and `exp t` is `exp (-t)⁻¹`, which leaves one field identity
  have hkey : -(Real.exp (-t) * -1) / (1 + Real.exp (-t)) ^ 2 = sigmoidDeriv t := by
    have hE : Real.exp (-t) ≠ 0 := ne_of_gt hEpos
    have hEt : Real.exp t = (Real.exp (-t))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [sigmoidDeriv, sigmoid, sigmoid, neg_neg, hEt]
    field_simp
    ring
  rw [← hkey]
  exact hinv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

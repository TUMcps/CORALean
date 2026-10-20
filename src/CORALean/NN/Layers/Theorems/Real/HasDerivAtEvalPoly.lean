module

public import CORALean.NN.Layers.Definitions.EvalPoly
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# A polynomial's derivative

ℝ-only, as `evalPoly` is: termwise, the power rule scaled by the coefficient.

## Inputs
* `n` – polynomial degree
* `c` – coefficients
* `t` – evaluation point

## Hypotheses
* none

## Conclusion
* the polynomial has the derivative given by its coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem hasDerivAt_evalPoly {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : -- --- CONCL ---
    HasDerivAt (evalPoly c) (evalPolyDeriv c t) t := by -- --- PROOF ---
  -- termwise, the power rule scaled by the coefficient
  have hterm : ∀ i : Fin (n + 1), i ∈ Finset.univ →
      HasDerivAt (fun x : ℝ => c i * x ^ (i : ℕ)) (c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))) t :=
    fun i _ => HasDerivAt.const_mul (c i) (hasDerivAt_pow (i : ℕ) t)
  have hsum := HasDerivAt.sum hterm
  -- the sum of the term functions is `evalPoly` itself, read pointwise
  have hfun : (∑ i : Fin (n + 1), fun x : ℝ => c i * x ^ (i : ℕ)) = evalPoly c := by
    funext x
    rw [Finset.sum_apply]
    rfl
  rwa [hfun] at hsum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

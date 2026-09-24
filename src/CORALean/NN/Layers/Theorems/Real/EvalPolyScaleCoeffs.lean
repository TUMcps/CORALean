import CORALean.NN.Layers.Definitions.EvalPoly

/-!
# Rescaled coefficients are a conjugated polynomial

ℝ-only, the rescaling being exact: `(b t) ^ i = b ^ i · t ^ i`, so the conjugation only
reweights the coefficients.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_scaleCoeffs {n : ℕ} (c : Fin (n + 1) → ℝ) (a b t : ℝ) :
    evalPoly (scaleCoeffs c a b) t = a * evalPoly c (b * t) := by -- --- PROOF ---
  show ∑ i : Fin (n + 1), a * c i * b ^ (i : ℕ) * t ^ (i : ℕ)
    = a * ∑ i : Fin (n + 1), c i * (b * t) ^ (i : ℕ)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.NN.Layers.Definitions.SigmoidPoly
import CORALean.NN.Layers.Theorems.Real.PolyOfAffineConjSound
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyRelaxationSound
import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

/-!
# The exact polynomial tanh relaxation is sound

ℝ-only, as the conjugation is: the sigmoid's, transported along the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanhPolyRelaxation_sound {n : ℕ} (c : ℝ → ℝ → Fin (n + 1) → ℝ) (N : ℝ → ℝ → ℕ)
    (hN : ∀ l u, 0 < N l u) : (tanhPolyRelaxation c N).Sound Real.tanh :=
  PolyRelaxation.ofAffineConj_sound (sigmoidPolyRelaxation_sound c N hN) (by norm_num)
    (by norm_num) fun t => by rw [tanh_eq_sigmoid]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

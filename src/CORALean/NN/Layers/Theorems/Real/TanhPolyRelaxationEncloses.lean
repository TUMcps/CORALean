module

public import CORALean.NN.Layers.Definitions.SigmoidPoly
public import CORALean.NN.Layers.Theorems.Real.PolyOfAffineConjEncloses
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

@[expose] public section

/-!
# The exact polynomial tanh relaxation is sound

ℝ-only, as the conjugation is: the sigmoid's, transported along the identity.

## Inputs
* `n` – polynomial degree
* `c` – fit coefficients for each interval
* `N` – sample count for each interval

## Hypotheses
* `hN` – sample counts are positive

## Conclusion
* the polynomial relaxation is sound for tanh
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanhPolyRelaxation_encloses {n : ℕ} (c : ℝ → ℝ → Fin (n + 1) → ℝ) (N : ℝ → ℝ → ℕ)
    (hN : ∀ l u, 0 < N l u) : (tanhPolyRelaxation c N).Encloses Real.tanh :=
  PolyRelaxation.ofAffineConj_encloses (sigmoidPolyRelaxation_encloses c N hN) (by norm_num)
    (by norm_num) fun t => by rw [tanh_eq_sigmoid]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Definitions.EvalPoly

@[expose] public section

/-!
# Moving the constant coefficient moves the polynomial

ℝ-only, the shift being exact: only the constant term is touched, and there `t ^ 0` is one.

## Inputs
* `n` – polynomial degree
* `c` – coefficients
* `s` – shift
* `t` – evaluation point

## Hypotheses
* none

## Conclusion
* moving the constant coefficient shifts the polynomial by the same amount
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_shiftConst {n : ℕ} (c : Fin (n + 1) → ℝ) (s t : ℝ) :
    evalPoly (shiftConst c s) t = evalPoly c t + s := by -- --- PROOF ---
  have hterm : ∀ i : Fin (n + 1), shiftConst c s i * t ^ (i : ℕ)
      = c i * t ^ (i : ℕ) + (if i = 0 then s else 0) := by
    intro i
    by_cases hi : i = 0
    · -- only the constant term is touched, and there `t ^ 0` is one
      rw [hi]
      simp only [shiftConst, Fin.val_zero, pow_zero, mul_one]
    · simp only [shiftConst, if_neg hi, add_zero]
  show ∑ i, shiftConst c s i * t ^ (i : ℕ) = (∑ i, c i * t ^ (i : ℕ)) + s
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1)) fun _ => s,
    if_pos (Finset.mem_univ (0 : Fin (n + 1)))]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

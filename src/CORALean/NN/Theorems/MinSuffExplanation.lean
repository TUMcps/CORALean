import CORALean.NN.Theorems.SuffExplanation

/-!
# Minimal sufficient explanation

[1, Def. 2]: a sufficient explanation minimal under `⊆` — dropping any one of
its features breaks sufficiency.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Sufficient, and no single feature of `E` can be dropped without losing it. -/
def IsMinSuffExplanation (f : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  IsSuffExplanation f x ε E l ∧ ∀ i ∈ E, ¬ IsSuffExplanation f x ε (E \ {i}) l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

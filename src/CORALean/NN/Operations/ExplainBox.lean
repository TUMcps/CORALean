module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The explanation query's input set

The box [1, Def. 1] quantifies over: `E`'s coordinates pinned to `x`, the rest
free within the `ℓ∞` ball of radius `ε`. An `ℓp` ball for `p ≠ ∞` is not a box
and is not covered.

## Inputs
* `n` – number of features
* `x` – input point
* `ε` – perturbation radius
* `E` – explanation, a feature set

## Output
* box pinning the explanation's features and perturbing the rest

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E`'s coordinates pinned to `x`'s values, the rest an `ε`-box around them. -/
def explainBox {n : ℕ} (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) : Real.Interval (Vec ℝ n) where
  inf := fun i => if i ∈ E then x i else x i - ε
  sup := fun i => if i ∈ E then x i else x i + ε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

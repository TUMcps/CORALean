import CORALean.ContSet.Interval.Real.Interval

/-!
# The explanation query's input set

The box `def:suff-explanation` [1] quantifies over: `E`'s coordinates pinned to
`x`, the rest free within the `ℓ∞` ball of radius `ε`. An `ℓp` ball for `p ≠ ∞`
is not a box and is not covered.

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

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E`'s coordinates pinned to `x`'s values, the rest an `ε`-box around them. -/
def explainBox {n : ℕ} (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) : Interval (Vec ℝ n) where
  inf := fun i => if i ∈ E then x i else x i - ε
  sup := fun i => if i ∈ E then x i else x i + ε

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

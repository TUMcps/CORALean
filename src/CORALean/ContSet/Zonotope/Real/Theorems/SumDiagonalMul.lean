import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A diagonal block of generators couples each coordinate to one coefficient

What moves an interval box into generators: off the diagonal every product
vanishes, so a sum over the block collapses to a single term.

Two declarations, not one per file: the primed lemma is the same fact read down
a column instead of along a row, which is the form a diagonal block takes when
generators carry the first index. A Lean module name cannot carry the prime, so
separating them would mean calling one of the two something it is not.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- A diagonal block couples each coordinate to one coefficient and no other. -/
theorem Zonotope.sum_diagonal_mul (v g : Vec ℝ n) (i : Fin n) :
    ∑ i', Matrix.diagonal v i i' * g i' = v i * g i := by
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne' _ hb, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The same read down a column, which is the form a diagonal block takes when
generators carry the first index. -/
theorem Zonotope.sum_diagonal_mul' (v g : Vec ℝ n) (i : Fin n) :
    ∑ l, Matrix.diagonal v l i * g l = v i * g i := by
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ hb, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real

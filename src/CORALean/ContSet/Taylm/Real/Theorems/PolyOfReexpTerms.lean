import CORALean.ContSet.Taylm.Real.Operations.ReexpTerms
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Nat.Choose.Sum

/-!
# Re-expansion is exact

`reexpTerms m r P` at `s` is `P` at `m + r ⊙ s`, term by term: the binomial theorem on each
coordinate, and `Finset.prod_univ_sum` to turn the product of sums into a sum of products.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_reexpTerms (m r : Vec ℝ n) (L : List (ℝ × (Fin n → ℕ))) (s : Vec ℝ n) :
    Taylm.polyOf (Taylm.reexpTerms m r L) s =
      Taylm.polyOf L fun k => m k + r k * s k := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.reexpTerms]
  | cons a L ih =>
    rw [Taylm.reexpTerms, List.flatMap_cons, Taylm.polyOf_append, ← Taylm.reexpTerms, ih,
      Taylm.polyOf_cons]
    congr 1
    simp only [Taylm.polyOf, List.map_map, Function.comp_def, Finset.sum_map_toList,
      Taylm.monomial]
    -- each factor by the binomial theorem, then the product of sums as a sum of products
    have hb : ∀ k, (m k + r k * s k) ^ a.2 k = ∑ j ∈ Finset.range (a.2 k + 1),
        ((a.2 k).choose j : ℝ) * m k ^ (a.2 k - j) * r k ^ j * s k ^ j := by
      intro k
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow]; ring
    simp only [hb, Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Finset.prod_mul_distrib]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

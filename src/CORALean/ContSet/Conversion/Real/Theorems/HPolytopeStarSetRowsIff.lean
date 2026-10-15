module

public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_StarSet
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# The rows of a halfspace description say what the polytope says

A factor vector satisfies every row `HPolytope.starRows` lists exactly when it is in the
polytope: a row is the functional's coefficients, and an equality is two rows.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A linear functional on `Vec ℝ n` is the dot product with its coefficients. -/
theorem HPolytope.aux_apply_eq_sum_coeffRow (f : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) :
    f x = ∑ k, HPolytope.coeffRow f k * x k := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  exact Finset.sum_congr rfl fun k _ => by simp [HPolytope.coeffRow, mul_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.starRows_iff (P : HPolytope (Vec ℝ n)) (α : Vec ℝ n) :
    (∀ r ∈ P.starRows, ∑ k, r.1 k * α k ≤ r.2) ↔ α ∈ P.construct := by -- --- PROOF ---
  simp only [HPolytope.starRows, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_flatMap, List.mem_finRange, forall_true_left, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib, neg_le_neg_iff]
  simp only [← HPolytope.aux_apply_eq_sum_coeffRow]
  constructor
  · rintro ⟨hA, hAe⟩
    exact ⟨hA, fun i => le_antisymm (hAe i).1 (hAe i).2⟩
  · rintro ⟨hA, hAe⟩
    exact ⟨hA, fun i => ⟨(hAe i).le, (hAe i).ge⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

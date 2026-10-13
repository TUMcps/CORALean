module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Minnorm

@[expose] public section

/-!
# `minnormPoint` is at distance `minnorm`

The foot of the perpendicular on the minimising facet is at Euclidean distance `minnorm Z` from
the centre: it is the offset `b` times a unit row.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormPoint_dist (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h)
    (hC : Z.facetNormal S ≠ 0) (hoff : Z.minnormOffset S = Z.minnorm) :
    (Z.minnormPoint S - Z.c) ⬝ᵥ (Z.minnormPoint S - Z.c) = Z.minnorm ^ 2 := by -- --- PROOF ---
  have hCC : 0 < Z.facetNormal S ⬝ᵥ Z.facetNormal S := by
    obtain ⟨k, hk⟩ : ∃ k, Z.facetNormal S k ≠ 0 := by
      by_contra h
      exact hC (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
    refine lt_of_lt_of_le (mul_self_pos.mpr hk) ?_
    exact Finset.single_le_sum (f := fun k => Z.facetNormal S k * Z.facetNormal S k)
      (fun k _ => mul_self_nonneg _) (Finset.mem_univ k)
  have hs : 0 < Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := Real.sqrt_pos.mpr hCC
  have hss : Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) ^ 2
      = Z.facetNormal S ⬝ᵥ Z.facetNormal S := Real.sq_sqrt hCC.le
  unfold Zonotope.minnormPoint
  simp only [add_sub_cancel_left, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hoff]
  field_simp
  rw [hss]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

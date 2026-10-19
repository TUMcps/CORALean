module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeMemHPolytopeFacetsIff
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# A zonotope lies in CORA's facet polytope

Whatever the rows: a point `c + Σ βⱼ Gⱼ` with `|βⱼ| ≤ 1` has `|v ⬝ (x - c)| ≤ Σ |v ⬝ Gⱼ|` for every
`v`, so the facet rows hold, generators spanning or not. Without generators the point is `c`,
which the box rows `[I; -I] x ≤ [c; -c]` pin.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zonotope lies in CORA's `polytope(Z)` rows. -/
theorem Zonotope.hPolytopeFacets_contains (Z : Zonotope (Vec ℝ (m + 1))) :
    Z.construct ⊆ Z.hPolytopeFacets.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, rfl⟩
  by_cases hG : ∀ j, Z.G j = 0
  · -- no generators: the point `c`, both box rows tight
    have hx : Z.c + ∑ j, β j • Z.G j = Z.c := by simp [hG]
    unfold Zonotope.hPolytopeFacets
    rw [if_pos hG, HPolytope.mem_ineqs_iff, hx]
    -- row `k` of `±I` reads `±cₖ`
    have hI : ∀ k : Fin (m + 1), (fun j => (1 : Mat ℝ (m + 1) (m + 1)) k j) ⬝ᵥ Z.c = Z.c k :=
      fun k => by
        rw [show (fun j => (1 : Mat ℝ (m + 1) (m + 1)) k j) = Pi.single k 1 from
          funext fun j => by simp [one_apply, Pi.single_apply, eq_comm], single_dotProduct, one_mul]
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rw [mulVec, Fin.append_left, Fin.append_left, hI]
    · rw [mulVec, Fin.append_right, Fin.append_right]
      show (fun j => -(1 : Mat ℝ (m + 1) (m + 1)) k j) ⬝ᵥ Z.c ≤ -Z.c k
      rw [show (fun j => -(1 : Mat ℝ (m + 1) (m + 1)) k j)
        = -(fun j => (1 : Mat ℝ (m + 1) (m + 1)) k j) from rfl, neg_dotProduct, hI]
  -- the facet rows: each pairs with `Σ βⱼ Gⱼ` to at most `Σ |v ⬝ Gⱼ|`
  rw [Z.mem_hPolytopeFacets_iff hG]
  intro v _
  rw [add_sub_cancel_left, dotProduct_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [dotProduct_smul, smul_eq_mul, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hβ j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

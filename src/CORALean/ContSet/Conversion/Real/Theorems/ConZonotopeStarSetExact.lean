module

public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_StarSet
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeStarSetRowsIff

@[expose] public section

/-!
# A constrained zonotope as a star set

Exact: the factor box `[-1, 1]` is the unit box of the constrained zonotope, and the rows are those
of its constraint polytope, so the same factors give the same points.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.starSet_exact (cZ : ConZonotope (Vec ℝ n)) :
    cZ.starSet.construct = cZ.construct := by -- --- PROOF ---
  ext x
  -- the same factors: a coordinate of `c + Σ β j • G j` is `c i + Σ G j i * β j`
  have hpt : ∀ β : Fin cZ.h → ℝ, (x = cZ.c + ∑ j, β j • cZ.G j) ↔
      ∀ i, x i = cZ.c i + ∑ k, cZ.G k i * β k := fun β => by
    simp only [funext_iff, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun i => by rw [Finset.sum_congr rfl fun k _ => mul_comm (β k) (cZ.G k i)]
  constructor
  · rintro ⟨α, ⟨hα, hrows⟩, hxα⟩
    exact ⟨α, fun j => abs_le.mpr ⟨(hα j).1, (hα j).2⟩,
      (HPolytope.starRows_iff cZ.P α).mp hrows, (hpt α).mpr hxα⟩
  · rintro ⟨β, hβ, hP, hxβ⟩
    exact ⟨β, ⟨fun j => ⟨(abs_le.mp (hβ j)).1, (abs_le.mp (hβ j)).2⟩,
      (HPolytope.starRows_iff cZ.P β).mpr hP⟩, (hpt β).mp hxβ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_StarSet
public import CORALean.ContSet.Interval.Real.Theorems.Basic

@[expose] public section

/-!
# A constrained zonotope as a star set

Exact: the coefficient box `[-1, 1]` is the unit box of the constrained zonotope, and the predicate
is its constraint polytope, so the same factors give the same points.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
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
  · rintro ⟨α, ⟨hα, hP⟩, hxα⟩
    exact ⟨α, (Interval.mem_unit_iff α).mp hα, hP, (hpt α).mpr hxα⟩
  · rintro ⟨β, hβ, hP, hxβ⟩
    exact ⟨β, ⟨(Interval.mem_unit_iff β).mpr hβ, hP⟩, (hpt β).mp hxβ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

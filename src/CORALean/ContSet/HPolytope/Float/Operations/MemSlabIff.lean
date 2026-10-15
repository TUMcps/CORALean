module

public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in `HPolytope.slab`

A point is in the slab iff every row reads between the two bounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_slab_iff {A : Mat 𝕋 q n} {lo hi : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab A lo hi).construct ↔
      ∀ i, toReal (lo i) ≤ (toRealMat A *ᵥ x) i ∧ (toRealMat A *ᵥ x) i ≤ toReal (hi i) := by
  rw [HPolytope.construct_eq_nominal (HPolytope.errFree_of_origin rfl)]
  exact HPolytope.mem_slab_nominal_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

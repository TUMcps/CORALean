module

public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in `HPolytope.eqs`, over a floating-point scalar

Membership at each shape, the block that is absent discharged by `Fin.elim0`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_eqs_iff {Ae : Mat 𝕋 q n} {be : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔ ∀ i, (toRealMat Ae *ᵥ x) i = toReal (be i) :=
  ⟨fun h => ((HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mp h).2,
   fun h => (HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mpr
     ⟨fun i => i.elim0, h⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

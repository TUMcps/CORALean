module

public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in `HPolytope.ineqs`, over a floating-point scalar

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

theorem HPolytope.mem_ineqs_iff {A : Mat 𝕋 q n} {b : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (toRealMat A *ᵥ x) i ≤ toReal (b i) :=
  ⟨fun h => ((HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mp h).1,
   fun h => (HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mpr
     ⟨h, fun i => i.elim0⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

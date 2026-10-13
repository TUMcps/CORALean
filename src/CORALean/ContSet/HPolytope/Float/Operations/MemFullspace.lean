module

public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace

@[expose] public section

/-!
# Every point is in `HPolytope.fullspace`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_fullspace (x : Vec ℝ n) :
    x ∈ (HPolytope.fullspace 𝕋 n).construct :=
  HPolytope.mem_construct_iff.mpr ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

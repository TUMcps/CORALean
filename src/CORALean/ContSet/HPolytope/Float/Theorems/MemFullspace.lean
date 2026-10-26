module

public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Every point is in `HPolytope.fullspace`

Neither block has a row to discharge.

## Inputs
* `x` – point

## Hypotheses
* none

## Conclusion
* the point lies in the constructed full space
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point is in `HPolytope.fullspace` -/
theorem HPolytope.mem_fullspace (x : Vec ℝ n) :
    x ∈ (HPolytope.fullspace 𝕋 n).construct :=
  (HPolytope.mem_construct_iff (HPolytope.isErrFree_of_origin rfl rfl rfl)).mpr
    ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

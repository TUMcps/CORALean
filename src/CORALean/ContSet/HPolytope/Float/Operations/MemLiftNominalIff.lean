module

public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecLiftCols
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal part of `HPolytope.lift_`

A point is in the lifted nominal part iff its selected coordinates are in the original one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_lift_nominal_iff (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) {y : Vec ℝ N} :
    y ∈ (P.lift_ dims).nominal.construct ↔ (fun k => y (dims k)) ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.lift_, HPolytope.mulVec_liftCols hdims]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

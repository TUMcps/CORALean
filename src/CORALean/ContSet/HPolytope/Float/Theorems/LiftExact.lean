import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Float.Operations.Lift
import CORALean.ContSet.HPolytope.Float.Operations.MulVecLiftCols

/-!
# `HPolytope.lift_` is exact

The lifted polytope is the set of points whose selected coordinates lie in the original, as the
exact layer's `lift_exact` states it: nothing rounds, and the stored right-hand sides are unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.lift_exact (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) :
    (P.lift_ dims).construct =
      {x : Vec ℝ N | (fun k => x (dims k)) ∈ P.construct} := by
  ext x
  show x ∈ (P.lift_ dims).construct ↔ (fun k => x (dims k)) ∈ P.construct
  rw [HPolytope.mem_construct_iff, HPolytope.mem_construct_iff]
  simp only [HPolytope.lift_, HPolytope.mulVec_liftCols hdims]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

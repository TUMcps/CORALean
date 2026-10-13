import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeFloat
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float input Jacobian encloses it at every parameter

For a float model enclosing the field and its Jacobians, the input Jacobian at the real value of
the float expansion point and at every parameter of the box lies in the enclosure `linearizeFloat`
returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.FloatModel.linearizeFloat_jacobianU_mem
    {sys : NonlinParamSys n m q} {fm : NonlinParamSys.FloatModel 𝕋 n m q}
    (h : fm.Encloses sys) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q))
    {p : Vec ℝ q} (hp : p ∈ construct P) :
    jacobianMat (fun u => sys.f (toRealVec xs) u p) (toRealVec us) ∈
      construct (fm.linearizeFloat xs us P).B :=
  h.jacU_mem _ _ _ _ (Interval.mem_point xs) _ (Interval.mem_point us) p hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

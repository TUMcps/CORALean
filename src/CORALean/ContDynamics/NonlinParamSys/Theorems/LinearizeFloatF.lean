import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeFloat
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float constant term encloses the dynamics at every parameter

For a float model enclosing the field and its Jacobians, the dynamics at the real value of the
float expansion point and at every parameter of the box lies in the enclosure `linearizeFloat`
returns.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.FloatModel.linearizeFloat_f_mem
    {sys : NonlinParamSys n m q} {fm : NonlinParamSys.FloatModel 𝕋 n m q}
    (h : fm.Encloses sys) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q))
    {p : Vec ℝ q} (hp : p ∈ construct P) :
    sys.f (toRealVec xs) (toRealVec us) p ∈
      construct (fm.linearizeFloat xs us P).f :=
  h.f_mem _ _ _ _ (Interval.mem_point xs) _ (Interval.mem_point us) p hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.NN.Operations.Enclose

/-!
# An interval-valued `simulate` of the closed loop

The float counterpart of `simulate`: the closed-loop step applied to boxes, from a
float start stored as a point interval. The plant acts by `A B ⊕ _` and the
controller supplies the input box by `enclose`, in float interval arithmetic; the
real run lies in the boxes by `simulate_mem_simulateBox` (ruling R-SIM). The
enclosure is outer: `enclose` of a box is not a point even from a point.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The boxes `B_k` of the closed loop from `x₀`: `B_{k+1} = A B_k ⊕ enclose(B_k)`. -/
def NeurNetContrSysDT.simulateBox (sys : NeurNetContrSysDT 𝕋 (fun n => Interval (Vec 𝕋 n)) n)
    (x₀ : Vec 𝕋 n) : ℕ → Interval (Vec 𝕋 n)
  | 0 => Interval.point x₀
  | k + 1 =>
    plus (S := Interval (Vec 𝕋 n)) (mtimes (S := fun n => Interval (Vec 𝕋 n)) sys.plant.A
      (sys.simulateBox x₀ k)) (sys.contr.enclose (sys.simulateBox x₀ k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

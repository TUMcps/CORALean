module

public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# An interval-valued `simulate` of the closed loop

The float counterpart of `simulate`: the closed-loop step applied to boxes, from a
float start stored as a point interval. The plant acts by `A B ⊕ _` and the
controller supplies the input box by `enclose`, in float interval arithmetic; the
real run lies in the boxes by `simulate_mem_simulateBox` (ruling R-SIM). The
enclosure is outer: `enclose` of a box is not a point even from a point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The boxes `B_k` of the closed loop from `x₀`: `B_{k+1} = A B_k ⊕ (B enclose(B_k) ⊕ c)`. -/
def NeurNetContrSysDT.simulateBox (sys : NeurNetContrSysDT 𝕋 ℐ𝒱[𝕋] n)
    (x₀ : Vec 𝕋 n) : ℕ → Interval (Vec 𝕋 n)
  | 0 => Interval.point x₀
  | k + 1 =>
    plus (S := Interval (Vec 𝕋 n)) (mtimes (S := ℐ𝒱[𝕋]) sys.plant.A (sys.simulateBox x₀ k))
      (plus (S := Interval (Vec 𝕋 n)) (mtimes (S := ℐ𝒱[𝕋]) sys.plant.B
        (sys.contr.enclose (sys.simulateBox x₀ k))) (OfScalarPoint.ofVec (S := ℐ𝒱[𝕋]) sys.plant.c))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

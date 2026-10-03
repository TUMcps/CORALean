import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.LinearSysDT.Theorems.MemSimulateBoxIn
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The real run lies in the float boxes

`simulate` of the real values of a float start and a float input signal lies, at
every step, in the box `simulateBox` computed in float arithmetic: the float
`simulate` row's guarantee (ruling R-SIM). An enclosure, so the box is outer.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.simulate_mem_simulateBox (sys : LinearSysDT 𝕋 n) (x₀ : Vec 𝕋 n)
    (u : ℕ → Vec 𝕋 n) (k : ℕ) :
    sys.simulate (Scalar.toRealVec x₀) (fun j => Scalar.toRealVec (u j)) k ∈
      construct (sys.simulateBox x₀ u k) :=
  sys.mem_simulateBoxIn _ _
    (x := sys.simulate (Scalar.toRealVec x₀) fun j => Scalar.toRealVec (u j))
    (u := fun j => Scalar.toRealVec (u j)) (Interval.mem_point x₀)
    (fun j => Interval.mem_point (u j)) (fun _ => rfl) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

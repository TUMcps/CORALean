module

public import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContDynamics.LinearSysDT.Theorems.MemSimulateBoxIn
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The real run lies in the float boxes

`simulate` of the real values of a float start and a float input signal lies, at
every step, in the box `simulateBox` computed in float arithmetic: the float
`simulate` row's guarantee (ruling R-SIM). An enclosure, so the box is outer.

## Inputs
* `sys` – system
* `x₀` – float start state
* `u` – float inputs
* `k` – step

## Hypotheses
* none

## Conclusion
* the real run lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.SimulateBoxFloat
public import CORALean.NN.Theorems.EncloseOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The real closed-loop run lies in the float boxes

For a controller function `π` the network is `Sound` for, `simulate` from the real
value of a float start lies at every step in the box `simulateBox` computed in
float arithmetic: the float `simulate` row's guarantee (ruling R-SIM). An
enclosure, so the box is outer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes ContSet CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_mem_simulateBox
    (sys : NeurNetContrSysDT 𝕋 ℐ𝒱[𝕋] n) {π : Vec ℝ n → Vec ℝ n}
    (hπ : sys.contr.Sound π) (x₀ : Vec 𝕋 n) (k : ℕ) :
    sys.simulate π (Scalar.toRealVec x₀) k ∈ construct (sys.simulateBox x₀ k) := by -- --- PROOF ---
  induction k with
  | zero => exact Interval.mem_point x₀
  | succ k ih =>
    exact plus_outer (S := Interval (Vec 𝕋 n)) _ _
      (Set.add_mem_add (mtimes_outer (S := ℐ𝒱[𝕋]) sys.plant.A _
        (Set.mem_biUnion rfl (Set.mem_image_of_mem _ ih))) (hπ.enclose_outer _ _ ih))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

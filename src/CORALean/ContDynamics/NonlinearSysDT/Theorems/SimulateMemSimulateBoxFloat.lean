import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate
import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat

/-!
# The real run lies in the float boxes

For a `FloatModel` that encloses the system, the real `simulate` from the real value of a float
start under the real value of a float input signal lies, at every step, in the box
`simulateBoxFloat` computes. An outer statement; the boxes are not the run.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.simulate_mem_simulateBoxFloat (sys : NonlinearSysDT n m)
    {fm : NonlinearSysDT.FloatModel 𝕋 n m} (h : fm.Encloses sys) (x₀ : Vec 𝕋 n)
    (u : ℕ → Vec 𝕋 m) (k : ℕ) :
    sys.simulate (Scalar.toRealVec x₀) (fun j => Scalar.toRealVec (u j)) k ∈
      construct (NonlinearSysDT.simulateBoxFloat fm x₀ u k) := by
  induction k with
  | zero => exact Interval.mem_point x₀
  | succ k ih =>
    exact h.f_mem _ _ _ ih _ (Interval.mem_point (u k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

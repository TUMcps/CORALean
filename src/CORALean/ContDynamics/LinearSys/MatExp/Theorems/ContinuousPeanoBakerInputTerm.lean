import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerInputTerm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Every Peano–Baker term of an input is continuous in time

Each is a primitive of a function integrable over every window — the input itself
at order `0`, then `A(σ)` against the continuous term one order down — and a
primitive of a locally integrable function is continuous.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.continuous_peanoBakerInputTerm {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) {u : ℝ → Vec ℝ n}
    (hu : ∀ a b, IntervalIntegrable u volume a b) (k : ℕ) :
    Continuous (MatExp.peanoBakerInputTerm A u k) := by -- --- PROOF ---
  induction k with
  | zero => exact intervalIntegral.continuous_primitive hu 0
  | succ k ih =>
    -- `A` against a continuous term is integrable over every window
    exact intervalIntegral.continuous_primitive
      (fun a b => MatExp.intervalIntegrable_mulVec hA ih.continuousOn) 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

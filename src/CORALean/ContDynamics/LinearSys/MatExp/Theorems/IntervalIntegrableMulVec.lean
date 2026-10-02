import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# A time-varying matrix applied to a continuous vector is integrable

`σ ↦ A(σ) w(σ)` over a window, given only that each entry of `A` is integrable
there and `w` is continuous on it: each coordinate is a finite sum of an
integrable function against a continuous one, and a map into `Vec` is integrable
when each coordinate is. Nothing is asked of `A` as a matrix-valued map, which
under the `l∞` operator norm Mathlib's integral could not be stated for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector-valued map is integrable if each coordinate is. -/
theorem aux_intervalIntegrable_of_coord {f : ℝ → Vec ℝ n} {a b : ℝ}
    (hf : ∀ i, IntervalIntegrable (fun s => f s i) volume a b) :
    IntervalIntegrable f volume a b :=
  ⟨Integrable.of_eval fun i => (hf i).1, Integrable.of_eval fun i => (hf i).2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.intervalIntegrable_mulVec {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) {w : ℝ → Vec ℝ n}
    {a b : ℝ} (hw : ContinuousOn w (Set.uIcc a b)) :
    IntervalIntegrable (fun s => A s *ᵥ w s) volume a b := by -- --- PROOF ---
  refine aux_intervalIntegrable_of_coord fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  -- one integrable entry against one continuous coordinate, summed
  have h := IntervalIntegrable.sum Finset.univ fun l _ =>
    (hA i l a b).mul_continuousOn ((continuous_apply l).comp_continuousOn hw)
  rwa [Finset.sum_fn] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.LinearSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContSet.ContSet.Theorems.Basic
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
import CORALean.Specification.Theorems.Basic

/-!
# A sampled run falsifies a specification the enclosure cannot refute

An enclosure is a superset, so a specification holding on it proves safety and one violated on it
proves nothing: the violation may sit entirely in the approximation error. A sampled run is exact,
one point genuinely reached, so a specification it violates is genuinely violated.
`not_holds_of_simulate` turns that violation into a verdict on whatever `reach` computes, at any
order. The system is a discrete double integrator, `x(k+1) = [[1, 1], [0, 1]] x(k)`, started at
`(0, 1)` with no input: `x(k) = (k, 1)`. The specification keeps the position at most `3`, so it
holds for three steps and the run leaves the safe set only at step `4`.

## Inputs
* none

## Output
* discrete double integrator
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The double integrator: position `+=` speed, speed constant. -/
def SAF.sys : LinearSysDT ℝ 2 := LinearSysDT.canonical !![1, 1; 0, 1]

/-- Position `0`, speed `1`. -/
def SAF.x0 : Vec ℝ 2 := ![0, 1]

def SAF.R0 : Interval (Vec ℝ 2) := Interval.point SAF.x0
def SAF.U : Interval (Vec ℝ 2) := Interval.point (0 : Vec ℝ 2)

/-- Safe: the position at most `3`. `x0` satisfies it. -/
def SAF.spec : Specification (Set (Vec ℝ 2)) := Specification.safeSet {x | x 0 ≤ 3}

/-- After `k` steps the run is at position `k`, speed `1`. -/
theorem SAF.sim_eq (k : ℕ) :
    SAF.sys.simulate SAF.x0 (fun _ => (0 : Vec ℝ 2)) k = ![(k : ℝ), 1] := by -- --- PROOF ---
  induction k with
  | zero => ext i; fin_cases i <;> simp [LinearSysDT.simulate, SAF.x0]
  | succ k ih =>
    simp only [LinearSysDT.simulate]
    rw [ih]
    ext i
    fin_cases i <;> simp [SAF.sys]

/-- Three steps in, the run is still at position `3`, inside the safe set: this
sample refutes nothing. -/
example : SAF.sys.simulate SAF.x0 (fun _ => (0 : Vec ℝ 2)) 3 ∈ {x : Vec ℝ 2 | x 0 ≤ 3} := by
  simp [SAF.sim_eq]

/-- Four steps in, the run is at position `4`, so it refutes `spec` over whatever
`reach` computes at step `4`, at any order — the half a sample is trusted for. -/
example {o : ℕ} (ho : 0 < o) :
    ¬ SAF.spec.Holds (construct (SAF.sys.reach (S := ℐ𝒱) ⟨SAF.R0, SAF.U, 0, 4⟩ ⟨o, ho⟩)) :=
  SAF.sys.not_holds_of_simulate (S := ℐ𝒱) ho SAF.R0 SAF.U SAF.spec
    (Interval.mem_point SAF.x0) (fun _ => Interval.mem_point 0) 4
    (by
      rw [SAF.sim_eq]
      simp [SAF.spec]
      norm_num)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

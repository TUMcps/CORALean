import CORALean.ContDynamics.LinearSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateMemReach
import CORALean.ContSet.Interval.Real.Instances

/-!
# Reachability and simulation answer opposite halves of the same question

An enclosure is a superset, so a specification holding on it proves safety and
one violated on it proves nothing — the violation may sit entirely in the
approximation error. A sampled run is exact: one point genuinely reached, so a
specification it violates is genuinely violated. `simulate_mem_reach` is the
first half, `not_holds_of_simulate` the second, at the same run.

The system here does nothing — `A = 1`, no input — so `simulate` just repeats
the initial point, and that point already sits outside the safe set: the
falsification needs no steps to find.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The identity: the state never moves on its own. -/
def SAF.sys : LinearSysDT ℝ 2 := ⟨1⟩

/-- `2` on the first coordinate, already outside `spec` below. -/
def SAF.x0 : Vec ℝ 2 := ![2, 0]

def SAF.R0 : Interval (Vec ℝ 2) := Interval.point SAF.x0
def SAF.U : Interval (Vec ℝ 2) := Interval.point (0 : Vec ℝ 2)

/-- Safe: the first coordinate at most `1`. `x0` already fails it. -/
def SAF.spec : Specification (Set (Vec ℝ 2)) := Specification.safeSet {x | x 0 ≤ 1}

/-- Held at `x0`, at every step: the identity system moved by a zero input. -/
theorem SAF.sim_const (k : ℕ) :
    SAF.sys.simulate SAF.x0 (fun _ => (0 : Vec ℝ 2)) k = SAF.x0 := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [LinearSysDT.simulate]
    rw [ih]
    simp [SAF.sys, Matrix.one_mulVec]

/-- `simulate`'s run sits inside `reach`'s enclosure at any order and any
horizon — the half an enclosure is trusted for. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    SAF.sys.simulate SAF.x0 (fun _ => (0 : Vec ℝ 2)) k
      ∈ construct (SAF.sys.reach (S := ℐ𝒱) ⟨SAF.R0, SAF.U, 0, k⟩ ⟨o, ho⟩) :=
  SAF.sys.simulate_mem_reach (S := ℐ𝒱) ho SAF.R0 SAF.U
    (Interval.mem_point SAF.x0) (fun _ => Interval.mem_point 0) k

/-- The sampled run violates `spec` outright, so it refutes `spec` over
whatever `reach` computes — the half a sample is trusted for, and an enclosure
never could be, since the violation might be nothing but its own slack. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    ¬ SAF.spec.Holds (construct (SAF.sys.reach (S := ℐ𝒱) ⟨SAF.R0, SAF.U, 0, k⟩ ⟨o, ho⟩)) :=
  SAF.sys.not_holds_of_simulate (S := ℐ𝒱) ho SAF.R0 SAF.U SAF.spec
    (Interval.mem_point SAF.x0) (fun _ => Interval.mem_point 0) k
    (by rw [SAF.sim_const]; simp [SAF.spec, SAF.x0])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

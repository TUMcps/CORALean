import CORALean.ContDynamics.LinearSys.Operations.Canonical
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReach
import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachTimeIntervalInner
import CORALean.ContDynamics.LinearSys.Theorems.MinkowskiDiffSubsetMaxBackReachCZ
import CORALean.Global.SupportFunction.OfIsBounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The support oracle of `Alg. 3` exists

`LinearSys.maxBackReach` and its steps ask their oracle `ρ` about bounded polytopes only, and the
supremum `SupportBound.ofIsBounded` answers every such question, so the theorems that take `ρ` are
about an oracle that exists. The examples run the algorithm on the interval `[-1, 1]` as a
halfspace description, whose rows bound it, and spend `minkowskiDiff_subset_maxBackReachCZ` on it.

## Inputs
* none

## Output
* the oracle, a bounded target set, and the algorithm and a theorem at them
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[-1, 1]` on the line, as the rows `x ≤ 1` and `-x ≤ 1`. -/
def MBR.box : HPolytope (Vec ℝ 1) :=
  ⟨2, ![LinearMap.proj 0, -LinearMap.proj 0], ![1, 1], 0, ![], ![]⟩

/-- The disturbance set `[-1/2, 1/2]` on the line. -/
def MBR.ZW : Zonotope (Vec ℝ 1) := ⟨1, ![0], fun _ => ![(0.5 : ℝ)]⟩

/-- The rows of `MBR.box` alone bound it: they keep every point in `[-1, 1]`. -/
theorem MBR.box_bounded : -- --- CONCL ---
    Bornology.IsBounded MBR.box.dropEqs.construct := by -- --- PROOF ---
  refine (Metric.isBounded_Icc (fun _ => (-1 : ℝ)) (fun _ => 1)).subset fun x hx => ?_
  -- the two rows, read at their indices
  have h₁ : x 0 ≤ 1 := hx.1 (0 : Fin 2)
  have h₂ : -x 0 ≤ 1 := hx.1 (1 : Fin 2)
  exact ⟨fun i => by fin_cases i; show -1 ≤ x 0; linarith, fun i => by fin_cases i; exact h₁⟩

-- the oracle `Alg. 3` asks for: every bounded polytope, every direction
noncomputable example : ∀ (P : HPolytope (Vec ℝ 1)) (_ : Bornology.IsBounded P.construct)
    (c : Vec ℝ 1 →ₗ[ℝ] ℝ), SupportBound P.construct c :=
  fun _ hP c => SupportBound.ofIsBounded hP c

-- `Alg. 3` on `ẋ = 0` with target `[-1, 1]`, two steps over `[0, 1]`
noncomputable example : Set (Vec ℝ 1) :=
  (LinearSys.canonical !![(0 : ℝ)]).maxBackReach (fun _ hP c => SupportBound.ofIsBounded hP c)
    MBR.box MBR.box_bounded MBR.ZW MBR.ZW (fun _ => MBR.ZW) 0 1 2 2

-- line 11's conversion holds the difference, at the oracle above
example : minkowskiDiff MBR.box.construct MBR.ZW.construct ⊆
    (LinearSys.maxBackReachCZ (fun _ hP c => SupportBound.ofIsBounded hP c) MBR.box
      MBR.box_bounded MBR.ZW).construct :=
  LinearSys.minkowskiDiff_subset_maxBackReachCZ _ _ _ MBR.box_bounded fun i => i.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

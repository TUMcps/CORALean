module

public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# The unit ball of `S_P` is not `P` when the origin is outside

`P = [1, 2] = {x ≤ 2, -x ≤ -1}` is a bounded polytope with every `hᵢ ≠ 0`, as `[1, Def. 3]`
asks. `S_P(0) = 0 ≤ 1`, but `0 ∉ P`: the unit-ball claim of `[1, Lemma 1]` needs the
origin inside `P`.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.polyNorm_isAsymmNorm_counterexample : -- --- CONCL ---
    ∃ (H : Mat ℝ 2 1) (h : Vec ℝ 2), (∀ i, h i ≠ 0) ∧
      (HPolytope.ineqs H h).construct.Nonempty ∧
      Bornology.IsBounded (HPolytope.ineqs H h).construct ∧
      ¬ ∀ x, HPolytope.polyNorm H h x ≤ 1 ↔
        x ∈ (HPolytope.ineqs H h).construct := by -- --- PROOF ---
  refine ⟨!![1; -1], ![2, -1], fun i => by fin_cases i <;> norm_num, ⟨![1], ?_⟩, ?_, fun h => ?_⟩
  · refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
    fin_cases i <;> norm_num [mulVec, dotProduct]
  -- `P ⊆ [-2, 2]`
  · refine (Metric.isBounded_closedBall (x := (0 : Vec ℝ 1)) (r := 2)).subset fun x hx => ?_
    have h0 := HPolytope.mem_ineqs_iff.mp hx 0
    have h1 := HPolytope.mem_ineqs_iff.mp hx 1
    simp [mulVec, dotProduct] at h0 h1
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i; fin_cases i
    simp [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  -- `0` is in the unit ball and not in `P`
  · have h0 := (h 0).mp (HPolytope.polyNorm_le_iff.mpr ⟨zero_le_one, fun i => by simp⟩)
    have := HPolytope.mem_ineqs_iff.mp h0 1
    norm_num [mulVec, dotProduct] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

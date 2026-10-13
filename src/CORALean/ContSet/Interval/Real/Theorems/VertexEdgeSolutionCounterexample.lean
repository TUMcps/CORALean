module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A solution on an edge the vertex lowers

[1, Cor. 6.3 (1)] says a vertex `v` has a solution at its edges only if `Σⱼ vⱼ < α`. On `[0, 1]`
with `α = 1/2`, the vertex `v = 1` has `Σⱼ vⱼ = 1 > α`, yet its one edge, from `1` down to `0`,
holds the solution `1/2`. The "only if" holds for the edges `v` raises, the low border vertices
of [1, Def. 4], which `Interval.vertex_edge_solution_iff` states.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vertex_edge_solution_counterexample :
    let b : Vec ℝ 1 := fun _ => 1
    let v := (⟨0, b⟩ : Interval (Vec ℝ 1)).corner fun _ => true
    Function.update v 0 (1 / 2) ∈
        (⟨0, b⟩ : Interval (Vec ℝ 1)).construct ∩ Interval.hyperplane 1 (1 / 2) ∧
      ¬ ∑ k, v k < 1 / 2 := by -- --- PROOF ---
  intro b v
  have hv : v = fun _ => 1 := by funext i; simp [v, b, Interval.corner]
  have hu : Function.update v 0 (1 / 2 : ℝ) = fun _ => 1 / 2 := by
    funext i; fin_cases i; simp
  rw [hu, hv]
  refine ⟨⟨fun i => ?_, ?_⟩, by norm_num⟩
  · show (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1
    norm_num
  · simp [Interval.hyperplane]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

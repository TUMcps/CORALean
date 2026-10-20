module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A piece of the partition whose own face misses the plane

[1, Lemma 6.5] says each element of `P(s, s')` has at least one solution. On `[0, 1]²` with
`Σᵢ xᵢ = 3/2`, line 6 of [1, Alg. 2] gives `k = 1` at the root, `(1, 0)` below the plane and
`(1, 1)` above it, and `P(s, s')` has the piece `(0, *)`. Its face `{0} × [0, 1]` never reaches
the plane, its sums being at most `1`; the solution `(1/2, 1)` lies on an edge leaving it, the
reading `Interval.piece_has_border_vertex` proves.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a piece whose own face misses the plane though the corner sums straddle it

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

theorem Interval.piece_solution_counterexample : -- --- CONCL ---
    let b : Vec ℝ 2 := fun _ => 1
    ∑ x, (⟨0, b⟩ : Interval (Vec ℝ 2)).corner (fun i => decide ((i : ℕ) < 1)) x ≤ 3 / 2 ∧
      3 / 2 < ∑ x, (⟨0, b⟩ : Interval (Vec ℝ 2)).corner (fun i => decide ((i : ℕ) < 2)) x ∧
      (⟨0, ![0, 1]⟩ : Interval (Vec ℝ 2)).construct ∩
        Interval.hyperplane 1 (3 / 2) = ∅ := by -- --- PROOF ---
  intro b
  refine ⟨?_, ?_, ?_⟩
  · simp [Interval.corner, b]; norm_num
  · simp [Interval.corner, b]; norm_num
  · -- on `{0} × [0, 1]` the sum is at most `1`
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hP
    have h0 : (0 : ℝ) ≤ x 0 ∧ x 0 ≤ 0 := hx 0
    have h1 : (0 : ℝ) ≤ x 1 ∧ x 1 ≤ 1 := hx 1
    have hs : x 0 + x 1 = 3 / 2 := by simpa [Interval.hyperplane, Fin.sum_univ_two] using hP
    linarith [h0.2, h1.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Real.Operations.ExploreBN
public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `EXPLORE BN` misses a vertex of an unordered box

[1, Sec. 6.3 (general problem)] says that scaling and translation reduce any box and hyperplane
to the case [1, Alg. 2] solves, but Alg. 2 also needs the box ordered, `b₁ ≤ … ≤ bₙ`, which
neither mapping gives. On `[0, 2] × [0, 1]`, `Σᵢ xᵢ = 3/2`, line 6 stops at `k = 0` since
`b₁ = 2 > 3/2`, no piece of a partition is pushed, and `FIND SOLUTIONS(0)` returns `(3/2, 0)`
alone: the vertex `(1/2, 1)` of the cut is missed. `Interval.exploreBN_sort` sorts first.

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

open Classical in
theorem Interval.exploreBN_unordered_counterexample :
    let b : Vec ℝ 2 := ![2, 1]
    let x : Vec ℝ 2 := ![1 / 2, 1]
    x ∈ Set.extremePoints ℝ ((⟨0, b⟩ : Interval (Vec ℝ 2)).construct ∩
        Interval.hyperplane 1 (3 / 2)) ∧ x ∉ Interval.exploreBN b (3 / 2) := by -- --- PROOF ---
  intro b x
  constructor
  · rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
    refine ⟨⟨fun i => ?_, ?_⟩, fun i j hij => ?_⟩
    · show (0 : ℝ) ≤ x i ∧ x i ≤ b i
      fin_cases i <;> norm_num [x, b]
    · simp [Interval.hyperplane, x, Fin.sum_univ_two]; norm_num
    · fin_cases i <;> fin_cases j <;> simp_all [b, x]
  · -- line 6 stops at `k = 0`, the vertices `(2, 0)` and `(2, 1)` being above the plane
    have hv : Interval.exploreBNVisits b (3 / 2) 0 (fun _ => false) = [fun _ => false] := by
      rw [Interval.exploreBNVisits]
      have hk : Nat.findGreatest (fun k =>
          (⟨0, b⟩ : Interval (Vec ℝ 2)).corner (fun i => decide ((i : ℕ) < k)) 0 +
          (⟨0, b⟩ : Interval (Vec ℝ 2)).corner (fun i => decide ((i : ℕ) < k)) 1 ≤ 3 / 2) 2 =
            0 := by
        rw [Nat.findGreatest_eq_zero_iff]
        intro k hk0 hk2
        interval_cases k <;> simp [Interval.corner, b] <;> norm_num
      simp [hk]
    unfold Interval.exploreBN
    rw [hv]
    simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
    -- `FIND SOLUTIONS(0)` raises one coordinate to `3/2`; `x` has none
    unfold Interval.findSolutions
    simp only
    rw [if_neg (by simp [Interval.corner]), Finset.mem_image]
    rintro ⟨i, _, hi⟩
    have := congrFun hi i
    fin_cases i <;> simp [x, Interval.corner] at this <;> norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

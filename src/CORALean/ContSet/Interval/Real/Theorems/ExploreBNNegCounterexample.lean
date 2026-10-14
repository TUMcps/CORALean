module

public import CORALean.ContSet.Interval.Real.Operations.ExploreBN
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# Below the box, `EXPLORE BN` returns a point outside it

[1, Alg. 2], line 6, computes the maximum `k` with `Σ_{i≤j} vᵢ + Σ_{i=j+1}^k bᵢ ≤ α`, which does
not exist at the root when `α < 0`; the proof of [1, Lemma 6.4] notes that a solution needs
`0 ≤ α`, the algorithm does not check it. Taking `k = j` then, `FIND SOLUTIONS(0)` with
`α' = α < 0` returns `0` with a coordinate lowered to `α`: for `n = 1`, `b = 1`, `α = -1` the
point `-1`, outside the box, although the cut is empty. `exploreBN_eq_extremePoints` assumes
`0 ≤ α`.

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
theorem Interval.exploreBN_neg_counterexample :
    let b : Vec ℝ 1 := fun _ => 1
    (fun _ => (-1 : ℝ)) ∈ Interval.exploreBN b (-1) ∧
      (fun _ => (-1 : ℝ)) ∉ (⟨0, b⟩ : Interval (Vec ℝ 1)).construct := by -- --- PROOF ---
  intro b
  constructor
  · unfold Interval.exploreBN
    rw [Interval.exploreBNVisits]
    -- line 6 finds no `k` with the vertex below the plane, so `k = 0` and `w = 0`
    have hk : Nat.findGreatest (fun k => ∑ i, (⟨0, b⟩ : Interval (Vec ℝ 1)).corner
        (fun i : Fin 1 => if (i : ℕ) < 0 then (fun _ => false) i else decide ((i : ℕ) < k)) i
          ≤ -1) 1 = 0 := by
      rw [Nat.findGreatest_eq_zero_iff]
      intro k hk0 hk1
      have : k = 1 := by omega
      subst this
      simp [Interval.corner, b]
    simp only [hk]
    simp only [List.foldr_cons, Finset.mem_union]
    left
    -- `FIND SOLUTIONS(0)`: `α' = -1`, raised (lowered) in the only coordinate
    unfold Interval.findSolutions
    simp [Interval.corner]
    refine ⟨by norm_num [b], ?_⟩
    funext i
    fin_cases i
    simp
  · intro h
    have h0 : (0 : ℝ) ≤ -1 := (h 0).1
    norm_num at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

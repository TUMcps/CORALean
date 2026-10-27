module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxCluster
public import CORALean.ContSet.Zonotope.Real.Theorems.MulGensInner
public import CORALean.ContSet.Zonotope.Real.Theorems.SumAbsLeOneOfSubsingletonSupport

@[expose] public section

/-!
# `reduceUnderApproxCluster` returns a subset

Whatever the partition into clusters, the reduced generators are `G T` with `T(i,k) = ±1`
if `gᵢ` is in cluster `k` and `0` otherwise: one `±1` per row, so `‖T‖∞ ≤ 1` and
[1, Eq. (1)] puts the result in `Z`. Which partition `k`-means++ finds does not matter.

## Inputs
* `Z` – zonotope
* `r` – cluster count
* `cl` – cluster assignment of the generators

## Hypotheses
* none

## Conclusion
* the clustered zonotope lies in `Z`

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-A]: the reduced zonotope is inside `Z`, for every partition. -/
theorem Zonotope.reduceUnderApproxCluster_inner [NeZero n] (Z : Zonotope (Vec ℝ n)) {r : ℕ}
    (cl : Fin Z.h → Fin r) : -- --- CONCL ---
    (Z.reduceUnderApproxCluster cl).construct ⊆ Z.construct := by -- --- PROOF ---
  -- the result is `G T` for `T(i,k) = sign(gᵢ(1))` if `gᵢ` is in `C_k`, else `0`
  let T : Mat ℝ Z.h r := fun i k => if cl i = k then (if Z.G i 0 < 0 then -1 else 1) else 0
  have hG : Z.reduceUnderApproxCluster cl = Z.mulGens T := by
    simp only [Zonotope.reduceUnderApproxCluster, Zonotope.mulGens]
    congr 1
    funext k
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : cl i = k <;> simp [T, h]
  rw [hG]
  refine Zonotope.mulGens_inner _ _ fun i => ?_
  refine Zonotope.sum_abs_le_one_of_subsingleton_support _ (fun k k' hk hk' => ?_) (fun k => ?_)
  · -- a nonzero entry is in the generator's own cluster
    have e : ∀ k, T i k ≠ 0 → cl i = k := fun k hk => by
      by_contra h; simp [T, h] at hk
    exact (e k hk).symm.trans (e k' hk')
  · simp only [T]
    split_ifs <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

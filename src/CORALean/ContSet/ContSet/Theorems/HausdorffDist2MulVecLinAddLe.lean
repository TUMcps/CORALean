module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.EuclideanHausdorffDistZero

@[expose] public section

/-!
# Perturbing a linear image moves it no further than the perturbation reaches, at `‖·‖₂`

[1, Prop. 10]: for a compact `S` and matrices `M1, M2`, `d_H((M1+M2)S, M1 S) ≤ d_H(0, M2 S)`, with
`d_H` [1, Def. 5]'s Hausdorff distance in `‖·‖₂` — `hausdorffDist₂`, not the supremum-norm
`Metric.hausdorffDist` that `hausdorffDist_mulVecLin_add_le` is stated at. The correspondence keeps
the same point of `S` on both sides, so the gap is `M2`'s image of that point, within `d_H(0, M2 S)`
of the origin by `norm₂_le_hausdorffDist₂_zero`. `S` compact is the one hypothesis, as [1] states
it: it makes `M2 S` bounded. Nonemptiness is never needed — an empty `S` leaves both sides `0`.

## Inputs
* `S` – set
* `M1` – matrix
* `M2` – perturbation matrix

## Hypotheses
* `hS` – `S` compact

## Conclusion
* Hausdorff distance is at most the distance of the perturbation's image from the origin

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10], at `‖·‖₂`: perturbing a linear image of a compact set by another matrix moves
it no further than that matrix's own image reaches from the origin. -/
theorem hausdorffDist₂_mulVecLin_add_le {S : Set (Vec ℝ n)} (M1 M2 : Mat ℝ m n)
    (hS : IsCompact S) : -- --- CONCL ---
    hausdorffDist₂ (mulVecLin (M1 + M2) '' S) (mulVecLin M1 '' S)
      ≤ hausdorffDist₂ ({0} : Set (Vec ℝ m)) (mulVecLin M2 '' S) := by -- --- PROOF ---
  have hB : Bornology.IsBounded (mulVecLin M2 '' S) :=
    (hS.image (mulVecLin M2).continuous_of_finiteDimensional).isBounded
  -- the gap at one point of `S` is `M2`'s image of it, a member of the set measured from `0`
  have hgap : ∀ s ∈ S, ‖mulVecLin M2 s‖₂
      ≤ hausdorffDist₂ ({0} : Set (Vec ℝ m)) (mulVecLin M2 '' S) :=
    fun s hs => norm₂_le_hausdorffDist₂_zero hB (Set.mem_image_of_mem _ hs)
  refine hausdorffDist₂_le_of_mem_dist Metric.hausdorffDist_nonneg ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨mulVecLin M1 s, Set.mem_image_of_mem _ hs, ?_⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply, add_sub_cancel_left]
    exact hgap s hs
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨mulVecLin (M1 + M2) s, Set.mem_image_of_mem _ hs, ?_⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply, sub_add_cancel_left, ← neg_one_smul ℝ,
      norm₂_smul, abs_neg, abs_one, one_mul]
    exact hgap s hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

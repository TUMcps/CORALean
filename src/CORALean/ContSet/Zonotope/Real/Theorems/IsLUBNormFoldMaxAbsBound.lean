module

public import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import Mathlib.Data.Finset.Fold

@[expose] public section

/-!
# A zonotope's largest sup norm, computed

`sup_{x∈Z} ‖x‖` in the infinity norm is the largest coordinate reach `absBound j =
|cⱼ| + Σᵢ |gᵢⱼ|`, folded from `0`: every coordinate's reach is attained
(`absBound_le_of_subset_closedBall`) and none is exceeded
(`subset_closedBall_of_absBound_le`). The fold from `0` is what `Vec ℝ 0`, whose only point
has norm `0`, needs. This is how [1, Alg. 1] computes the `sup_{x∈I} ‖x‖` in `α_r`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sup_{x∈Z} ‖x‖ = max(0, maxⱼ absBound j)`, as a least upper bound. -/
theorem Zonotope.isLUB_norm_image_fold_max_absBound (Z : Zonotope (Vec ℝ n)) :
    IsLUB ((fun x => ‖x‖) '' Z.construct)
      (Finset.univ.fold max 0 Z.absBound) := by -- --- PROOF ---
  have h0 : 0 ≤ Finset.univ.fold max 0 Z.absBound := (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have := Zonotope.subset_closedBall_of_absBound_le h0
      (fun j => (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_univ j, le_rfl⟩)) hx
    exact mem_closedBall_zero_iff.mp this
  · intro b hb
    have hsub : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) b := fun x hx =>
      mem_closedBall_zero_iff.mpr (hb ⟨x, hx, rfl⟩)
    refine (Finset.fold_max_le _).mpr
      ⟨?_, fun j _ => Zonotope.absBound_le_of_subset_closedBall hsub j⟩
    exact (norm_nonneg _).trans (hb ⟨Z.c, Zonotope.center_mem_construct Z, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# The triangle inequality for the Euclidean Hausdorff distance

Mathlib's `Metric.hausdorffDist_triangle` reads `d_H(S,U) ≤ d_H(S,T) + d_H(T,U)` only where
the first distance is finite, which for these sets is what boundedness and non-emptiness
supply. Stated here at `‖·‖₂` so the reachability error accumulations — each a chain
through one intermediate computed set — can use it without unfolding `toEuclidean`.

The middle set is the one that has to be nonempty and bounded: it is the one both halves of
the chain are measured against.

## Inputs
* `S` – first set
* `T` – middle set
* `U` – last set

## Hypotheses
* `hS` – the first set is bounded
* `hSne` – the first set is nonempty
* `hT` – the middle set is bounded
* `hTne` – the middle set is nonempty

## Conclusion
* the Euclidean Hausdorff distance obeys the triangle inequality
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `d_H(S,U) ≤ d_H(S,T) + d_H(T,U)`, read at `‖·‖₂`, for bounded nonempty sets. -/
theorem hausdorffDist₂_triangle {S T U : Set (Vec ℝ n)} (hS : Bornology.IsBounded S)
    (hSne : S.Nonempty) (hT : Bornology.IsBounded T) (hTne : T.Nonempty) : -- --- CONCL ---
    hausdorffDist₂ S U ≤ hausdorffDist₂ S T + hausdorffDist₂ T U := by -- --- PROOF ---
  have himg : ∀ X : Set (Vec ℝ n), Bornology.IsBounded X →
      Bornology.IsBounded (toEuclidean '' X) := by
    intro X hX
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hX
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt n * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_toEuclidean]
    exact (norm₂_le_sqrt_mul_norm z).trans
      (mul_le_mul_of_nonneg_left (hC z hz) (Real.sqrt_nonneg _))
  -- finiteness of the first leg is all Mathlib's triangle inequality asks
  have hfin : Metric.hausdorffEDist (toEuclidean '' S) (toEuclidean '' T) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hSne.image _) (hTne.image _)
      (himg _ hS) (himg _ hT)
  exact Metric.hausdorffDist_triangle hfin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

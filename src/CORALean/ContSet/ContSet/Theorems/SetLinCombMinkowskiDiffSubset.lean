module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Minkowski difference distributes over the hull of two sets

[1, Lemma 1]: for compact, convex, nonempty `S1, S2, S3 ⊂ ℝⁿ`, `conv(S1 ⊖ S3, S2 ⊖ S3) ⊆ conv(S1,
S2) ⊖ S3`. Stated on `Set.linComb`, which is CORA's convex hull exactly when both operands are
convex, so this is a literal reading of the claim.

The inclusion needs none of the three hypotheses: a point of the left side is `λ•(y1+z) +
(1-λ)•(y2+z)` for any `z ∈ S3`, and that is already a point of the right side. They are what the
paper needs to identify `conv` with pairwise segments, and are dropped as in
`minkowskiDiff_add_subset_add`.

## Inputs
* `S1` – first minuend
* `S2` – second minuend
* `S3` – subtrahend

## Hypotheses
* none

## Conclusion
* the linear combination of the differences lies in the difference of the linear combination

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: the segments of two Minkowski differences by the same set sit
inside the Minkowski difference of the segments by that set. -/
theorem setLinComb_minkowskiDiff_subset (S1 S2 S3 : Set α) :
    Set.linComb (minkowskiDiff S1 S3) (minkowskiDiff S2 S3) ⊆
      minkowskiDiff (Set.linComb S1 S2) S3 := by
  rintro x ⟨y1, hy1, y2, hy2, lam, hlam, rfl⟩ z hz
  exact ⟨y1 + z, hy1 z hz, y2 + z, hy2 z hz, lam, hlam, by module⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

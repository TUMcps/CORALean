import CORALean.ContSet.ContSet.ContSet

/-!
# Minkowski difference distributes over the hull of two sets

[1, Lemma 1]: for compact, convex, nonempty `S1, S2, S3 ⊂ ℝⁿ`,
`conv(S1 ⊖ S3, S2 ⊖ S3) ⊆ conv(S1, S2) ⊖ S3`. Stated on `segments`, which is
CORA's convex hull exactly when both operands are convex — the paper's own
hypothesis on `S1` and `S2` — so this is a literal reading of the claim rather
than a restatement of it.

The inclusion needs none of the paper's three hypotheses: a point of the left
side is `λ•(y1+z) + (1-λ)•(y2+z)` for any `z ∈ S3`, whatever `y1, y2, λ` witness
it, and that is already a point of the right side. Compactness, convexity and
nonemptiness of `S1, S2, S3` are what the paper needs to identify `conv` with
pairwise segments in the first place — not asked for here, following the
convention already set by `minkowskiDiff_add_subset_add`, which drops a
hypothesis its own proof does not use.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: the segments of two Minkowski differences by the same set sit
inside the Minkowski difference of the segments by that set. -/
theorem segments_minkowskiDiff_subset (S1 S2 S3 : Set α) :
    segments (minkowskiDiff S1 S3) (minkowskiDiff S2 S3) ⊆
      minkowskiDiff (segments S1 S2) S3 := by
  rintro x ⟨y1, hy1, y2, hy2, lam, hlam, rfl⟩ z hz
  exact ⟨y1 + z, hy1 z hz, y2 + z, hy2 z hz, lam, hlam, by module⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

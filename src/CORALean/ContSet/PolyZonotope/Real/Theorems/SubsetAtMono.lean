import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt

/-!
# `subsetAt` is monotone in the sub-box

`subsetAt` is `point`'s image of the sub-box that names [1, Thm. 1]'s dependent subset,
and image is monotone in the set mapped: a larger sub-box reaches more of it.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger sub-box of the factor domain reaches a larger subset. -/
theorem PolyZonotope.subsetAt_mono (pZ : PolyZonotope α) {B B' : Set (Fin pZ.p → ℝ)}
    (h : B ⊆ B') : pZ.subsetAt B ⊆ pZ.subsetAt B' :=
  Set.image_mono h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

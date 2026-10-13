import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn

/-!
# A larger sub-box of the factors evaluates to a larger set

`subsetAt_mono` at [1, Def. 3]'s own evaluation function, its (13): the
independent block is the same on both sides, so only the dependent half moves and
the image is monotone. Property (6) of [1] for "hold the factors in `B`", and
what lets a chain of dependency statements be relaxed one step at a time.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger sub-box of the factor domain evaluates to a larger set. -/
theorem PolyZonotope.evalOn_mono (pZ : PolyZonotope α) {B B' : Set (Fin pZ.p → ℝ)}
    (h : B ⊆ B') : pZ.evalOn B ⊆ pZ.evalOn B' := by
  rintro _ ⟨a, ha, β, hβ, rfl⟩
  exact ⟨a, h ha, β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

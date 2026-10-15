module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# When the zonotope norm is defined

`[1, Lemma 2]`: for a zonotope with generator matrix `G`, these are equivalent — `G` has
rank `n`; `Z` has an interior point; `G` is onto; `ν` is defined on all of `ℝⁿ` and
positive definite. Each is stated against "onto". Rank `n` is the range being everything,
the interior is `isFullDim_iff` (the generators span), and definiteness is `coeffNorm`'s
at an attained minimum. The printed `m ≥ n` and center `0` are not needed.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_tfae (Z : Zonotope (Vec ℝ n)) :
    (Module.finrank ℝ (LinearMap.range Z.genMap) = n ↔ Function.Surjective Z.genMap) ∧
      ((interior Z.construct).Nonempty ↔ Function.Surjective Z.genMap) ∧
      (((∀ v, ∃ γ, Z.genMap γ = v) ∧ ∀ v, Z.zonotopeNorm v = 0 ↔ v = 0) ↔
        Function.Surjective Z.genMap) := by -- --- PROOF ---
  -- the range of the generator map is the span of the generators
  have hrange : LinearMap.range Z.genMap = Submodule.span ℝ (Set.range Z.G) := by
    rw [← Fintype.range_linearCombination ℝ Z.G]
    congr 1
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top]
    constructor
    · intro h
      exact Submodule.eq_top_of_finrank_eq (by simpa using h)
    · intro h
      rw [h, finrank_top]
      simp
  · rw [Zonotope.isFullDim_iff, ← hrange, LinearMap.range_eq_top]
  · constructor
    · exact fun h => h.1
    · intro hG
      exact ⟨hG, fun v => coeffNorm_eq_zero_iff _ (hG v)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

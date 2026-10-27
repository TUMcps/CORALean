module

public import CORALean.Specification.STL.Operations.FactorMeet
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# [1, Alg. 2, l. 12] read index by index loses unsafe factors

Line 12 prints `V ← (V(1) ∩ W(1), ..., V(|V|) ∩ W(|W|))`. Read as `List.zipWith`, two passes
over `V = [ℝ]` with `W₁ = [{0}, {1}]` and `W₂ = [{1}, {0}]` give `[∅]`: the zip pairs `ℝ` with
`{0}` only and `{0}` with `{1}` only. Take the factor `0` of a trajectory that is `0` throughout,
so `W₁` and `W₂` are the polytopes `P_hjkl` of two disjuncts, each entered by it at one of its two
polytopes: the formula fails for it, since neither disjunct holds, and `0` is in a polytope of
`STL.factorMeet` (all pairs) but in none of the zipped ones, so the zipped check would call it
safe. The pairs of `V` and `W` are all of them, as CORA's `aux_orConstraints` forms.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* reading the factor intersection index by index loses unsafe factors

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.factorMeet_zip_counterexample : -- --- CONCL ---
    let W₁ : List (Set ℝ) := [{0}, {1}]
    let W₂ : List (Set ℝ) := [{1}, {0}]
    -- the factor `0` is in a polytope of each disjunct
    (∀ W ∈ [W₁, W₂], ∃ w ∈ W, (0 : ℝ) ∈ w) ∧
    (∃ v ∈ STL.factorMeet (STL.factorMeet [Set.univ] W₁) W₂, (0 : ℝ) ∈ v) ∧
    ∀ v ∈ List.zipWith (· ∩ ·) (List.zipWith (· ∩ ·) [Set.univ] W₁) W₂,
      (0 : ℝ) ∉ v := by -- --- PROOF ---
  intro W₁ W₂
  refine ⟨?_, ?_, ?_⟩
  · -- `0` is in `{0}` in both
    intro W hW
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact ⟨{0}, by simp [W₁], rfl⟩
    · exact ⟨{0}, by simp [W₂], rfl⟩
  · -- `ℝ ∩ {0} ∩ {0}`
    refine ⟨Set.univ ∩ {0} ∩ {0}, ?_, by simp⟩
    simp [STL.factorMeet, W₁, W₂]
  · -- the zips are `[{0}]` and then `[{0} ∩ {1}] = [∅]`
    intro v hv
    simp [W₁, W₂] at hv
    rw [hv]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

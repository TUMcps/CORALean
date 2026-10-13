module

public import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormLeIff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `[1, Eq. 11]` fails for `p ≠ ∞`

In `ℝ¹`: the inbody `E₂(G, c) = 1 + [-1, 1] = [0, 2]` (`G = 1`, `c = 1`; every `p`-ball of
`ℝ¹` is `[-1, 1]`) and the circumbody `Z(H) = [-1, 1]`, `d = 0`, with facets `x ≤ 1`,
`-x ≤ 1`. The containment radius `max_{|α| ≤ 1} S(α + 1)` is `2`, at `α = 1`. The printed
formula gives, for either facet, `‖G'ᵀλᵢ‖₂ / |bᵢ| = ‖(±1, ±1)‖₂ = √2`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isGreatest_polyNorm_ellipsotope_counterexample :
    let Λ : Mat ℝ 2 1 := !![1; -1]
    let b : Vec ℝ 2 := ![1, 1]
    let c : Vec ℝ 1 := ![1]
    IsGreatest ((fun α : ℝ => HPolytope.polyNorm Λ b (![α] + c - 0)) '' Set.Icc (-1) 1) 2 ∧
      (∀ i, Real.sqrt ((Λ i 0) ^ 2 + ((Λ *ᵥ (c - 0)) i) ^ 2) / |b i| = Real.sqrt 2) ∧
      Real.sqrt 2 ≠ 2 := by -- --- PROOF ---
  intro Λ b c
  refine ⟨⟨⟨1, ⟨by norm_num, le_rfl⟩, le_antisymm ?_ ?_⟩, ?_⟩, fun i => ?_, ?_⟩
  -- at `α = 1` the first facet gives `2`, and no facet gives more
  · refine HPolytope.polyNorm_le_iff.mpr ⟨by norm_num, fun i => ?_⟩
    fin_cases i <;> norm_num [Λ, b, c, mulVec, dotProduct]
  · have := (HPolytope.polyNorm_le_iff.mp (le_refl (HPolytope.polyNorm Λ b (![1] + c - 0)))).2 0
    norm_num [Λ, b, c, mulVec, dotProduct] at this ⊢
    linarith
  · rintro _ ⟨α, ⟨h1, h2⟩, rfl⟩
    refine HPolytope.polyNorm_le_iff.mpr ⟨by norm_num, fun i => ?_⟩
    fin_cases i <;> norm_num [Λ, b, c, mulVec, dotProduct] <;> linarith
  -- each facet's printed value is `‖(±1, ±1)‖₂ = √2`
  · fin_cases i <;> norm_num [Λ, b, c, mulVec, dotProduct]
  · intro h
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [h] at this
    norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

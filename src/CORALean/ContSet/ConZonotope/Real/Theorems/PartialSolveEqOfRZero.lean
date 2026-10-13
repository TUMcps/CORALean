module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveConstructEq

@[expose] public section

/-!
# `r_j = 0` makes the partial solve exact, given an `R_j` that satisfies (A.1)

[1, Sec. 4.2 (choice of j)]: with `r_j ≡ max(0, max(|ρ^L_j|, |ρ^U_j|) − 1)`, "if `r_j = 0` for any
`j`, then (A.1) and (A.4) imply that `Z = Z̃` when `j` is selected". This is the inference with
(A.1) as its hypothesis. `ρ^L_j ≤ ξ_j ≤ ρ^U_j` for every `ξ` with `Aξ = b` and `|ξ_i| ≤ 1` for
`i ≠ j`, and `r_j = 0`, make the dropped bound `|ξ_j| ≤ 1` redundant. Then `Z̃`, which is `Z`
without that bound (`partialSolve_construct_eq`), is `Z`.

The hypothesis is the one Algorithm 1 does not deliver: its `R_j` need not satisfy (A.1)
(`tightenER_not_superset`), and then `r_j = 0` does not give `Z = Z̃`
(`partialSolve_rZero_counterexample`).

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2 (choice of j)]: an interval `[ρL, ρU]` satisfying (A.1) at `j`, with `r_j = 0`,
gives `Z̃ = Z`. -/
theorem ConZonotope.partialSolve_eq_of_rZero {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) (ρL ρU : ℝ)
    (hA1 : ∀ ξ : Vec ℝ h, (∀ i, i ≠ j → |ξ i| ≤ 1) → (∀ i, (A *ᵥ ξ) i = b i) →
      ρL ≤ ξ j ∧ ξ j ≤ ρU)
    (hr : max 0 (max |ρL| |ρU| - 1) = 0) :
    (ConZonotope.partialSolve c G A b r j).construct
      = (ConZonotope.ofMat c G A b).construct := by -- --- PROOF ---
  rw [ConZonotope.partialSolve_construct_eq c G A b r j hAj]
  ext x
  rw [Set.mem_setOf_eq, ConZonotope.mem_ofMat_iff]
  -- `r_j = 0` is `|ρL|, |ρU| ≤ 1`
  have hL : |ρL| ≤ 1 := by
    have := (max_eq_left_iff.mp hr); linarith [le_max_left |ρL| |ρU|]
  have hU : |ρU| ≤ 1 := by
    have := (max_eq_left_iff.mp hr); linarith [le_max_right |ρL| |ρU|]
  constructor
  · rintro ⟨ξ, hξ, hA, rfl⟩
    -- the dropped bound is redundant: `ξ_j ∈ [ρL, ρU] ⊆ [-1, 1]`
    refine ⟨ξ, fun i => ?_, hA, rfl⟩
    rcases eq_or_ne i j with rfl | hi
    · obtain ⟨h1, h2⟩ := hA1 ξ hξ hA
      exact abs_le.mpr ⟨by linarith [neg_abs_le ρL], by linarith [le_abs_self ρU]⟩
    · exact hξ i hi
  · rintro ⟨ξ, hξ, hA, rfl⟩
    exact ⟨ξ, fun i _ => hξ i, hA, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveConstructEq
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The Hausdorff error of the partial solve, over coefficients

[1, Sec. 4.2 (choice of j)]: with `H_j ≡ max_{z̃∈Z̃} min_{z∈Z} ‖z̃ − z‖₂`, "it follows" from (A.4)
that `H_j = max_ξ min_{δ∈B∞(A,b)} ‖G(ξ − δ)‖₂` subject to `Aξ = b`, `|ξ_i| ≤ 1`, `i ≠ j`. `Z̃` is
the image of those `ξ` under `ξ ↦ Gξ + c` (`partialSolve_construct_eq`), `Z` the image of
`B∞(A, b)`, and the center cancels in the difference. The `max` and `min` are `sSup` and `sInf`
here, the same values whenever they are attained.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – constraint row to solve
* `j` – coefficient to eliminate

## Hypotheses
* `hAj` – pivot entry nonzero

## Conclusion
* the Hausdorff error equals the error over the coefficients

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

/-- [1, Sec. 4.2 (choice of j)]: `H_j` read over the coefficients, `Gξ + c ∈ Z̃` against
`Gδ + c ∈ Z`. -/
theorem ConZonotope.partialSolve_hausdorff_eq {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) : -- --- CONCL ---
    sSup ((fun zt => sInf ((fun z => ‖zt - z‖₂) '' (ConZonotope.ofMat c G A b).construct))
        '' (ConZonotope.partialSolve c G A b r j).construct)
      = sSup ((fun ξ : Vec ℝ h => sInf ((fun δ : Vec ℝ h => ‖∑ k, (ξ k - δ k) • G k‖₂)
          '' {δ | (∀ i, |δ i| ≤ 1) ∧ ∀ i, (A *ᵥ δ) i = b i}))
        '' {ξ | (∀ i, i ≠ j → |ξ i| ≤ 1) ∧ ∀ i, (A *ᵥ ξ) i = b i}) := by -- --- PROOF ---
  -- both sets as images of their coefficient sets under `ξ ↦ Gξ + c`
  have hZ : (ConZonotope.ofMat c G A b).construct
      = (fun δ : Vec ℝ h => c + ∑ k, δ k • G k) ''
          {δ | (∀ i, |δ i| ≤ 1) ∧ ∀ i, (A *ᵥ δ) i = b i} := by
    ext x
    rw [ConZonotope.mem_ofMat_iff]
    constructor
    · rintro ⟨β, hβ, hA, rfl⟩; exact ⟨β, ⟨hβ, hA⟩, rfl⟩
    · rintro ⟨β, ⟨hβ, hA⟩, rfl⟩; exact ⟨β, hβ, hA, rfl⟩
  -- `Z̃` likewise, through (A.4)
  have hZt : (ConZonotope.partialSolve c G A b r j).construct
      = (fun ξ : Vec ℝ h => c + ∑ k, ξ k • G k) ''
          {ξ | (∀ i, i ≠ j → |ξ i| ≤ 1) ∧ ∀ i, (A *ᵥ ξ) i = b i} := by
    rw [ConZonotope.partialSolve_construct_eq c G A b r j hAj]
    ext x
    constructor
    · rintro ⟨ξ, hξ, hA, rfl⟩; exact ⟨ξ, ⟨hξ, hA⟩, rfl⟩
    · rintro ⟨ξ, ⟨hξ, hA⟩, rfl⟩; exact ⟨ξ, hξ, hA, rfl⟩
  -- compare the two programs point by point
  rw [hZ, hZt, Set.image_image]
  congr 1
  refine Set.image_congr fun ξ _ => ?_
  rw [Set.image_image]
  congr 1
  refine Set.image_congr fun δ _ => ?_
  -- the center cancels
  congr 1
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

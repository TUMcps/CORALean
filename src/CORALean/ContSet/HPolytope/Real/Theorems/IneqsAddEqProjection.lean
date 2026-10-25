module

public import CORALean.ContSet.HPolytope.Real.Theorems.IneqsBlockDiagEq

@[expose] public section

/-!
# The Minkowski sum of two H-polytopes, as a projection

[1, Eq. 26]: `⟨A₁, b₁⟩ ⊕ ⟨A₂, b₂⟩ = [Iₙ Iₙ] ⟨blkdiag(A₁, A₂), [b₁; b₂]⟩`, the image of the
Cartesian product [1, Eq. 29] under the map adding the two blocks. The image is the projection
the paper computes by Fourier–Motzkin elimination; it is stated here as an image, the existence of
a halfspace form being `HPolytope.exists_construct_eq_image_fst`.

## Inputs
* `A₁` – `q₁ × n` matrix
* `b₁` – offset vector of length `q₁`
* `A₂` – `q₂ × n` matrix
* `b₂` – offset vector of length `q₂`

## Hypotheses
* none

## Conclusion
* the Minkowski sum of two H-polytopes, as a projection

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {q₁ q₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_add_eq_projection (A₁ : Mat ℝ q₁ n) (b₁ : Vec ℝ q₁) (A₂ : Mat ℝ q₂ n)
    (b₂ : Vec ℝ q₂) : -- --- CONCL ---
    (HPolytope.ineqs A₁ b₁).construct + (HPolytope.ineqs A₂ b₂).construct =
      ((Matrix.of fun i => Fin.append ((1 : Mat ℝ n n) i) ((1 : Mat ℝ n n) i)) *ᵥ ·) ''
        (HPolytope.ineqs (Matrix.of fun r => Fin.addCases (fun r₁ => Fin.append (A₁ r₁) 0)
          (fun r₂ => Fin.append 0 (A₂ r₂)) r) (Fin.append b₁ b₂)).construct := by -- --- PROOF ---
  -- `[I I]` adds the two blocks
  have hII : ∀ x₁ x₂ : Vec ℝ n,
      (Matrix.of fun i => Fin.append ((1 : Mat ℝ n n) i) ((1 : Mat ℝ n n) i)) *ᵥ
        Fin.append x₁ x₂ = x₁ + x₂ := by
    intro x₁ x₂
    funext i
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, Pi.add_apply]
    simp [Matrix.one_apply]
  rw [HPolytope.ineqs_blockDiag_eq, ← Set.image_comp]
  ext x
  simp only [Set.mem_image, Set.mem_prod, Function.comp_apply, Prod.exists, hII, Set.mem_add]
  constructor
  · rintro ⟨x₁, h₁, x₂, h₂, rfl⟩
    exact ⟨x₁, x₂, ⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨x₁, x₂, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨x₁, h₁, x₂, h₂, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

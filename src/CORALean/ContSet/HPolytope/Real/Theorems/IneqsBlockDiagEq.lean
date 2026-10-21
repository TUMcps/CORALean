module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The Cartesian product of two H-polytopes

[1, Eq. 29]: `⟨A₁, b₁⟩ × ⟨A₂, b₂⟩ = ⟨blkdiag(A₁, A₂), [b₁; b₂]⟩`, the rows of each acting on its
own block of coordinates. The product is read as the paper writes it, stacked:
`[s₁; s₂] = Fin.append s₁ s₂`.

## Inputs
* `A₁` – `q₁ × n₁` matrix
* `b₁` – offset vector of length `q₁`
* `A₂` – `q₂ × n₂` matrix
* `b₂` – offset vector of length `q₂`

## Hypotheses
* none

## Conclusion
* the block-diagonal polytope is the product of the two polytopes, coordinates concatenated

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q₁ q₂ n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_blockDiag_eq (A₁ : Mat ℝ q₁ n₁) (b₁ : Vec ℝ q₁) (A₂ : Mat ℝ q₂ n₂)
    (b₂ : Vec ℝ q₂) : -- --- CONCL ---
    (HPolytope.ineqs (Matrix.of fun r => Fin.addCases (fun r₁ => Fin.append (A₁ r₁) 0)
        (fun r₂ => Fin.append 0 (A₂ r₂)) r) (Fin.append b₁ b₂)).construct =
      (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
        ((HPolytope.ineqs A₁ b₁).construct ×ˢ
          (HPolytope.ineqs A₂ b₂).construct) := by -- --- PROOF ---
  -- a block row sees only its own block of coordinates
  have hrow : ∀ (z : Vec ℝ (n₁ + n₂)) (r : Fin (q₁ + q₂)),
      ((Matrix.of fun r => Fin.addCases (fun r₁ => Fin.append (A₁ r₁) 0)
        (fun r₂ => Fin.append (0 : Vec ℝ n₁) (A₂ r₂)) r) *ᵥ z) r =
        Fin.addCases (fun r₁ => (A₁ *ᵥ fun i => z (Fin.castAdd n₂ i)) r₁)
          (fun r₂ => (A₂ *ᵥ fun i => z (Fin.natAdd n₁ i)) r₂) r := by
    intro z r
    refine Fin.addCases (fun r₁ => ?_) (fun r₂ => ?_) r <;>
      simp [mulVec, dotProduct, Fin.sum_univ_add]
  ext z
  rw [HPolytope.mem_ineqs_iff]
  constructor
  -- a point of the stacked system splits into a point of each factor
  · intro h
    refine ⟨(fun i => z (Fin.castAdd n₂ i), fun i => z (Fin.natAdd n₁ i)), ⟨?_, ?_⟩, ?_⟩
    · refine HPolytope.mem_ineqs_iff.mpr fun r₁ => ?_
      have := h (Fin.castAdd q₂ r₁)
      rwa [hrow, Fin.addCases_left, Fin.append_left] at this
    · refine HPolytope.mem_ineqs_iff.mpr fun r₂ => ?_
      have := h (Fin.natAdd q₁ r₂)
      rwa [hrow, Fin.addCases_right, Fin.append_right] at this
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  · rintro ⟨⟨x₁, x₂⟩, ⟨h₁, h₂⟩, rfl⟩ r
    rw [hrow]
    refine Fin.addCases (fun r₁ => ?_) (fun r₂ => ?_) r
    · simpa using HPolytope.mem_ineqs_iff.mp h₁ r₁
    · simpa using HPolytope.mem_ineqs_iff.mp h₂ r₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

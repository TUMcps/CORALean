import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

/-!
# The Minkowski sum of two AH-polytopes

`[1, Eq. 6]`: `(x̄₁ + X₁ P₁) ⊕ (x̄₂ + X₂ P₂) = x̄₁ + x̄₂ + (X₁, X₂) P_⊕` with
`P_⊕ = {z | blk(H₁, H₂) z ≤ [h₁, h₂]}`, the product of the two coefficient polytopes. The
coefficient vector is `Fin.append` of the two, `(X₁, X₂)` the horizontal stacking and
`blk(H₁, H₂)` the block-diagonal rows; a point of `P_⊕` splits back into its two halves.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n n₁ n₂ q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_add_eq (x₁ x₂ : Vec ℝ n) (X₁ : Mat ℝ n n₁) (X₂ : Mat ℝ n n₂)
    (H₁ : Mat ℝ q₁ n₁) (h₁ : Vec ℝ q₁) (H₂ : Mat ℝ q₂ n₂) (h₂ : Vec ℝ q₂) :
    HPolytope.ahPolytope x₁ X₁ (HPolytope.ineqs H₁ h₁)
        + HPolytope.ahPolytope x₂ X₂ (HPolytope.ineqs H₂ h₂)
      = HPolytope.ahPolytope (x₁ + x₂) (Matrix.of fun i k => Fin.append (X₁ i) (X₂ i) k)
          (HPolytope.ineqs (Matrix.of fun r k => Fin.addCases (fun r₁ => Fin.append (H₁ r₁) 0 k)
            (fun r₂ => Fin.append 0 (H₂ r₂) k) r) (Fin.append h₁ h₂)) := by -- --- PROOF ---
  -- the stacked map and the block rows, read on a split coefficient vector
  have hX : ∀ p₁ p₂, (Matrix.of fun i k => Fin.append (X₁ i) (X₂ i) k) *ᵥ Fin.append p₁ p₂
      = X₁ *ᵥ p₁ + X₂ *ᵥ p₂ := by
    intro p₁ p₂; ext i
    simp only [Pi.add_apply, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, Matrix.of_apply]
  have hH : ∀ (p₁ : Vec ℝ n₁) (p₂ : Vec ℝ n₂),
      Fin.append p₁ p₂ ∈ (HPolytope.ineqs (Matrix.of fun r k => Fin.addCases
        (fun r₁ => Fin.append (H₁ r₁) 0 k) (fun r₂ => Fin.append 0 (H₂ r₂) k) r)
        (Fin.append h₁ h₂)).construct ↔
      p₁ ∈ (HPolytope.ineqs H₁ h₁).construct ∧ p₂ ∈ (HPolytope.ineqs H₂ h₂).construct := by
    intro p₁ p₂
    rw [HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff,
      Fin.forall_fin_add]
    simp only [mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]
  -- a sum of two points is the stacked map at the appended coefficients, and back
  ext x
  constructor
  · rintro ⟨_, ⟨p₁, hp₁, rfl⟩, _, ⟨p₂, hp₂, rfl⟩, rfl⟩
    exact ⟨Fin.append p₁ p₂, (hH p₁ p₂).mpr ⟨hp₁, hp₂⟩, by rw [hX]; abel_nf⟩
  · rintro ⟨z, hz, rfl⟩
    rw [← Fin.append_castAdd_natAdd (f := z)] at hz ⊢
    obtain ⟨hp₁, hp₂⟩ := (hH _ _).mp hz
    exact Set.mem_add.mpr ⟨_, ⟨_, hp₁, rfl⟩, _, ⟨_, hp₂, rfl⟩, by rw [hX]; abel⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

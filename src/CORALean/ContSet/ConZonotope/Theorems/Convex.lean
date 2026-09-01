import CORALean.ContSet.ConZonotope.ConZonotope

/-!
# A constrained zonotope is convex

The affine image of a polytope. Read off the coefficients: a weighted average of
two admissible ones stays in the unit box, and satisfies `A β = b` because the
constraint is affine and the weights sum to one — that second half is all the
constraints add over a zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem ConZonotope.convex_construct (C : ConZonotope α) : Convex ℝ C.construct := by
  rintro x ⟨β₁, hβ₁, hA₁, rfl⟩ y ⟨β₂, hβ₂, hA₂, rfl⟩ s t hs ht hst
  have hbox : ∀ j, |s * β₁ j + t * β₂ j| ≤ 1 := by
    intro j
    have h1 : |s * β₁ j| ≤ s := by
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |β₁ j| ≤ s * 1 := mul_le_mul_of_nonneg_left (hβ₁ j) hs
        _ = s := mul_one s
    have h2 : |t * β₂ j| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht]
      calc t * |β₂ j| ≤ t * 1 := mul_le_mul_of_nonneg_left (hβ₂ j) ht
        _ = t := mul_one t
    calc |s * β₁ j + t * β₂ j| ≤ |s * β₁ j| + |t * β₂ j| := abs_add_le _ _
      _ ≤ s + t := add_le_add h1 h2
      _ = 1 := hst
  have hA : C.A *ᵥ (s • β₁ + t • β₂) = C.b := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hA₁, hA₂, ← add_smul, hst,
      one_smul]
  have hval : ∑ j, (s * β₁ j + t * β₂ j) • C.G j
      = s • (∑ j, β₁ j • C.G j) + t • ∑ j, β₂ j • C.G j := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [add_smul, smul_smul, smul_smul]
  refine ⟨fun j => s * β₁ j + t * β₂ j, hbox, hA, ?_⟩
  calc s • (C.c + ∑ j, β₁ j • C.G j) + t • (C.c + ∑ j, β₂ j • C.G j)
      = (s + t) • C.c + (s • (∑ j, β₁ j • C.G j) + t • ∑ j, β₂ j • C.G j) := by
        rw [smul_add, smul_add, add_smul]; abel
    _ = C.c + ∑ j, (s * β₁ j + t * β₂ j) • C.G j := by rw [hst, one_smul, hval]

end CORALean.Real

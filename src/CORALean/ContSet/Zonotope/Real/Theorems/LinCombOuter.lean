import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `linComb` contains every segment between the two zonotopes

The coefficients are `λ β₁` and `(1-λ) β₂` on the two generator blocks, both
back in `[-1,1]` because `λ ∈ [0,1]`, and `2λ - 1` on the generator spanning the
half-difference of the centres.

Nothing here asks for convexity: the claim is about the segments themselves, so
it is the statement a non-convex representation could also make.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.aux_sum_univ_linComb {Z₁ Z₂ : Zonotope α}
    (f : Fin (Z₁.h + Z₂.h + 1) → α) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f

set_option maxHeartbeats 400000 in
theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope α) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct := by
  rintro x ⟨y₁, ⟨β₁, hβ₁, rfl⟩, y₂, ⟨β₂, hβ₂, rfl⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j))
      (fun _ : Fin 1 => 2 * lam - 1), ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using Zonotope.abs_mul_le_one hl0 hl1 (hβ₁ j)
      · intro j
        simpa using Zonotope.abs_mul_le_one (by linarith) (by linarith) (hβ₂ j)
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · rw [Zonotope.aux_sum_univ_linComb,
      Fin.sum_univ_add]
    simp only [Zonotope.linComb, Fin.append_left, Fin.append_right, Fin.sum_univ_one,
      smul_smul]
    -- the weight comes out of each generator block, which `module` cannot do
    -- for itself: a sum is one atom to it
    have h₁ : (∑ j, (lam * β₁ j) • Z₁.G j) = lam • ∑ j, β₁ j • Z₁.G j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
    have h₂ : (∑ j, ((1 - lam) * β₂ j) • Z₂.G j) = (1 - lam) • ∑ j, β₂ j • Z₂.G j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
    rw [h₁, h₂]
    -- what is left is the centres, which the fresh generator carries
    module

end CORALean.Real

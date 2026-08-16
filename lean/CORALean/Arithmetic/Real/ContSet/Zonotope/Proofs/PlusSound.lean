import CORALean.Arithmetic.Real.ContSet.Zonotope.API

/-!
# `Zonotope.plus` over-approximates the Minkowski sum

The witness is `Fin.append β₁ β₂`: concatenated generators take concatenated
coefficients. `Fin.addCases` and `Fin.sum_univ_add` split the bound and the sum
the same way. The inclusion is an equality; only this direction is recorded.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Zonotope.Proofs

open Pointwise

variable {n h k : ℕ}

theorem plus_sound (Z₁ : Zonotope n h) (Z₂ : Zonotope n k) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct := by
  rintro _ ⟨x₁, ⟨β₁, hβ₁, hx₁⟩, x₂, ⟨β₂, hβ₂, hx₂⟩, rfl⟩
  refine ⟨Fin.append β₁ β₂, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ₁ l
    · simpa using hβ₂ l
  · simp only [Zonotope.plus, Pi.add_apply, hx₁ i, hx₂ i, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
    ring

end CORALean.Arithmetic.Real.Zonotope.Proofs

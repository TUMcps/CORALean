import CORALean.Arithmetic.Real.ContSet.Zonotope.API

/-!
# `Zonotope.plus` is exactly the Minkowski sum

The witness is `Fin.append β₁ β₂`: concatenated generators take concatenated
coefficients. `Fin.addCases` and `Fin.sum_univ_add` split the bound and the sum
the same way, and splitting a coefficient vector the other way gives the
converse, so concatenation loses nothing.

No `plus_outer` here: the float `plus` displaces the centre, so it reproves this
against the displaced centre rather than composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   17-August-2026 (exactness)
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Zonotope.Proofs

open Pointwise

variable {n h k : ℕ}

theorem plus_exact (Z₁ : Zonotope n h) (Z₂ : Zonotope n k) :
    Z₁.construct + Z₂.construct = (Z₁.plus Z₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨β₁, hβ₁, hx₁⟩, x₂, ⟨β₂, hβ₂, hx₂⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, ?_, fun i => ?_⟩
    · refine Fin.addCases (fun l => ?_) (fun l => ?_)
      · simpa using hβ₁ l
      · simpa using hβ₂ l
    · simp only [Zonotope.plus, Pi.add_apply, hx₁ i, hx₂ i, Fin.sum_univ_add,
        Fin.append_left, Fin.append_right]
      ring
  · rintro x ⟨β, hβ, hx⟩
    refine ⟨fun i => Z₁.c i + ∑ j, Z₁.G i j * β (Fin.castAdd k j),
            ⟨fun j => β (Fin.castAdd k j), fun j => hβ _, fun _ => rfl⟩,
            fun i => Z₂.c i + ∑ j, Z₂.G i j * β (Fin.natAdd h j),
            ⟨fun j => β (Fin.natAdd h j), fun j => hβ _, fun _ => rfl⟩, ?_⟩
    funext i
    simp only [Pi.add_apply, hx i, Zonotope.plus, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
    ring

end CORALean.Arithmetic.Real.Zonotope.Proofs

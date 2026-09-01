import CORALean.ContSet.ConZonotope.Operations.Plus

/-!
# `ConZonotope.plus` is exactly the Minkowski sum

The witness is `Fin.append β₁ β₂`, as for a zonotope. What the constraints add is
that the concatenated coefficients satisfy the block-diagonal system exactly when
each half satisfies its own, which is `aux_constraint_plus` — the off-diagonal
block contributes a sum of zeros.

So a constrained zonotope is closed under Minkowski sums without giving anything
up, which is what makes it worth carrying constraints at all.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's
type. -/
theorem ConZonotope.aux_sum_univ_plus {M : Type} [AddCommMonoid M] {C₁ C₂ : ConZonotope α}
    (f : Fin (C₁.h + C₂.h) → M) :
    ∑ j : Fin (C₁.plus C₂).h, f j
      = ∑ j, f (Fin.castAdd C₂.h j) + ∑ j, f (Fin.natAdd C₁.h j) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
theorem ConZonotope.aux_mulVec_plus_left (C₁ C₂ : ConZonotope α)
    (β : Fin (C₁.h + C₂.h) → ℝ) (i : Fin C₁.q) :
    ((C₁.plus C₂).A *ᵥ β) (Fin.castAdd C₂.q i)
      = (C₁.A *ᵥ fun j => β (Fin.castAdd C₂.h j)) i := by
  show ∑ j : Fin (C₁.plus C₂).h, (C₁.plus C₂).A (Fin.castAdd C₂.q i) j * β j
    = ∑ j, C₁.A i j * β (Fin.castAdd C₂.h j)
  rw [ConZonotope.aux_sum_univ_plus]
  simp only [ConZonotope.plus, Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]

omit [Module ℝ α] in
theorem ConZonotope.aux_mulVec_plus_right (C₁ C₂ : ConZonotope α)
    (β : Fin (C₁.h + C₂.h) → ℝ) (i : Fin C₂.q) :
    ((C₁.plus C₂).A *ᵥ β) (Fin.natAdd C₁.q i)
      = (C₂.A *ᵥ fun j => β (Fin.natAdd C₁.h j)) i := by
  show ∑ j : Fin (C₁.plus C₂).h, (C₁.plus C₂).A (Fin.natAdd C₁.q i) j * β j
    = ∑ j, C₂.A i j * β (Fin.natAdd C₁.h j)
  rw [ConZonotope.aux_sum_univ_plus]
  simp only [ConZonotope.plus, Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

omit [Module ℝ α] in
theorem ConZonotope.aux_plus_b_left (C₁ C₂ : ConZonotope α) (i : Fin C₁.q) :
    (C₁.plus C₂).b (Fin.castAdd C₂.q i) = C₁.b i := by
  simp only [ConZonotope.plus, Fin.append_left]

omit [Module ℝ α] in
theorem ConZonotope.aux_plus_b_right (C₁ C₂ : ConZonotope α) (i : Fin C₂.q) :
    (C₁.plus C₂).b (Fin.natAdd C₁.q i) = C₂.b i := by
  simp only [ConZonotope.plus, Fin.append_right]

omit [Module ℝ α] in
/-- The constraint block is block diagonal, so the concatenated coefficients
satisfy it exactly when each half satisfies its own. -/
theorem ConZonotope.aux_constraint_plus (C₁ C₂ : ConZonotope α)
    (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.plus C₂).A *ᵥ β = (C₁.plus C₂).b
      ↔ (C₁.A *ᵥ fun j => β (Fin.castAdd C₂.h j)) = C₁.b
        ∧ (C₂.A *ᵥ fun j => β (Fin.natAdd C₁.h j)) = C₂.b := by
  constructor
  · intro hall
    constructor
    · funext i
      rw [← ConZonotope.aux_mulVec_plus_left, ← ConZonotope.aux_plus_b_left, hall]
    · funext i
      rw [← ConZonotope.aux_mulVec_plus_right, ← ConZonotope.aux_plus_b_right, hall]
  · rintro ⟨h₁, h₂⟩
    refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
    · rw [ConZonotope.aux_mulVec_plus_left, ConZonotope.aux_plus_b_left, h₁]
    · rw [ConZonotope.aux_mulVec_plus_right, ConZonotope.aux_plus_b_right, h₂]

theorem ConZonotope.aux_value_plus' (C₁ C₂ : ConZonotope α) (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.plus C₂).c + ∑ j : Fin (C₁.plus C₂).h, β j • (C₁.plus C₂).G j
      = (C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j)
        + (C₂.c + ∑ j, β (Fin.natAdd C₁.h j) • C₂.G j) := by
  rw [ConZonotope.aux_sum_univ_plus]
  simp only [ConZonotope.plus, Fin.append_left, Fin.append_right]
  abel

theorem ConZonotope.aux_value_plus (C₁ C₂ : ConZonotope α)
    (β₁ : Fin C₁.h → ℝ) (β₂ : Fin C₂.h → ℝ) :
    (C₁.plus C₂).c + ∑ j : Fin (C₁.plus C₂).h, Fin.append β₁ β₂ j • (C₁.plus C₂).G j
      = (C₁.c + ∑ j, β₁ j • C₁.G j) + (C₂.c + ∑ j, β₂ j • C₂.G j) := by
  rw [ConZonotope.aux_value_plus']
  simp only [Fin.append_left, Fin.append_right]

theorem ConZonotope.plus_exact (C₁ C₂ : ConZonotope α) :
    C₁.construct + C₂.construct = (C₁.plus C₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨β₁, hβ₁, hA₁, rfl⟩, _, ⟨β₂, hβ₂, hA₂, rfl⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, (ConZonotope.aux_value_plus C₁ C₂ β₁ β₂).symm⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · refine (ConZonotope.aux_constraint_plus C₁ C₂ _).mpr ⟨?_, ?_⟩
      · rw [show (fun j => Fin.append β₁ β₂ (Fin.castAdd C₂.h j)) = β₁ from
          funext fun j => Fin.append_left β₁ β₂ j]
        exact hA₁
      · rw [show (fun j => Fin.append β₁ β₂ (Fin.natAdd C₁.h j)) = β₂ from
          funext fun j => Fin.append_right β₁ β₂ j]
        exact hA₂
  · rintro _ ⟨β, hβ, hA, rfl⟩
    obtain ⟨hA₁, hA₂⟩ := (ConZonotope.aux_constraint_plus C₁ C₂ β).mp hA
    exact ⟨C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j,
      ⟨fun j => β (Fin.castAdd C₂.h j), fun j => hβ _, hA₁, rfl⟩,
      C₂.c + ∑ j, β (Fin.natAdd C₁.h j) • C₂.G j,
      ⟨fun j => β (Fin.natAdd C₁.h j), fun j => hβ _, hA₂, rfl⟩,
      (ConZonotope.aux_value_plus' C₁ C₂ β).symm⟩

end CORALean.Real

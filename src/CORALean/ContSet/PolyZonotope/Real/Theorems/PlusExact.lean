import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `PolyZonotope.plus` is exactly the Minkowski sum

The witnesses are `Fin.append a₁ a₂` and `Fin.append β₁ β₂` on the factors and
the independent coefficients, and the block-diagonal exponent matrix is what
makes them work: a generator of one set carries exponent zero on every factor of
the other, so its monomial reads back as a monomial of its own set alone.

Exactness is the point of separating the factors. Had the two sets' factors been
identified, the reverse inclusion would fail — one factor cannot take two values
at once, so the sum would come out too small rather than too large.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_plus_h {PZ₁ PZ₂ : PolyZonotope α}
    (f : Fin (PZ₁.h + PZ₂.h) → α) :
    ∑ i : Fin (PZ₁.plus PZ₂).h, f i
      = ∑ i, f (Fin.castAdd PZ₂.h i) + ∑ i, f (Fin.natAdd PZ₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_plus_q {PZ₁ PZ₂ : PolyZonotope α}
    (f : Fin (PZ₁.q + PZ₂.q) → α) :
    ∑ j : Fin (PZ₁.plus PZ₂).q, f j
      = ∑ j, f (Fin.castAdd PZ₂.q j) + ∑ j, f (Fin.natAdd PZ₁.q j) :=
  Fin.sum_univ_add f

theorem PolyZonotope.plus_exact (PZ₁ PZ₂ : PolyZonotope α) :
    PZ₁.construct + PZ₂.construct = (PZ₁.plus PZ₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨a₁, β₁, ha₁, hβ₁, rfl⟩, x₂, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩, rfl⟩
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j), ?_⟩
    rw [PolyZonotope.aux_sum_univ_plus_h, PolyZonotope.aux_sum_univ_plus_q]
    simp only [PolyZonotope.plus, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    abel
  -- back: the appended data split again, giving one point of each set
  · rintro x ⟨a, β, ha, hβ, rfl⟩
    refine ⟨PZ₁.c + ∑ i, PolyZonotope.monomial PZ₁.E (fun k => a (Fin.castAdd PZ₂.p k)) i
              • PZ₁.G i + ∑ j, β (Fin.castAdd PZ₂.q j) • PZ₁.GI j,
            ⟨fun k => a (Fin.castAdd PZ₂.p k), fun j => β (Fin.castAdd PZ₂.q j),
              fun k => ha _, fun j => hβ _, rfl⟩,
            PZ₂.c + ∑ i, PolyZonotope.monomial PZ₂.E (fun k => a (Fin.natAdd PZ₁.p k)) i
              • PZ₂.G i + ∑ j, β (Fin.natAdd PZ₁.q j) • PZ₂.GI j,
            ⟨fun k => a (Fin.natAdd PZ₁.p k), fun j => β (Fin.natAdd PZ₁.q j),
              fun k => ha _, fun j => hβ _, rfl⟩, ?_⟩
    rw [PolyZonotope.aux_sum_univ_plus_h, PolyZonotope.aux_sum_univ_plus_q]
    simp only [PolyZonotope.plus, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real

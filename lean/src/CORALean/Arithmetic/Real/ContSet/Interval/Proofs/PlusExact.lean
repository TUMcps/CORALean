import CORALean.Arithmetic.Real.ContSet.Interval.API

/-!
# `Interval.plus` is exactly the Minkowski sum

Coordinatewise. Splitting a point of the sum is the only work: `I₁` takes
`min (I₁.sup i) (x i - I₂.inf i)`, and the bounds leave a remainder `I₂` holds.

Both boxes must be `IsNonempty`: `[1, 0] + [0, 10]` is `∅` as a set but `[1, 10]`
by the definition.

`plus_outer` is what the float layer composes with.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   17-August-2026 (exactness)
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Interval.Proofs

open Pointwise

variable {n : ℕ}

theorem plus_outer (I₁ I₂ : Interval n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct := by
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ i
  exact ⟨add_le_add (hx₁ i).1 (hx₂ i).1, add_le_add (hx₁ i).2 (hx₂ i).2⟩

theorem plus_exact (I₁ I₂ : Interval n) (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    I₁.construct + I₂.construct = (I₁.plus I₂).construct := by
  refine Set.eq_of_subset_of_subset (plus_outer I₁ I₂) fun x hx => ?_
  have hlo : ∀ i, I₁.inf i + I₂.inf i ≤ x i := fun i => (hx i).1
  have hhi : ∀ i, x i ≤ I₁.sup i + I₂.sup i := fun i => (hx i).2
  refine ⟨fun i => min (I₁.sup i) (x i - I₂.inf i), fun i => ⟨?_, ?_⟩,
          fun i => x i - min (I₁.sup i) (x i - I₂.inf i), fun i => ⟨?_, ?_⟩, ?_⟩
  · exact le_min (h₁ i) (by linarith [hlo i])
  · exact min_le_left _ _
  · linarith [min_le_right (I₁.sup i) (x i - I₂.inf i)]
  · have : x i - I₂.sup i ≤ min (I₁.sup i) (x i - I₂.inf i) :=
      le_min (by linarith [hhi i]) (by linarith [h₂ i])
    linarith
  · funext i
    show min (I₁.sup i) (x i - I₂.inf i) + (x i - min (I₁.sup i) (x i - I₂.inf i)) = x i
    ring

end CORALean.Arithmetic.Real.Interval.Proofs

import CORALean.Arithmetic.Real.ContSet.Interval.API

/-!
# `Interval.plus` is exactly the Minkowski sum

Coordinatewise in both directions. Splitting a point of the sum is the only work:
`I₁` takes as much of it as it can hold, `min (I₁.sup i) (x i - I₂.inf i)`, and
the bounds leave a remainder `I₂` contains.

Both boxes must be nonempty. `[1, 0]` denotes `∅`, so `[1, 0] + [0, 10]` is `∅`
as a set while `plus` gives `[1, 10]` — the sum interval forgets which side was
empty. Every other operation ignores emptiness because over-approximation is
vacuous there; only exactness sees it.

`plus_outer` is the inclusion the float layer composes with.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   17-August-2026 (exactness)
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Interval.Proofs

open Pointwise

variable {n : ℕ}

/-- Nonemptiness as the bound the splitting needs. -/
theorem inf_le_sup {I : Interval n} (h : I.construct.Nonempty) (i : Fin n) :
    I.inf i ≤ I.sup i :=
  let ⟨_, hx⟩ := h
  le_trans (hx i).1 (hx i).2

theorem plus_outer (I₁ I₂ : Interval n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct := by
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ i
  exact ⟨add_le_add (hx₁ i).1 (hx₂ i).1, add_le_add (hx₁ i).2 (hx₂ i).2⟩

theorem plus_exact (I₁ I₂ : Interval n) (h₁ : I₁.construct.Nonempty)
    (h₂ : I₂.construct.Nonempty) :
    I₁.construct + I₂.construct = (I₁.plus I₂).construct := by
  refine Set.eq_of_subset_of_subset (plus_outer I₁ I₂) fun x hx => ?_
  have hlo : ∀ i, I₁.inf i + I₂.inf i ≤ x i := fun i => (hx i).1
  have hhi : ∀ i, x i ≤ I₁.sup i + I₂.sup i := fun i => (hx i).2
  refine ⟨fun i => min (I₁.sup i) (x i - I₂.inf i), fun i => ⟨?_, ?_⟩,
          fun i => x i - min (I₁.sup i) (x i - I₂.inf i), fun i => ⟨?_, ?_⟩, ?_⟩
  · exact le_min (inf_le_sup h₁ i) (by linarith [hlo i])
  · exact min_le_left _ _
  · linarith [min_le_right (I₁.sup i) (x i - I₂.inf i)]
  · have : x i - I₂.sup i ≤ min (I₁.sup i) (x i - I₂.inf i) :=
      le_min (by linarith [hhi i]) (by linarith [inf_le_sup h₂ i])
    linarith
  · funext i
    show min (I₁.sup i) (x i - I₂.inf i) + (x i - min (I₁.sup i) (x i - I₂.inf i)) = x i
    ring

end CORALean.Arithmetic.Real.Interval.Proofs

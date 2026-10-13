import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox

/-!
# The intersection of two polynomial zonotopes

[1, Prop. 2]: `PZ₁ ∩ PZ₂` is `PZ₁` with its factors restricted by the equality constraint
`c(α) = 0`, `c` the difference of the two polynomials in the stacked factors `α`, the second
set's own factors appended after the first's. [1, Def. 2]'s sets have no independent block,
`q = 0` here, and the stacked factor vector is the pair `(a, b)`. Exact, both ways.

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `PZ₁ ∩ PZ₂ = {PZ₁(a) | a, b ∈ [-1, 1], PZ₁(a) - PZ₂(b) = 0}`. -/
theorem PolyZonotope.construct_inter_construct (pZ₁ pZ₂ : PolyZonotope α) (h₁ : pZ₁.q = 0)
    (h₂ : pZ₂.q = 0) :
    pZ₁.construct ∩ pZ₂.construct = {x | ∃ a b, (∀ k, |a k| ≤ 1) ∧ (∀ k, |b k| ≤ 1) ∧
      pZ₁.point a - pZ₂.point b = 0 ∧ x = pZ₁.point a} := by -- --- PROOF ---
  rw [← pZ₁.subsetAt_unitBox h₁, ← pZ₂.subsetAt_unitBox h₂]
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    exact ⟨a, b, ha, hb, by rw [hab, sub_self], rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, (sub_eq_zero.mp hab).symm⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

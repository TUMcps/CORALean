import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# A point at admissible factors is a member

`construct` is the image of `point` widened by the independent block, so the
inclusion one way is free: read the independent coefficients as zero, which is
admissible whatever `q` is, and `point pZ a` is a member of `construct pZ`.

`mul_exact` does without this, `mul` setting `q := 0` so that the result's
`construct` *is* the image of its dependent part alone. The moment a product is
chained back into a propagation it is the first thing wanted, since `mul` is
stated against `point` and every enclosure downstream is stated against
`construct`.

The converse fails as an equality: a set with a non-empty independent block has
members no factor vector reaches.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- At factors in `[-1,1]`, the point the dependent part picks out is a member
of the set. -/
theorem PolyZonotope.point_mem_construct (pZ : PolyZonotope α) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) : pZ.point a ∈ pZ.construct := by
  refine ⟨a, fun _ => 0, ha, fun _ => by rw [abs_zero]; exact zero_le_one, ?_⟩
  -- the independent block contributes nothing at zero coefficients
  simp only [PolyZonotope.point, zero_smul, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

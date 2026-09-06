import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# With no independent block, every member is a point

`point_mem_construct` read backwards, and only available under the hypothesis:
`construct` is the image of `point` *widened* by the independent block, so a
member is a point exactly when that block is empty. `dependent` is what empties
it without moving the set, and `mul` produces sets that are already empty there.

Stated at `q = 0` rather than at `dependent` because both callers need it and
neither has a `dependent` in hand: the exact layer's activation layer holds
`S.dependent`, whose `q` is `0` by definition, and the float layer holds the
*nominal* of one, which is a different construction with the same empty block.

This is what `evalPoly` asks of a caller in place of a `dependent` wrapper. One
wrapper per set would give unrelated free coefficients the same fresh factor
indices; running `dependent` once, on the base set, is the discipline, and this
theorem is what turns it into a usable factor vector.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.exists_point_of_q_zero (S : PolyZonotope α) (hq : S.q = 0) {x : α}
    (hx :
      x ∈ S.construct) : ∃ a : Fin S.p → ℝ, (∀ k, |a k| ≤ 1) ∧ x = S.point a := by -- --- PROOF ---
  obtain ⟨a, β, ha, -, rfl⟩ := hx
  have hempty : IsEmpty (Fin S.q) := by rw [hq]; infer_instance
  refine ⟨a, ha, ?_⟩
  -- what is left once the independent sum drops out is exactly `point`
  show S.c + (∑ i, PolyZonotope.monomial S.E a i • S.G i) + ∑ j, β j • S.GI j
      = S.c + ∑ i, PolyZonotope.monomial S.E a i • S.G i
  rw [Finset.sum_eq_zero fun j (_ : j ∈ Finset.univ) => (hempty.false j).elim, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

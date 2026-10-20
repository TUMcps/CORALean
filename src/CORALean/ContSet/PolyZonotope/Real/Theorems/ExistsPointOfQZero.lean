module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# With no independent block, every member is a point

`point_mem_construct` read backwards, and only available under the hypothesis: `construct` is
the image of `point` *widened* by the independent block, so a member is a point exactly when
that block is empty. `dependent` empties it without moving the set, and `mul` produces sets
already empty there. Stated at `q = 0` rather than at `dependent` because both callers need
it and neither has a `dependent` in hand. This is what `evalPoly` asks of a caller: running
`dependent` once, on the base set, is the discipline, and this turns it into a factor vector.

## Inputs
* `pZ` – polynomial zonotope
* `x` – element of the set

## Hypotheses
* `hq` – no independent generators
* `hx` – element lies in the set

## Conclusion
* the element is a point for some factor values
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.exists_point_of_q_zero (pZ : PolyZonotope α) (hq : pZ.q = 0) {x : α}
    (hx : x ∈ pZ.construct) : -- --- CONCL ---
    ∃ a : Fin pZ.p → ℝ, (∀ k, |a k| ≤ 1) ∧ x = pZ.point a := by -- --- PROOF ---
  obtain ⟨a, β, ha, -, rfl⟩ := hx
  have hempty : IsEmpty (Fin pZ.q) := by rw [hq]; infer_instance
  refine ⟨a, ha, ?_⟩
  -- what is left once the independent sum drops out is exactly `point`
  show pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, β j • pZ.GI j
      = pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
  rw [Finset.sum_eq_zero fun j (_ : j ∈ Finset.univ) => (hempty.false j).elim, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

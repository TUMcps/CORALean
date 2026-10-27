module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# The boundary of a box is the union of its faces

[1, Eq. 7]: `∂[l, u] = ⋃ᵢ ⋃ⱼ Iᵢⱼ`, `Iᵢ₁ = {x ∈ [l, u] | x(i) = u(i)}`, `Iᵢ₂` with `l(i)`. In the
product topology the interior of the box is the product of the open intervals, so a point of
the box is on its frontier exactly when some coordinate sits at a bound. No `l ≤ u` is needed:
a box with `l(i) > u(i)` is empty and so are its faces, and a flat one is its own frontier.

## Inputs
* `l` – lower corner of the box
* `u` – upper corner of the box

## Hypotheses
* none

## Conclusion
* the frontier of the box is the union of its faces

## References

* [1] [N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../references/2020/kochdumper-cdc-nonconvex-inner.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7]: the frontier of `[l, u] ⊂ ℝⁿ` is the union of its `2n` faces. -/
theorem frontier_Icc_eq_iUnion_faces (l u : Fin n → ℝ) : -- --- CONCL ---
    frontier (Icc l u) =
      ⋃ i, ({x | x ∈ Icc l u ∧ x i = u i} ∪ {x | x ∈ Icc l u ∧ x i = l i}) := by -- --- PROOF ---
  have hbox : Icc l u = pi univ fun i => Icc (l i) (u i) := (pi_univ_Icc l u).symm
  have hint : interior (Icc l u) = pi univ fun i => Ioo (l i) (u i) := by
    rw [hbox, interior_pi_set finite_univ]
    simp only [interior_Icc]
  rw [frontier, isClosed_Icc.closure_eq, hint]
  ext x
  simp only [mem_sdiff, mem_pi, mem_univ, forall_const, mem_Ioo, mem_iUnion, mem_union,
    mem_setOf_eq, not_forall]
  constructor
  · rintro ⟨hx, i, hi⟩
    -- a coordinate not strictly inside its bounds sits on one of them
    refine ⟨i, ?_⟩
    have h1 := hx.1 i
    have h2 := hx.2 i
    rcases (not_and_or.mp hi) with h | h
    · exact Or.inr ⟨hx, le_antisymm (not_lt.mp h) h1⟩
    · exact Or.inl ⟨hx, le_antisymm h2 (not_lt.mp h)⟩
  · rintro ⟨i, ⟨hx, hi⟩ | ⟨hx, hi⟩⟩
    · exact ⟨hx, i, fun h => h.2.ne hi⟩
    · exact ⟨hx, i, fun h => h.1.ne' hi⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

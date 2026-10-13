module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup

@[expose] public section

/-!
# A group merge pays no more width than the pairwise merges it replaces

What issue #72 asks of a group merge: does bounding the group's errors together
beat accumulating them pairwise? At the width it does. `eDiff` obeys the
triangle inequality — two exponents of unequal parity are `2` apart, and
whatever lies between them differs in parity from one of the two — so the
direct width from a member to the target is at most the total of any chain of
steps between them, and a run of pairwise merges is such a chain: a merge
copies exponent columns, so every intermediate column is a column of `pZ.E`.

The saving is per member and per member only: this weighs the widths two
schemes pay on one generator, not the sets they produce. A chain pays its later
widths on the partial *sums* it has already built, where a group merge pays
each member alone, and `relaxExpGroup_not_always_tighter` is where that leaves
the group merge enclosing strictly more.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `eDiff` obeys the triangle inequality, parity being what carries it at `2`. -/
theorem PolyZonotope.aux_eDiff_triangle (a b c : ℕ) :
    PolyZonotope.eDiff a c ≤ PolyZonotope.eDiff a b + PolyZonotope.eDiff b c := by
  simp only [PolyZonotope.eDiff]
  split_ifs <;> omega

/-- Along a chain: a walk from `f 0` to `f n` never costs less than the step
straight across. -/
theorem PolyZonotope.aux_eDiff_chain (f : ℕ → ℕ) (n : ℕ) :
    PolyZonotope.eDiff (f 0) (f n)
      ≤ ∑ s ∈ Finset.range n, PolyZonotope.eDiff (f s) (f (s + 1)) := by -- --- PROOF ---
  induction n with
  | zero => simp [PolyZonotope.eDiff]
  -- one more step of the walk, and the triangle inequality closes it up
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (PolyZonotope.aux_eDiff_triangle (f 0) (f n) (f (n + 1)))
      (Nat.add_le_add_right ih _)


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
/-- The width a group merge pays on one member is at most the total paid by any
chain of merges carrying that member's column to the target's. -/
theorem PolyZonotope.relaxWidthGroup_le_chain (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin k)) (t : Fin d) (l : Fin k)
    (n : ℕ) (c : ℕ → Fin pZ.h) (hfst : c 0 = part.right l) (hlst : c n = part.left t) :
    pZ.relaxWidthGroup part t l
      ≤ ∑ s ∈ Finset.range n, ∑ i, PolyZonotope.eDiff (pZ.E i (c s)) (pZ.E i (c (s + 1))) := by
  rw [PolyZonotope.relaxWidthGroup, ← hfst, ← hlst, Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ => PolyZonotope.aux_eDiff_chain (fun s => pZ.E i (c s)) n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

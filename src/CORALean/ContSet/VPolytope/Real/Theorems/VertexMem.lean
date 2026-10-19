module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# Every vertex is a point of the polytope

The combination weighted entirely onto one vertex. Trivial as a statement and
not as a proof: `construct` quantifies over coefficient families, so the witness
has to be built and its sum computed, which is three rewrites through
`Finset.sum_ite_eq'`.

What the convex-hull characterisation and `linComb`'s enclosure both start from.

## Inputs
* `P` – polytope
* `j` – vertex index

## Hypotheses
* none

## Conclusion
* vertex `j` lies in `P`
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.vertex_mem (P : VPolytope α) (j : Fin P.k) :
    P.V j ∈ P.construct := by -- --- PROOF ---
  have hnn : ∀ l : Fin P.k, 0 ≤ (if l = j then (1:ℝ) else 0) := by
    intro l; split <;> [exact zero_le_one; exact le_rfl]
  have hsum : ∑ l : Fin P.k, (if l = j then (1:ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ j fun _ => (1:ℝ), if_pos (Finset.mem_univ j)]
  -- the indicator passes the scalar action before the sum is collapsed
  have hsmul : ∀ l : Fin P.k, (if l = j then (1:ℝ) else 0) • P.V l
      = if l = j then P.V l else 0 := by
    intro l; split <;> [rw [one_smul]; rw [zero_smul]]
  have hval : ∑ l, (if l = j then (1:ℝ) else 0) • P.V l = P.V j := by
    rw [Finset.sum_congr rfl fun l _ => hsmul l, Finset.sum_ite_eq' Finset.univ j P.V,
      if_pos (Finset.mem_univ j)]
  exact ⟨fun l => if l = j then 1 else 0, hnn, hsum, hval.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

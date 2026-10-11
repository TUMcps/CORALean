import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpMultiOuter

/-!
# The greedy relaxation of `Alg. 2` over-approximates

`[1, Thm. 2]`: `relax(PZ, η) ⊇ PZ`. Each merge of `Alg. 2` is `relaxExpMulti`, which
over-approximates whichever pair it merges (`relaxExpMulti_outer`), so the greedy subgraph, the
leaf and the tie-break decide precision and nothing else, and the loop encloses at every `fuel`.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `[1, Alg. 2]` returns a set containing `PZ`. -/
theorem PolyZonotope.relaxGreedy_outer (η : ℕ) (fuel : ℕ) (PZ : PolyZonotope α) :
    PZ.construct ⊆ (PolyZonotope.relaxGreedy η fuel PZ).construct := by -- --- PROOF ---
  induction fuel generalizing PZ with
  | zero => exact Set.Subset.rfl
  | succ fuel ih =>
    unfold PolyZonotope.relaxGreedy
    dsimp only
    -- the leaf search either stops the loop or names a merge, which encloses
    split
    · exact Set.Subset.rfl
    · split
      · exact Set.Subset.trans (PZ.relaxExpMulti_outer _) (ih _)
      · exact Set.Subset.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

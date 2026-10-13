module

public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# An interval is full-dimensional iff no coordinate is degenerate

The box is a product of its coordinate intervals, whose interior is the product of the open
intervals; that is nonempty exactly when every one is. A crossed box is `∅`, so a crossed
coordinate fails the right-hand side too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Set

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isFullDim_iff (I : Interval (Vec ℝ n)) :
    ContSet.IsFullDim I ↔ ∀ i, I.inf i < I.sup i := by -- --- PROOF ---
  have hc : construct I = Icc I.inf I.sup := by
    ext x
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  have hi : interior (construct I) = Set.pi univ fun i => Ioo (I.inf i) (I.sup i) := by
    rw [hc, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
    exact congrArg _ (funext fun i => interior_Icc)
  change (interior (construct I)).Nonempty ↔ _
  rw [hi, Set.univ_pi_nonempty_iff]
  exact forall_congr' fun i => Set.nonempty_Ioo

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

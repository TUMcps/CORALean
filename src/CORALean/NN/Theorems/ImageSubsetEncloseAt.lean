module

public import CORALean.NN.Definitions.RefinableNetworkImage
public import CORALean.NN.Theorems.EncloseAtOuter

@[expose] public section

/-!
# A schedule's propagation encloses the image

Split out of `EncloseAtOuter.lean` (issue #62): all five declarations there
were genuinely public — none used outside the file, and no single one is the
file's whole point over the others — so split one file each, as CORA gives
each of the refinement rules a place too.

The set-level reading of `encloseAt_outer`: the image of every point.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.image_subset_encloseAt (rn : RefinableNetwork S n m)
    (sch : Schedule) (X : S n) : rn.image (construct X) ⊆ construct (rn.encloseAt sch X) := by
  rintro _ ⟨x, hx, rfl⟩
  exact rn.encloseAt_outer sch X x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

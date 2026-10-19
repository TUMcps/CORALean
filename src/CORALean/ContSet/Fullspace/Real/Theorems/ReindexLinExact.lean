module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# Relabelling the full space gives the full space

`reindexLin e` reads a vector's coordinates through `e`, and `e` is an
equivalence, so `y ∘ e.symm` is a preimage of any `y`: nothing is missed and
the image is again everything. An equality, which is what `Reindex` asks for —
the one class in this tree whose obligation is not an inclusion.

## Inputs
* `e` – coordinate relabelling
* `F` – full space

## Hypotheses
* none

## Conclusion
* the full space is the image of the full space under relabelling
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.reindexLin_exact (e : Fin m ≃ Fin n) (F : Fullspace n) :
    (Fullspace.mk : Fullspace m).construct = reindexLin e '' F.construct := by
  ext y
  simp only [Fullspace.construct, Set.image_univ, Set.mem_range, Set.mem_univ, true_iff]
  exact ⟨fun j => y (e.symm j), funext fun i => by simp [reindexLin]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

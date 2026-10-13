module

public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell

@[expose] public section

/-!
# `potInt`'s scan over level-set guards, as CORA runs it

CORA's `@location/potInt.m` loops over the guards `i` and the reach sets `j` and lists `(i, j)`
when `isIntersecting_(guardSet,Rset{j},'approx',1e-8)`. Here each guard is a level set, so the
test is `LevelSet.isIntersecting_cell` at tolerance `1e-8` on the bounds `B guardSet j` of the
guard function over set `j` (assumed a range bound, as there). The list is the set of listed
index pairs, 0-based. Not modelled: the skip of transitions into `finalLoc`, and the final step
that swaps a lone hyperplane hit for the next time-point set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.potIntCora (guards : List (LevelSet n)) (nSets : ℕ)
    (B : (g : LevelSet n) → ℕ → Fin g.m → ℝ × ℝ) : Set (ℕ × ℕ) :=
  {p | ∃ i : p.1 < guards.length,
    let guardSet := guards[p.1]
    p.2 < nSets ∧ LevelSet.isIntersecting_cell (1 / 10 ^ 8) guardSet.op (B guardSet p.2)}


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

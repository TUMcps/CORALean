module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.And
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

@[expose] public section

/-!
# `ContSet/PolyLevelSet/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `PolyLevelSet.andRows`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `and_`'s rows on the first operand's box, as over ℝ (`Real.PolyLevelSet.andRows`): further rows
on the same variables, each with its slack. -/
def PolyLevelSet.andRows (P Q : PolyLevelSet 𝕋 n) : PolyLevelSet 𝕋 n :=
  { P.and_ Q with dom := P.dom }


-- =================================  `PolyLevelSet.mergedCol`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- The merged coefficient column as stored, rounded down, `A`'s rows read as a generator matrix. -/
def PolyLevelSet.mergedCol (P : PolyLevelSet 𝕋 n) (i : Fin P.m)
    (l : Fin (PolyZonotope.repKeep P.R).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep P.R) P.A i (PolyZonotope.keepIdx P.R l)


-- ================================  `PolyLevelSet.mergedColUp`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- The merged coefficient column rounded up, the other side of `mergedCol`. -/
def PolyLevelSet.mergedColUp (P : PolyLevelSet 𝕋 n) (i : Fin P.m)
    (l : Fin (PolyZonotope.repKeep P.R).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep P.R) P.A i (PolyZonotope.keepIdx P.R l)


-- ================================  `PolyLevelSet.compactGap`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- What a merged coefficient column can be off by. -/
def PolyLevelSet.compactGap (P : PolyLevelSet 𝕋 n) : Mat 𝕋 P.m (PolyZonotope.repKeep P.R).card :=
  fun i l => subUp (P.mergedColUp i l) (P.mergedCol i l)


-- ===============================  `PolyLevelSet.compactSlack`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- The slack widened by what a merged row can be off by: one `radius` of the row's gaps, every
monomial being in `[-1,1]` on the unit box. -/
def PolyLevelSet.compactSlack (P : PolyLevelSet 𝕋 n) : Vec 𝕋 P.m :=
  fun i => addUp (absolute (P.b_error i)) (radius P.compactGap i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

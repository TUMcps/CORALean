import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.Zonotope.Float.Operations.PairDiff
import CORALean.ContSet.Zonotope.Float.Operations.PairSum

/-!
# `linComb`'s independent block, at one rounding

Split out of `LinComb.lean` (issue #62): read again by `linCombGIDiff` in this
directory and by `Theorems/LinCombOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The independent block at one rounding: CORA's `zonotope/enclose` on the two
independent blocks, which is the exact layer's pairing at a zero centre. -/
def PolyZonotope.linCombGI (add sub : 𝕋 → 𝕋 → 𝕋) (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n (PZ₁.q + PZ₂.q) :=
  fun i => Fin.append (Zonotope.pairSum add (PZ₁.GI i) (PZ₂.GI i))
    (Zonotope.pairDiff sub (PZ₁.GI i) (PZ₂.GI i))

end CORALean.Float

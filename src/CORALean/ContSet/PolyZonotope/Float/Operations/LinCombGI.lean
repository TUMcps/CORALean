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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The independent block at one rounding: CORA's `zonotope/enclose` on the two
independent blocks, which is the exact layer's pairing at a zero centre. -/
def PolyZonotope.linCombGI (add sub : 𝕋 → 𝕋 → 𝕋) (pZ₁ pZ₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n (pZ₁.q + pZ₂.q) :=
  fun i => Fin.append (Zonotope.pairSum add (fun j => pZ₁.GI j i) (fun j => pZ₂.GI j i))
    (Zonotope.pairDiff sub (fun j => pZ₁.GI j i) (fun j => pZ₂.GI j i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

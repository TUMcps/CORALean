import CORALean.ContSet.Zonotope.Float.Operations.LongestGen
import CORALean.ContSet.Zonotope.Float.Operations.Split

/-!
# `Zonotope.splitLongestGen`, over a floating-point scalar

CORA's `splitLongestGen`: `split` at the generator `longestGen` picks. A zonotope with no
generator is its own two halves.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along its longest generator. -/
def Zonotope.splitLongestGen (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) :=
  match Z.longestGen with
  | some j => Z.split j
  | none => (Z, Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

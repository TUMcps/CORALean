import CORALean.ContSet.Zonotope.Float.Operations.CubMapDep
import CORALean.ContSet.Zonotope.Float.Operations.Dependent

/-!
# `Zonotope.cubMap`, over a floating-point scalar

CORA's `@zonotope/cubMap`: an enclosure of `{ (xᵀ T x) * x | x ∈ Z }`, `zᵢ = Σₖ xₖ (xᵀ T{i,k} x)`,
by a zonotope. The box is made into generators first (`dependent`), then `cubMapDep`. The factors
of a zonotope are free in `[-1, 1]`, so the products `β_k β_j β_c` are enclosed rather than
tracked, which is why the result is an outer enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMap (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 m) :=
  Zonotope.cubMapDep T Z.dependent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.cartProdVec`, over a floating-point scalar

CORA's `@ellipsoid/cartProd_.m` with a point operand, which is exact: the centre extended by the
point, the generators by zero rows and the error box by the origin. Nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.cartProdVec (E : Ellipsoid 𝕋 n) (v : Vec 𝕋 m) : Ellipsoid 𝕋 (n + m) where
  k := E.k
  q := Fin.append E.q v
  G := fun i j => Fin.addCases (fun i => E.G i j) (fun _ => zero) i
  err := ⟨Fin.append E.err.inf fun _ => zero, Fin.append E.err.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

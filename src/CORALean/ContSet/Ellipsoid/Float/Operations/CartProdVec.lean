module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.cartProdVec`, over a floating-point scalar

CORA's `@ellipsoid/cartProd_.m` with a point operand, which is exact: `blkdiag(E.Q, zeros(m))`,
the center extended by the point and the error box by the origin. Nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.cartProdVec (E : Ellipsoid 𝕋 n) (v : Vec 𝕋 m) : Ellipsoid 𝕋 (n + m) where
  Q := fun i j => Fin.addCases (fun i => Fin.addCases (fun j => E.Q i j) (fun _ => zero) j)
    (fun _ => zero) i
  q := Fin.append E.q v
  I_error := ⟨Fin.append E.I_error.inf fun _ => zero, Fin.append E.I_error.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

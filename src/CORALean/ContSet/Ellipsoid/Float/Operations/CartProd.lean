import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid

/-!
# `Ellipsoid.cartProd`, over a floating-point scalar

CORA's `@ellipsoid/cartProd_.m` in its one supported mode, `'outer'`: the ellipsoid of the product
of the two bounding boxes, `ellipsoid(cartProd_(interval(E), interval(S), 'exact'))`. The two square
roots the conversions need are certificates the caller proposes, one length per coordinate for each
box (`s₁`, `s₂`) and the factor `σ` for the product (`n + m ≤ σ·σ`), as in the conversions.
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

def Ellipsoid.cartProd (E₁ : Ellipsoid 𝕋 n) (E₂ : Ellipsoid 𝕋 m) (s₁ : Vec 𝕋 n) (s₂ : Vec 𝕋 m)
    (σ : 𝕋) : Ellipsoid 𝕋 (n + m) :=
  let I₁ := E₁.interval s₁
  let I₂ := E₂.interval s₂
  Interval.ellipsoid ⟨Fin.append I₁.inf I₂.inf, Fin.append I₁.sup I₂.sup⟩ σ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

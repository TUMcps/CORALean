module

public import CORALean.ContSet.Taylm.Float.Operations.PowBounds
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Taylm.prodBounds`, over a floating-point scalar

The range of a product of factors each known to lie in an interval: the corner products of the
running interval with the next factor's, rounded outward (`Interval.mulLo`, `Interval.mulHi`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prodBounds : {m : ℕ} → (Fin m → 𝕋 × 𝕋) → 𝕋 × 𝕋
  | 0, _ => (one, one)
  | _ + 1, f =>
    let rest := Taylm.prodBounds fun i => f i.succ
    (Interval.mulLo (f 0).1 (f 0).2 rest.1 rest.2, Interval.mulHi (f 0).1 (f 0).2 rest.1 rest.2)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

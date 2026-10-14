module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.Reexpand

@[expose] public section

/-!
# `Taylm.reexpBoxBounds`, over a floating-point scalar

The range of a term list over a box after re-expanding it at the box's midpoint, so that the box
becomes `[-1, 1]ⁿ`: the float `Taylm.reexpand`'s bounds. The re-expansion needs `|m| + |r| ≤ 1` in
every coordinate, which `le` certifies; where it does not, the range is `polyBoxBounds`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpBoxBounds (P : List (𝕋 × (Fin n → ℕ))) (B : Fin n → Interval 𝕋) : Interval 𝕋 :=
  let m := Taylm.boxMid B
  let r := Taylm.boxRad B
  if (List.finRange n).all (fun k => le (addUp (absolute (m k)) (absolute (r k))) one) = true then
    (Taylm.reexpand m r ⟨P, zero, zero, 0⟩).bounds
  else Taylm.polyBoxBounds P B
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

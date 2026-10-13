module

public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The coefficients of `1/x` at the centre, from both sides

The Taylor coefficient `(-1)ᵏ c⁻⁽ᵏ⁺¹⁾` of `x ↦ 1/x` at `c`, between `1/|c|` rounded each way and
raised to `k + 1` by the directed powers. The sign is read off only where `ltStrict` certifies it;
an uncertified sign gives the symmetric interval, which holds either.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.invCoef (c : 𝕋) (k : ℕ) : 𝕋 × 𝕋 :=
  let s := maximum c (neg c)
  -- `1 / |c|` between its roundings, to the power `k + 1`
  let wl := maximum zero (divDown one s)
  let wh := divUp one s
  let pl := powDown wl (k + 1)
  let ph := powUp wh (k + 1)
  if ltStrict zero c = true then (if k % 2 = 0 then (pl, ph) else (neg ph, neg pl))
  else if ltStrict c zero = true then (neg ph, neg pl)
  else (neg ph, ph)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

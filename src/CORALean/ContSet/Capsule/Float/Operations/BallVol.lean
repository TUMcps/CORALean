module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.Global.Float.IntRound
public import CORALean.Global.Float.InverseTrig

@[expose] public section

/-!
# `Capsule.ballVol`, over a floating-point scalar

The volume `π^(k/2) / Γ(k/2 + 1)` of the unit `k`-ball, which CORA's `@capsule/volume_` evaluates
with Euler's gamma function, rounded up. No float has `Γ`: for an integer `k` the quotient obeys
`ω₀ = 1`, `ω₁ = 2` and `ω_{k+2} = 2π / (k + 2) · ωₖ`, each step run with outward rounding from an
upper bound of `2π`. A divisor not certified positive is replaced by `1`, which only raises the
quotient.

## Inputs
* `twoPi` – upper bound of `2π`

## Output
* upper bound of the volume of the unit `k`-ball
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.ballVol (twoPi : 𝕋) : ℕ → 𝕋
  | 0 => one
  | 1 => addUp one one
  | k + 2 =>
    -- `2π / (k + 2)`, rounded up
    let d : 𝕋 := intDown ((k : ℤ) + 2)
    mulUp (if ltStrict zero d then divUp twoPi d else twoPi) (Capsule.ballVol twoPi k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

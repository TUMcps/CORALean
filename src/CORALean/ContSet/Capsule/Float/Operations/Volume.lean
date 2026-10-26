module

public import CORALean.ContSet.Capsule.Float.Operations.BallVol
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Capsule.volume`, over a floating-point scalar

CORA's `@capsule/volume_`, `π^(n/2)/Γ(n/2+1) rⁿ + π^((n-1)/2)/Γ((n-1)/2+1) r^(n-1) · 2‖g‖`, in
floats with outward rounding: the ball volumes `Capsule.ballVol` from `π` rounded up (twice `acos
0`), the powers of the radius by `powUp`, the norm of the generator by `normUp`. A radius below
zero denotes the empty capsule, whose volume is `0`; it is clipped at `0`, which keeps the bound.
`0` at `n = 0`, as CORA. The stored numbers are read as the nominal capsule; the error box is not
part of `volume_`.

## Inputs
* `n` – dimension
* `p` – precision of acos
* `k` – Newton steps for the root
* `C` – capsule

## Output
* upper bound of the volume of the capsule
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.volume {n : ℕ} (p k : ℕ) (C : Capsule 𝕋 n) : 𝕋 :=
  if n = 0 then zero else
  -- `2π` from above, and the radius with a negative one cut to `0`
  let twoPi : 𝕋 := addUp (addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero))
    (addUp (acosUp p k zero) (acosUp p k zero))
  let r : 𝕋 := maximum zero C.r
  let volBall : 𝕋 := mulUp (Capsule.ballVol twoPi n) (powUp r n)
  let volBallMinus1 : 𝕋 := mulUp (Capsule.ballVol twoPi (n - 1)) (powUp r (n - 1))
  addUp volBall (mulUp volBallMinus1 (mulUp (addUp one one) (normUp k C.g)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

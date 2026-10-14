module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Cos
public import CORALean.ContSet.Interval.Float.Operations.Sin
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `Capsule.arcBox`: a box around one sampled boundary point

The sample `ctr + r (cos a, sin a)` of `a = a₀ + i * step`, with the centre `ctr` and the base
angle `a₀` known only in boxes and the step `π / 499` in bounds: the index `i` enclosed by
`intDown`, `intUp`, the angle by the interval plus and times, the cosine and sine by
`Interval.cos`, `Interval.sin`, the coordinates by the interval plus and times again.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.arcBox (p : ℕ) (step : Interval 𝕋) (ctr : Interval (Vec 𝕋 2)) (a₀ : Interval (Vec 𝕋 1))
    (r : 𝕋) (i : ℕ) : Interval (Vec 𝕋 2) :=
  -- the angle `a₀ + i * step`
  let idx : Interval (Vec 𝕋 1) := ⟨fun _ => intDown (i : ℤ), fun _ => intUp (i : ℤ)⟩
  let stp : Interval (Vec 𝕋 1) := ⟨fun _ => step.inf, fun _ => step.sup⟩
  let a := a₀.plus (idx.times stp)
  -- the two coordinates `ctr j + r * cos a` and `ctr j + r * sin a`
  let rad : Interval (Vec 𝕋 1) := Interval.point fun _ => r
  let x : Interval (Vec 𝕋 1) := (⟨fun _ => ctr.inf 0, fun _ => ctr.sup 0⟩ : Interval (Vec 𝕋 1)).plus
    (rad.times (a.cos p))
  let y : Interval (Vec 𝕋 1) := (⟨fun _ => ctr.inf 1, fun _ => ctr.sup 1⟩ : Interval (Vec 𝕋 1)).plus
    (rad.times (a.sin p))
  ⟨![x.inf 0, y.inf 0], ![x.sup 0, y.sup 0]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

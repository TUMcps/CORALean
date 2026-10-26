module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.Global.Float.IntRound
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.Operations.PiFloat
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# The periodic tail of `aux_sin_`, `aux_cos_` and `aux_tan_` over a float scalar

The tail of `syntaxTree.m` that finds the largest and the smallest solution `x + 2 pi k` inside
`intPrev` and meets `intPrev` with their hull, with the bounds held in `𝕋`. The index `k` is the
integer part of a quotient of the stored bounds, decoded exactly (`ToRat`): any integer would do,
because a bound is only used where the interval arithmetic certifies it, with `2 pi` and the shifted
copy `x + k·2 pi` rounded outward. Where no bound is certified the bound of `intPrev` stays.
Soundness is `SyntaxTree.periodicFloat_contains`.

## Inputs
* `p` – precision of `pi`
* `k` – Newton steps of `pi`
* `resTemp₁` – interval of the first branch
* `resTemp₂` – interval of the second branch
* `prev` – previous interval

## Output
* the interval of shifted branch solutions closest to the previous interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `R + m·(2 pi)`: the interval `R` shifted by `m` periods, rounded outward. -/
def SyntaxTree.aux_periodicFloat_shift (twoPi R : Float.SyntaxTree.Dom 𝕋) (m : ℤ) :
    Float.SyntaxTree.Dom 𝕋 :=
  Float.Interval.plus R (Float.Interval.times ⟨fun _ => intDown m, fun _ => intUp m⟩ twoPi)

/-- The upper bound a branch allows below `b`: the top of the last copy of `R` before the first
one certified to start above `b`, and `b` where none is. -/
def SyntaxTree.aux_periodicFloat_upper (twoPi R : Float.SyntaxTree.Dom 𝕋) (b : 𝕋) : 𝕋 :=
  let ind : ℤ := ⌈(ToRat.toRat b - ToRat.toRat (R.sup 0)) / ToRat.toRat (twoPi.inf 0)⌉
  if ltStrict b ((SyntaxTree.aux_periodicFloat_shift twoPi R ind).inf 0) = true then
    (SyntaxTree.aux_periodicFloat_shift twoPi R (ind - 1)).sup 0
  else b

/-- The lower bound a branch allows above `a`: the bottom of the first copy of `R` after the last
one certified to end below `a`, and `a` where none is. -/
def SyntaxTree.aux_periodicFloat_lower (twoPi R : Float.SyntaxTree.Dom 𝕋) (a : 𝕋) : 𝕋 :=
  let ind : ℤ := ⌊(ToRat.toRat a - ToRat.toRat (R.inf 0)) / ToRat.toRat (twoPi.inf 0)⌋
  if ltStrict ((SyntaxTree.aux_periodicFloat_shift twoPi R ind).sup 0) a = true then
    (SyntaxTree.aux_periodicFloat_shift twoPi R (ind + 1)).inf 0
  else a


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The solutions of the two inverse branches, shifted by `2 pi k`, closest to `intPrev`'s ends,
rounded outward. -/
def SyntaxTree.periodicFloat (p k : ℕ) (resTemp₁ resTemp₂ prev : Float.SyntaxTree.Dom 𝕋) :
    Float.SyntaxTree.Dom 𝕋 :=
  -- the period `2 pi`, rounded outward
  let piI := SyntaxTree.piFloat (𝕋 := 𝕋) p k
  let twoPi : Float.SyntaxTree.Dom 𝕋 :=
    ⟨fun _ => addDown piI.inf piI.inf, fun _ => addUp piI.sup piI.sup⟩
  -- compute updated upper bound
  let supNew := minimum (prev.sup 0)
    (maximum (SyntaxTree.aux_periodicFloat_upper twoPi resTemp₁ (prev.sup 0))
      (SyntaxTree.aux_periodicFloat_upper twoPi resTemp₂ (prev.sup 0)))
  -- compute updated lower bound
  let infNew := maximum (prev.inf 0)
    (minimum (SyntaxTree.aux_periodicFloat_lower twoPi resTemp₁ (prev.inf 0))
      (SyntaxTree.aux_periodicFloat_lower twoPi resTemp₂ (prev.inf 0)))
  ⟨fun _ => infNew, fun _ => supNew⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.Exp
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The bounds of a softmax's sums of exponentials

CORA.cpp's `aux_box_image` for a layer that sums the outputs of an exp layer: the exponentials of
`[l, u]` lie in the box `[e^l, e^u]`, whose image under `x ↦ W x + b` is the center's image
`c = W m + b` plus or minus `r = |W| ρ`, `m` and `ρ` the box's middle and radius. CORA.cpp widens
`r` by `w (|W| |m| + |b| + r)` (`w = (n + 4) eps`); the rounding of the middle and of the center's
image is paid on top, a difference of one value rounded two ways that is zero at round to nearest,
where this is CORA.cpp's order.

## Inputs
* `k` – the exponential's reduction depth
* `w` – the margin's factor (CORA.cpp's `(n + 4) eps`)
* `W` – the sum layer's weights
* `b` – the sum layer's bias
* `l` – the lower bounds of the exponentials' arguments
* `u` – the upper bounds of the exponentials' arguments

## Output
* the box of the sums
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The middle `(e^l + e^u) / 2` of the exponentials' box, rounded down. -/
@[step_of softmaxSumBounds]
def step_softmaxSumMid (k : ℕ) (l u : Vec 𝕋 n) : Vec 𝕋 n :=
  fun j => half (addDown (expDown k (l j)) (expUp k (u j)))

/-- The radius `(e^u - e^l) / 2` plus the middle's rounding, rounded up. -/
@[step_of softmaxSumBounds]
def step_softmaxSumRad (k : ℕ) (l u : Vec 𝕋 n) : Vec 𝕋 n := fun j =>
  let lo := expDown k (l j)
  let hi := expUp k (u j)
  addUp (half (subUp hi lo)) (half (subUp (addUp lo hi) (addDown lo hi)))

/-- The half-width `r + w (|W| |m| + |b| + r)` plus the center's rounding, `r = |W| ρ`. -/
@[step_of softmaxSumBounds]
def step_softmaxSumWidth (k : ℕ) (w : 𝕋) (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (l u : Vec 𝕋 n)
    (i : Fin m) : 𝕋 :=
  let mid := step_softmaxSumMid k l u
  let absW := fun j => absolute (W i j)
  let r := dotUp absW (step_softmaxSumRad k l u)
  let margin := mulUp (addUp (addUp (dotUp absW fun j => absolute (mid j)) (absolute (b i))) r) w
  let cost := subUp (addUp (dotUp (W i) mid) (b i)) (addDown (dotDown (W i) mid) (b i))
  addUp (addUp r margin) cost


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center's image `W m + b`, minus and plus the half-width. -/
def softmaxSumBounds (k : ℕ) (w : 𝕋) (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (l u : Vec 𝕋 n) :
    Interval (Vec 𝕋 m) :=
  let c := fun i => addDown (dotDown (W i) (step_softmaxSumMid k l u)) (b i)
  ⟨fun i => subDown (c i) (step_softmaxSumWidth k w W b l u i),
    fun i => addUp (c i) (step_softmaxSumWidth k w W b l u i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

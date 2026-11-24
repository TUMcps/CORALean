module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
public import CORALean.NN.Layers.Operations.RelaxationToPoly
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The quadratic ReLU fit of order 2

CORA's `computeApproxPoly` for a ReLU at `'singh'` and order 2, as CORA.cpp's `priv_approx_poly`:
where `l < 0 < u`, the parabola `a (x - l)²` through `(l, 0)` and `(u, u)`, stored as
`a = u/(u - l)²`, `b = -2 a l`, `c = a l l`. On each piece of `p - relu`, `[l, 0]` (`q = p`) and
`[0, u]` (`q = p - x`, `b - 1` kept between its roundings), the convex `q` lies below its larger
end value and above the smaller one, or above the closed-form vertex value `c - b²/(4a)` where the
vertex may lie in the piece. `c` moves by the band's middle `m`; the error is `max(hi - m, m - lo)`
plus the rounding of `c - m`, zero at nearest. A linear box has the line `0` or `x`; an `a` not
certified positive falls back to `reluRelaxation`'s line.

## Inputs
* none

## Output
* the coefficients, lowest first, and the error radius
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `(a x + b) x + c` from below, Horner's order, for every `b` in `[bd, bu]`. -/
@[step_of reluSinghQuadRelaxation]
def step_quadDown (a bd bu c x : 𝕋) : 𝕋 :=
  addDown (minimum (mulDown (addDown (mulDown a x) bd) x) (mulDown (addUp (mulUp a x) bu) x)) c

/-- `(a x + b) x + c` from above, for every `b` in `[bd, bu]`. -/
@[step_of reluSinghQuadRelaxation]
def step_quadUp (a bd bu c x : 𝕋) : 𝕋 :=
  addUp (maximum (mulUp (addDown (mulDown a x) bd) x) (mulUp (addUp (mulUp a x) bu) x)) c

/-- The vertex value `c - b²/(4a)` from below, for `a > 0` and every `b` in `[bd, bu]`. -/
@[step_of reluSinghQuadRelaxation]
def step_quadVertexDown (a bd bu c : 𝕋) : 𝕋 :=
  subDown c (half (half (divUp (maximum (mulUp bd bd) (mulUp bu bu)) a)))

/-- Whether the vertex `-b/(2a)` may lie in `[x₀, x₁]`: not certified below `x₀` nor above `x₁`. -/
@[step_of reluSinghQuadRelaxation]
def step_quadVertexIn (a bd bu x₀ x₁ : 𝕋) : Bool :=
  !(ltStrict (half (divUp (neg bd) a)) x₀ || ltStrict x₁ (half (divDown (neg bu) a)))

/-- The least and largest value of `a x² + b x + c` over `[x₀, x₁]`: the ends, and the vertex
value for the least where the vertex may lie in between. -/
@[step_of reluSinghQuadRelaxation]
def step_quadRange (a bd bu c x₀ x₁ : 𝕋) : 𝕋 × 𝕋 :=
  let lo := minimum (step_quadDown a bd bu c x₀) (step_quadDown a bd bu c x₁)
  let hi := maximum (step_quadUp a bd bu c x₀) (step_quadUp a bd bu c x₁)
  (if step_quadVertexIn a bd bu x₀ x₁ then minimum lo (step_quadVertexDown a bd bu c) else lo, hi)

/-- The parabola's stored coefficients `a = u / (u - l)²`, `b = -2 a l`, `c = a l l`. -/
@[step_of reluSinghQuadRelaxation]
def step_reluQuadCoeffs (l u : 𝕋) : 𝕋 × 𝕋 × 𝕋 :=
  let w := subUp u l
  let a := divUp u (mulUp w w)
  (a, mulUp (mulUp (neg (addUp one one)) a) l, mulUp (mulUp a l) l)

/-- The band of `p - relu`: the ranges of `p` on `[l, 0]` and of `p - x` on `[0, u]`. -/
@[step_of reluSinghQuadRelaxation]
def step_reluQuadBand (l u : 𝕋) : 𝕋 × 𝕋 :=
  let a := (step_reluQuadCoeffs l u).1
  let b := (step_reluQuadCoeffs l u).2.1
  let c := (step_reluQuadCoeffs l u).2.2
  let r₁ := step_quadRange a b b c l zero
  let r₂ := step_quadRange a (subDown b one) (subUp b one) c zero u
  (minimum r₁.1 r₂.1, maximum r₁.2 r₂.2)

/-- The band's middle `(hi + lo) / 2`. -/
@[step_of reluSinghQuadRelaxation]
def step_reluQuadMid (l u : 𝕋) : 𝕋 :=
  half (addUp (step_reluQuadBand l u).2 (step_reluQuadBand l u).1)

/-- The kind of box: `0` where ReLU is `0`, `1` where it is `x`, `2` for the parabola, `3` for
the fallback line; the fit has degree 2 in case `2` only. -/
@[step_of reluSinghQuadRelaxation]
def step_reluQuadCase (l u : 𝕋) : ℕ :=
  if le u zero then 0 else if le zero l then 1
  else if ltStrict zero (step_reluQuadCoeffs l u).1 then 2 else 3


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The fit of order 2, lowest coefficient first, and its error. -/
def reluSinghQuadRelaxation : PolyRelaxation 𝕋 2 where
  coeffs l u :=
    let q := step_reluQuadCoeffs l u                                  -- (a, b, c)
    match step_reluQuadCase l u with
    | 0 => ![zero, zero, zero]
    | 1 => ![zero, one, zero]
    | 2 => ![subDown q.2.2 (step_reluQuadMid l u), q.2.1, q.1]
    | _ => (((reluRelaxation reluSlope).toPoly).padTo 2).coeffs l u
  error l u :=
    let c := (step_reluQuadCoeffs l u).2.2
    let m := step_reluQuadMid l u
    let D := maximum (subUp (step_reluQuadBand l u).2 m) (subUp m (step_reluQuadBand l u).1)
    let g := subUp (subUp c m) (subDown c m)                         -- the rounding of c - m
    match step_reluQuadCase l u with
    | 0 | 1 => zero
    | 2 => if le g zero then D else addUp D g
    | _ => (reluRelaxation (𝕋 := 𝕋) reluSlope).error l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

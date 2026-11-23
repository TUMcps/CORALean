module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.Global.Float.SinCos
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The relaxation of sine and cosine

CORA.cpp's `priv_trig_line` for `f = sin` or `cos` on `[l, u]`, the narrower of two lines, in
CORA.cpp's order at round to nearest:
* the tangent at the middle `c`, radius `d² / 2` (`|f''| ≤ 1`, `d` the larger half width times
  `1 + w₄`), widened by CORA.cpp's `w (1 + |m| max(|l|, |u|) + d)` and by the cost of rounding
  `f(c)`, `f'(c)` and the offset (`+0` at nearest);
* slope 0 over `priv_trig_box`: the end values widened by `w`, and `±1` where an extremum
  `a + 2π k` may lie in the box, decided by an integer between the widened quotients
  `(l - a) / 2π` and `(u - a) / 2π`; binary64's `π` is bracketed from below and above.

## Inputs
* `cosine` – `cos`, else `sin`
* `n` – the halvings of `sin` and `cos`
* `w` – the margin's factor (CORA.cpp's `16 eps`)
* `w₁` – the box's margin factor (CORA.cpp's `eps`)
* `w₄` – the half width's widening (CORA.cpp's `4 eps`)

## Output
* the relaxation of sine or cosine
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The exponents `k` of binary64's `π / 2 = Σ 2⁻ᵏ`. -/
@[step_of trigRelaxation]
def step_trigPiBits : List ℕ :=
  [0, 1, 4, 7, 12, 13, 14, 15, 16, 17, 19, 20, 22, 24, 26, 30, 34, 39, 41, 42, 44, 48, 49]

/-- Binary64's `π`, below the real one: its bits summed downward, doubled. -/
@[step_of trigRelaxation]
def step_trigPiDown : 𝕋 :=
  let σ := step_trigPiBits.foldr (fun k s => addDown (half^[k] one) s) zero
  addDown σ σ

/-- Above the real `π`: binary64's, plus `3 · 2⁻⁵⁴` (less than its half ulp). -/
@[step_of trigRelaxation]
def step_trigPiUp : 𝕋 :=
  let σ := step_trigPiBits.foldr (fun k s => addUp (half^[k] one) s) zero
  addUp (addUp σ σ) (addUp (half^[53] one) (half^[54] one))

/-- The maxima `a + 2π k` (`bottom`: the minima) of `f`, `a` from below and from above:
`π / 2` (`0` for `cos`), and `π` more for the minima. -/
@[step_of trigRelaxation]
def step_trigPeak (cosine bottom : Bool) : 𝕋 × 𝕋 :=
  let pL := step_trigPiDown (𝕋 := 𝕋)
  let pU := step_trigPiUp (𝕋 := 𝕋)
  let top : 𝕋 × 𝕋 := if cosine then (zero, zero) else (half pL, half pU)
  if bottom then (addDown top.1 pL, addUp top.2 pU) else top

/-- Whether `a + 2π k` may lie in `[l, u]` for `a ∈ [aLo, aHi]`: an integer between
`(l - a) / 2π` from below and `(u - a) / 2π` from above, each widened by `w (|t| + 1)`. -/
@[step_of trigRelaxation]
def step_trigInside (w aLo aHi l u : 𝕋) : Bool :=
  let pL := step_trigPiDown (𝕋 := 𝕋)
  let pU := step_trigPiUp (𝕋 := 𝕋)
  -- `1 / 2π` from below and from above (`1` if `2π` is not certified positive from below)
  let invLo := divDown one (addUp pU pU)
  let twoL := addDown pL pL
  let invHi := if ltStrict zero twoL then divUp one twoL else one
  -- the quotients, then widened
  let nl := subDown l aHi
  let nu := subUp u aLo
  let tl := minimum (mulDown nl invLo) (mulDown nl invHi)
  let tu := maximum (mulUp nu invLo) (mulUp nu invHi)
  let sl := subDown tl (mulUp (addUp (absolute tl) one) w)
  let su := addUp tu (mulUp (addUp (absolute tu) one) w)
  if ⌈ToRat.toRat sl⌉ ≤ ⌊ToRat.toRat su⌋ then true else false

/-- The box's lower end: the smaller end value less `w`, or `-1` where a minimum may lie inside;
at least `-1`. -/
@[step_of trigRelaxation]
def step_trigBoxLo (cosine : Bool) (n : ℕ) (w l u : 𝕋) : 𝕋 :=
  let f := fun x => if cosine then cosDown n x else sinDown n x
  let lo := subDown (minimum (f l) (f u)) w
  let a := step_trigPeak (𝕋 := 𝕋) cosine true
  if step_trigInside w a.1 a.2 l u then neg one else maximum lo (neg one)

/-- The box's upper end: the larger end value plus `w`, or `1` where a maximum may lie inside; at
most `1`. -/
@[step_of trigRelaxation]
def step_trigBoxHi (cosine : Bool) (n : ℕ) (w l u : 𝕋) : 𝕋 :=
  let f := fun x => if cosine then cosUp n x else sinUp n x
  let hi := addUp (maximum (f l) (f u)) w
  let a := step_trigPeak (𝕋 := 𝕋) cosine false
  if step_trigInside w a.1 a.2 l u then one else minimum hi one

/-- The band of slope 0 over the box, with CORA.cpp's margin `w₁ (|hi| + |lo|)`. -/
@[step_of trigRelaxation]
def step_trigBand (cosine : Bool) (n : ℕ) (w w₁ : 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofBand (fun _ _ => zero) (step_trigBoxLo cosine n w) (step_trigBoxHi cosine n w)
    fun l u => mulUp (addUp (absolute (step_trigBoxHi cosine n w l u))
      (absolute (step_trigBoxLo cosine n w l u))) w₁

/-- The middle `l / 2 + u / 2`. -/
@[step_of trigRelaxation]
def step_trigMid (l u : 𝕋) : 𝕋 := addUp (half l) (half u)

/-- The larger half width, times `1 + w₄`. -/
@[step_of trigRelaxation]
def step_trigReach (w₄ l u : 𝕋) : 𝕋 :=
  let c := step_trigMid l u
  mulUp (maximum (subUp u c) (subUp c l)) (addUp one w₄)

/-- `f'(c)` from below (`cos c`, or `-sin c`), and from above. -/
@[step_of trigRelaxation]
def step_trigSlope (cosine : Bool) (n : ℕ) (c : 𝕋) : 𝕋 × 𝕋 :=
  if cosine then (neg (sinUp n c), neg (sinDown n c)) else (cosDown n c, cosUp n c)

/-- `f(c)` from below, and from above. -/
@[step_of trigRelaxation]
def step_trigValue (cosine : Bool) (n : ℕ) (c : 𝕋) : 𝕋 × 𝕋 :=
  if cosine then (cosDown n c, cosUp n c) else (sinDown n c, sinUp n c)

/-- The tangent's offset `f(c) - m c`, rounded down. -/
@[step_of trigRelaxation]
def step_trigOffset (cosine : Bool) (n : ℕ) (l u : 𝕋) : 𝕋 :=
  let c := step_trigMid l u
  subDown (step_trigValue cosine n c).1 (mulUp (step_trigSlope cosine n c).1 c)

/-- CORA.cpp's radius of the tangent, `d² / 2 + w (1 + |m| max(|l|, |u|) + d)`. -/
@[step_of trigRelaxation]
def step_trigRadius (cosine : Bool) (n : ℕ) (w w₄ l u : 𝕋) : 𝕋 :=
  let c := step_trigMid l u
  let d := step_trigReach w₄ l u
  let m := (step_trigSlope cosine n c).1
  let big := addUp (addUp one (mulUp (absolute m) (maximum (absolute l) (absolute u)))) d
  addUp (half (mulUp d d)) (mulUp big w)

/-- The tangent's error: the radius plus the roundings' cost of `f(c)`, `f'(c)` (at the reach) and
the offset, each `+0` at round to nearest. -/
@[step_of trigRelaxation]
def step_trigError (cosine : Bool) (n : ℕ) (w w₄ l u : 𝕋) : 𝕋 :=
  let c := step_trigMid l u
  let d := step_trigReach w₄ l u
  let m := step_trigSlope cosine n c
  let fc := step_trigValue cosine n c
  let e₁ := subUp fc.2 fc.1
  let e₂ := subUp m.2 m.1
  let e₃ := subUp (subUp fc.1 (mulDown m.1 c)) (step_trigOffset cosine n l u)
  addUp (addUp (addUp (step_trigRadius cosine n w w₄ l u) e₁) (mulUp e₂ d)) e₃

/-- The tangent where its radius is below the band's error. -/
@[step_of trigRelaxation]
def step_trigUse (cosine : Bool) (n : ℕ) (w w₁ w₄ l u : 𝕋) : Bool :=
  ltStrict (step_trigRadius cosine n w w₄ l u) ((step_trigBand cosine n w w₁).error l u)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tangent at the middle where it is narrower, else slope 0 over the range's box. -/
def trigRelaxation (cosine : Bool) (n : ℕ) (w w₁ w₄ : 𝕋) : Relaxation 𝕋 where
  slope l u := if step_trigUse cosine n w w₁ w₄ l u then
    (step_trigSlope cosine n (step_trigMid l u)).1 else zero
  offset l u := if step_trigUse cosine n w w₁ w₄ l u then step_trigOffset cosine n l u
    else (step_trigBand cosine n w w₁).offset l u
  error l u := if step_trigUse cosine n w w₁ w₄ l u then step_trigError cosine n w w₄ l u
    else (step_trigBand cosine n w w₁).error l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

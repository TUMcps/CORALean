module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.NN.Layers.Operations.RegressionSlope
public import CORALean.Global.Float.SqrtDownCora
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The line of the square root

CORA.cpp's `priv_monotone_line` for `f(x) = √x` on boxes with `0 ≤ l`, with the upper end from the
closed-form maximum. The slope `m` is Singh's `f'(u) = (1 / √u) / 2` (`0` at `u = 0`) or the
least-squares slope through twenty points (`regressionSlope`). `g(x) = √x - m x` is concave, so on
the box it is at least the smaller of `g(l)` and `g(u)`. For `m > 0` it is at most its maximum over
the half-line, `1 / (4 m)` at `x = 1 / (4 m²)`, for `m ≤ 0` the larger end value; a sound format
that decides neither takes `√u` plus the larger of `-m l` and `-m u`. The band goes to
`Relaxation.ofBand` without a margin; at round to nearest this is CORA.cpp's order.

## Inputs
* `regression` – the least-squares slope (CORA's default), else Singh's
* `p` – the square root's Newton steps

## Output
* the line of the square root
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `√x` from below and above. -/
@[step_of rootLineRelaxation]
def step_rootLineEnclosure (p : ℕ) : Enclosure 𝕋 where
  enclose x := ⟨sqrtDownCora p x, sqrtUp p x⟩

/-- The least-squares slope, or Singh's `(1 / √u) / 2` (`0` at `u = 0`). -/
@[step_of rootLineRelaxation]
def step_rootLineSlope (regression : Bool) (p : ℕ) (l u : 𝕋) : 𝕋 :=
  if regression then regressionSlope (step_rootLineEnclosure p) l u
  else if ltStrict zero u then half (divDown one (sqrtDownCora p u)) else zero

/-- The smaller of `g(l)` and `g(u)`, rounded down. -/
@[step_of rootLineRelaxation]
def step_rootLineLo (regression : Bool) (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_rootLineSlope regression p l u
  let g := fun x => subDown ((step_rootLineEnclosure p).enclose x).inf (mulUp m x)
  minimum (g l) (g u)

/-- The larger of `g(l)` and `g(u)`, and the closed-form maximum `1 / (4 m)` where `m > 0`,
rounded up. -/
@[step_of rootLineRelaxation]
def step_rootLineHi (regression : Bool) (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_rootLineSlope regression p l u
  let g := fun x => subUp ((step_rootLineEnclosure p).enclose x).sup (mulDown m x)
  let ends := maximum (g l) (g u)
  if ltStrict zero m then maximum ends (half (half (divUp one m)))
  else if le m zero then ends
  else addUp (sqrtUp p u) (maximum (neg (mulDown m l)) (neg (mulDown m u)))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `√x - m x`, its middle and half its width. -/
def rootLineRelaxation (regression : Bool) (p : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofBand (step_rootLineSlope regression p) (step_rootLineLo regression p)
    (step_rootLineHi regression p) fun _ _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

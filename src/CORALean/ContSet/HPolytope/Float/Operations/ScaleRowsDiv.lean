module

public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `HPolytope.scaleRowsDiv`: rows divided by given numbers, the rounding paid on the right-hand side

CORA.cpp's `normalizeConstraints` divides every entry of a row by a number (`A / d`), where
`HPolytope.scaleRows` multiplies by a given scaling (`A * (1/d)`), which rounds differently. Every
entry of a divided row is rounded down (`sdivDown`), which names a slightly different halfspace,
so the difference is absorbed on the right-hand side over a box `dom` of interest, as for
`scaleRows`. The divisor of an equality row may be negative: `sdivDown a d` is then the quotient
of `-a` by `-d`.

## Inputs
* `P` – H-polytope
* `dA` – divisors indexed by `Fin P.m`
* `dE` – divisors indexed by `Fin P.me`
* `dom` – domain interval

## Output
* row `i` divided by `dA i` (`dE i`), the rounding in the rows' slacks
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `a / d` rounded down for a certified negative or a positive `d`: a negative one by the
negation of both. -/
@[step_of HPolytope.scaleRowsDiv]
def HPolytope.step_sdivDown (a d : 𝕋) : 𝕋 :=
  if ltStrict d zero then divDown (neg a) (neg d) else divDown a d

/-- `a / d` rounded up, as `sdivDown`. -/
@[step_of HPolytope.scaleRowsDiv]
def HPolytope.step_sdivUp (a d : 𝕋) : 𝕋 :=
  if ltStrict d zero then divUp (neg a) (neg d) else divUp a d

/-- The lower bound of `(v / d - ṽ)ᵀ x` over `x ∈ dom`, for `ṽ = sdivDown v d`. -/
@[step_of HPolytope.scaleRowsDiv]
def HPolytope.step_divDevLo (v : Vec 𝕋 n) (d : 𝕋) (dom : Interval (Vec 𝕋 n)) : 𝕋 :=
  sumDown fun j =>
    Interval.mulLo (subDown (HPolytope.step_sdivDown (v j) d) (HPolytope.step_sdivDown (v j) d))
      (subUp (HPolytope.step_sdivUp (v j) d) (HPolytope.step_sdivDown (v j) d))
      (dom.inf j) (dom.sup j)

/-- The upper bound of `(v / d - ṽ)ᵀ x` over `x ∈ dom`, for `ṽ = sdivDown v d`. -/
@[step_of HPolytope.scaleRowsDiv]
def HPolytope.step_divDevHi (v : Vec 𝕋 n) (d : 𝕋) (dom : Interval (Vec 𝕋 n)) : 𝕋 :=
  sumUp fun j =>
    Interval.mulHi (subDown (HPolytope.step_sdivDown (v j) d) (HPolytope.step_sdivDown (v j) d))
      (subUp (HPolytope.step_sdivUp (v j) d) (HPolytope.step_sdivDown (v j) d))
      (dom.inf j) (dom.sup j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` divided by `dA i` (`dE i`), the rounding in the rows' slacks. -/
def HPolytope.scaleRowsDiv (P : HPolytope 𝕋 (Vec 𝕋 n)) (dA : Fin P.m → 𝕋) (dE : Fin P.me → 𝕋)
    (dom : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the divided rows, read as error-free
  let Q : HPolytope 𝕋 (Vec 𝕋 n) :=
    { m := P.m
      A := fun i j => HPolytope.step_sdivDown (P.A i j) (dA i)
      b := P.b
      me := P.me
      Ae := fun i j => HPolytope.step_sdivDown (P.Ae i j) (dE i)
      be := P.be
      b_error := fun _ => zero
      be_error := fun _ => zero
      I_error := Interval.origin n }
  -- each right-hand side: the divided bound less the deviation, between its two ends
  Q.setRhs
    (fun i => subDown (HPolytope.step_sdivDown (P.b i) (dA i))
      (HPolytope.step_divDevHi (P.A i) (dA i) dom))
    (fun i => subUp (HPolytope.step_sdivUp (P.b i) (dA i))
      (HPolytope.step_divDevLo (P.A i) (dA i) dom))
    (fun i => subDown (HPolytope.step_sdivDown (P.be i) (dE i))
      (HPolytope.step_divDevHi (P.Ae i) (dE i) dom))
    (fun i => subUp (HPolytope.step_sdivUp (P.be i) (dE i))
      (HPolytope.step_divDevLo (P.Ae i) (dE i) dom))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

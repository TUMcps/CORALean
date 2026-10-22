import CORALean.Examples.Bench.RandVerifyRatExact
import CORALean.Global.Float.Interfaces
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `randverify`: an unsafe box rounded outward into a number type

Each lower bound is rounded down and each upper bound up, by the format's own `addDown x 0` and
`addUp x 0` on the exact value, so the box only grows: a reach set disjoint from the enlarged box
is disjoint from the original. A bound that is not binary (a decimal) is first bracketed by the
dyadic at `2^-60` on the outward side, then rounded. Per dimension the result is the two bounds
and whether rounding moved each (`ToRat.toRat` against the file's exact value).

## Inputs
* `exactIn` – exact number held off the grid
* `S` – unsafe box

## Output
* box rounded outward into the number type
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q` if binary, else the dyadic at `2^-60` just below (`up = false`) or above it. -/
def aux_bracket (q : ℚ) (up : Bool) : ExactDyadic :=
  match ratExact q with
  | .ok d => d
  | .error _ =>
    let k : ℚ := 2 ^ 60
    let m : ℤ := if up then ⌈q * k⌉ else ⌊q * k⌋
    (ratExact ((m : ℚ) / k)).toOption.getD ⟨m, -60⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(lower, upper, lower moved, upper moved)` per dimension. -/
def roundUnsafeOut (exactIn : ExactDyadic → 𝕋) (S : Array (ℚ × ℚ)) :
    Array (𝕋 × 𝕋 × Bool × Bool) :=
  S.map fun (l, h) =>
    let lo := FloatOps.addDown (exactIn (aux_bracket l false)) FloatOps.zero
    let hi := FloatOps.addUp (exactIn (aux_bracket h true)) FloatOps.zero
    (lo, hi, ToRat.toRat lo != l, ToRat.toRat hi != h)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

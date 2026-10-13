module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Mul
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-!
# `PolyZonotope.evalPoly`'s dependent-generator count

Horner's rule multiplies by `pZ` once per coefficient, and `mul_h` turns every
step into `(h+1)*(pZ.h+1)`: starting the accumulator at `h = 0` and folding that
step `coeffs.length` times is exactly `x * geom_sum x coeffs.length` at
`x = pZ.h + 1`, `geom_sum_succ` carrying the one step the induction needs. The
count depends on `pZ` only through `pZ.h`, and on `coeffs` only through its
length, not on the coefficients' own values — the fact `Layer.activationPoly`'s
generator count rests on: a layer's order pattern chooses `coeffs.length`, and
nothing about the individual neurons' fits reaches this count at all.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact count: `pZ.h + 1` times the geometric sum of `coeffs.length` of its
own powers, `mul_h`'s step for step. -/
theorem PolyZonotope.evalPoly_h (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    (pZ.evalPoly coeffs).h
      = (pZ.h + 1) * ∑ i ∈ Finset.range coeffs.length, (pZ.h + 1) ^ i := by -- --- PROOF ---
  induction coeffs with
  | nil =>
    show (0 : ℕ) = (pZ.h + 1) * ∑ i ∈ Finset.range 0, (pZ.h + 1) ^ i
    simp
  | cons a0 rest ih =>
    have hstep : (pZ.evalPoly (a0 :: rest)).h
        = (PolyZonotope.mul (pZ.evalPoly rest) pZ (PolyZonotope.evalPolyP pZ rest).2).h := rfl
    rw [hstep, PolyZonotope.mul_h, ih, List.length_cons, geom_sum_succ]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

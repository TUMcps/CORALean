module

public import CORALean.ContSet.Interval.Float.Operations.EvalPolyCoeffs
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.Global.EvalList

@[expose] public section

/-!
# `Interval.evalPolyCoeffs` encloses the polynomial

At every point of the box `[lo, hi]` the value of the polynomial with the integer coefficients `l`
(`evalL l x`) lies between the two ends.

## Inputs
* `lo` – lower bound of the argument
* `hi` – upper bound of the argument
* `x` – real argument
* `l` – integer coefficient list

## Hypotheses
* `h₁` – lower bound below `x`
* `h₂` – `x` below the upper bound

## Conclusion
* the polynomial value at `x` lies between the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.evalPolyCoeffs_mem {lo hi : 𝕋} {x : ℝ} (h₁ : toReal lo ≤ x) (h₂ : x ≤ toReal hi)
    (l : List ℤ) :
    toReal (Interval.evalPolyCoeffs lo hi l).inf ≤ evalL l x ∧
      evalL l x ≤ toReal (Interval.evalPolyCoeffs lo hi l).sup := by -- --- PROOF ---
  induction l with
  | nil => simp [Interval.evalPolyCoeffs, evalL, toReal_zero]
  | cons a l ih =>
    have hm := Interval.mul_between_corners h₁ h₂ ih.1 ih.2
    have ha := intDown_le_intUp (𝕋 := 𝕋) a
    have h3 := addDown_le_add (intDown a : 𝕋)
      (Interval.mulLo lo hi (Interval.evalPolyCoeffs lo hi l).inf
        (Interval.evalPolyCoeffs lo hi l).sup)
    have h4 := add_le_addUp (intUp a : 𝕋)
      (Interval.mulHi lo hi (Interval.evalPolyCoeffs lo hi l).inf
        (Interval.evalPolyCoeffs lo hi l).sup)
    simp only [Interval.evalPolyCoeffs, evalL]
    constructor <;> linarith [ha.1, ha.2, hm.1, hm.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

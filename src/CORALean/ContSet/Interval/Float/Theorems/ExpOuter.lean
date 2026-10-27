module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.ExpExact

@[expose] public section

/-!
# `Interval.exp` contains the image under the exponential

`expDown` holds at every argument, `expUp p a` only for `toReal a ≤ 2 ^ p / 2` (`le_expUp`, issues
#46 and #48). So the theorem takes that bound on every upper bound of the box as a hypothesis,
which a caller discharges with `le_expUp_of_le` against a known bound.

Eq. (3.2) of [1, Def. 5] for the exponential, under the precision bound.

## Inputs
* `p` – precision of the exponentials
* `I` – interval box

## Hypotheses
* `hI` – upper bounds within the exponential range

## Conclusion
* the exponential image of `I` lies in the result box

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exp_outer (p : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.sup i) ≤ 2 ^ p / 2) :
    (fun x i => Real.exp (x i)) '' I.construct ⊆ (I.exp p).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (expDown_le p _) (Real.exp_le_exp.2 hx'.1),
    le_trans (Real.exp_le_exp.2 hx'.2) (le_expUp p _ (hI i))⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

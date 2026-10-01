import CORALean.ContSet.Interval.Float.Operations.Exp
import CORALean.ContSet.Interval.Real.Theorems.ExpExact

/-!
# `Interval.exp` contains the image under the exponential

`expDown` holds at every argument, `expUp p a` only for `toReal a ≤ 2 ^ p / 2` (`le_expUp`, issues
#46 and #48). So the theorem takes that bound on every upper bound of the box as a hypothesis,
which a caller discharges with `le_expUp_of_le` against a known bound.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

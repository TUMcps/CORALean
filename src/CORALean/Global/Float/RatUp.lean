import CORALean.Global.Float.FloatOps
import Mathlib.Data.Rat.Defs

/-!
# A rational, rounded up into the scalar

`ratUp q`: `num` and `den` by binary doubling, `num` rounded up and `den` down,
then `divUp`. Made for a tuning loop's guesses, where a horizon `t_f - t_i`
held exactly in ℚ has to become a candidate step: nothing proves the result
dominates `q`, and nothing needs to, since a caller reads the step it chose
back through `ToRat` rather than trusting this.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(lo, hi)` around `k`, by binary doubling. -/
def aux_natBracket : ℕ → 𝕋 × 𝕋
  | 0 => (zero, zero)
  | k + 1 =>
    let h := aux_natBracket ((k + 1) / 2)                             -- ⌊(k + 1)/2⌋
    let d := (addDown h.1 h.1, addUp h.2 h.2)                         -- doubled
    if (k + 1) % 2 = 0 then d else (addDown d.1 one, addUp d.2 one)  -- and one more if odd
termination_by k => k
decreasing_by omega


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `q`, rounded up for a positive `q`: the numerator up over the denominator down. -/
def ratUp (q : ℚ) : 𝕋 :=
  divUp (aux_natBracket q.num.toNat).2 (aux_natBracket q.den).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

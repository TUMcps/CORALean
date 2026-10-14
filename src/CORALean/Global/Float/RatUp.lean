module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# A rational, rounded up into the scalar

`ratUp q`: `num` and `den` by binary doubling, `num` rounded up and `den` down,
then `divUp`. Made for a tuning loop's guesses, where a horizon `t_f - t_i`
held exactly in ℚ has to become a candidate step: nothing proves the result
dominates `q`, and nothing needs to, since a caller reads the step it chose
back through `ToRat` rather than trusting this.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `[inf, sup]` around `k`, by binary doubling. -/
def aux_natBracket : ℕ → Interval 𝕋
  | 0 => ⟨zero, zero⟩
  | k + 1 =>
    let h := aux_natBracket ((k + 1) / 2)                             -- ⌊(k + 1)/2⌋
    let d : Interval 𝕋 := ⟨addDown h.inf h.inf, addUp h.sup h.sup⟩   -- doubled
    if (k + 1) % 2 = 0 then d else ⟨addDown d.inf one, addUp d.sup one⟩ -- and one more if odd
termination_by k => k
decreasing_by omega


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `q`, rounded up for a positive `q`: the numerator up over the denominator down. -/
def ratUp (q : ℚ) : 𝕋 :=
  divUp (aux_natBracket q.num.toNat).sup (aux_natBracket q.den).inf

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

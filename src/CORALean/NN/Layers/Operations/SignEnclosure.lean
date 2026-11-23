module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The sign enclosure

The sign of a stored value, `-1`, `0` or `1`, read off the comparisons with zero. `le` certifies
`≤` only, so each end decides by the comparison that is sound for it: the upper end is `-1` only
where `ltStrict` proves the value negative, `0` where `le` proves it at most zero, else `1`; the
lower end mirrors it. At round to nearest both ends are the machine's `sign`.

## Inputs
* none

## Output
* enclosure of the sign from the comparisons with zero
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

/-- The sign from below: `1` where the value is provably positive, `0` where it is provably at
least zero, else `-1`. -/
@[step_of signEnclosure]
def step_signDown (a : 𝕋) : 𝕋 :=
  if ltStrict zero a then one else if le zero a then zero else neg one

/-- The sign from above: `-1` where the value is provably negative, `0` where it is provably at
most zero, else `1`. -/
@[step_of signEnclosure]
def step_signUp (a : 𝕋) : 𝕋 :=
  if ltStrict a zero then neg one else if le a zero then zero else one


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both ends of the sign of a stored value. -/
def signEnclosure : Enclosure 𝕋 where
  enclose a := ⟨step_signDown a, step_signUp a⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

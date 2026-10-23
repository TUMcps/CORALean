module

public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# An interval over a float scalar, read as reals

The interval with the same flags whose bounds are the reals the stored bounds denote: what a float
`stlInterval` means. It is the time interval the soundness of the float signal operations refers
to; it has the same `set`.

## Inputs
* none

## Output
* the interval over `ℝ` with the denoted bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval with the reals the bounds denote; the proof fields carry over, as they are stated
through `toReal` and `toReal` is the identity on `ℝ`. -/
def STLInterval.toRealInterval : STLInterval 𝕋 → STLInterval ℝ
  | .empty => .empty
  | .nonempty l none lc rc hu hlt h0 => .nonempty (toReal l) none lc rc (fun _ => hu rfl) hlt h0
  | .nonempty l (some u) lc rc _ hlt h0 =>
    .nonempty (toReal l) (some (toReal u)) lc rc (fun h => nomatch h) hlt h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

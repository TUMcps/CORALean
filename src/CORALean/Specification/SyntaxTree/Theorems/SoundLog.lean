module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesLog
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.LogSound

@[expose] public section

/-!
# `log` of a sound tree is sound

The node `log` of a positive operand builds over a sound tree is sound: its interval encloses it
(`encloses_log`) and its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound
* `hd` – the operand is positive

## Conclusion
* the logarithm tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `log` of a positive operand node over a sound tree is sound. -/
theorem SyntaxTree.sound_log (h : Sound B t) (hd : 0 < t.value.inf 0) : Sound B (t.log) :=
  ⟨h, encloses_log (encloses_of_sound h) hd, log_sound t.value hd⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

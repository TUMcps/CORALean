module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSqrt
public import CORALean.Specification.SyntaxTree.Theorems.SqrtSound

@[expose] public section

/-!
# `sqrt` of a sound tree is sound

The node `sqrt` of a nonnegative operand builds over a sound tree is sound: its interval encloses
it (`encloses_sqrt`) and its `funHan` is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `sqrt` of a nonnegative operand node over a sound tree is sound. -/
theorem SyntaxTree.sound_sqrt (h : Sound B t) (hd : 0 ≤ t.value.inf 0) : Sound B (t.sqrt) :=
  ⟨h, encloses_sqrt (encloses_of_sound h) hd, sqrt_sound t.value hd⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

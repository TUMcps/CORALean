module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSin
public import CORALean.Specification.SyntaxTree.Theorems.SinSound

@[expose] public section

/-!
# `sin` of a sound tree is sound

The node `sin` builds over a sound tree is sound: its interval encloses it (`encloses_sin`) and its
`funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the sine tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `sin` node over a sound tree is sound. -/
theorem SyntaxTree.sound_sin (h : IsSound B t) : IsSound B (t.sin) :=
  ⟨h, encloses_sin (encloses_of_sound h), sin_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

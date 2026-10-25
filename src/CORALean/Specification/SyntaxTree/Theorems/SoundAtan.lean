module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAtan
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanSound

@[expose] public section

/-!
# `atan` of a sound tree is sound

The node `atan` builds over a sound tree is sound: its interval encloses it (`encloses_atan`) and
its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the inverse tangent tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `atan` node over a sound tree is sound. -/
theorem SyntaxTree.sound_atan (h : IsSound B t) : IsSound B (t.atan) :=
  ⟨h, encloses_atan (encloses_of_sound h), funHanAtan_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

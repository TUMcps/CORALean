module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSinh
public import CORALean.Specification.SyntaxTree.Theorems.FunHanSinhSound

@[expose] public section

/-!
# `sinh` of a sound tree is sound

The node `sinh` builds over a sound tree is sound: its interval encloses it (`encloses_sinh`) and
its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the hyperbolic sine tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `sinh` node over a sound tree is sound. -/
theorem SyntaxTree.sound_sinh (h : Sound B t) : Sound B (t.sinh) :=
  ⟨h, encloses_sinh (encloses_of_sound h), funHanSinh_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

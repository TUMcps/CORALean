module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAsinh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinhSound

@[expose] public section

/-!
# `asinh` of a sound tree is sound

The node `asinh` builds over a sound tree is sound: its interval encloses it (`encloses_asinh`) and
its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the inverse hyperbolic sine tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `asinh` node over a sound tree is sound. -/
theorem SyntaxTree.sound_asinh (h : Sound B t) : Sound B (t.asinh) :=
  ⟨h, encloses_asinh (encloses_of_sound h), funHanAsinh_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

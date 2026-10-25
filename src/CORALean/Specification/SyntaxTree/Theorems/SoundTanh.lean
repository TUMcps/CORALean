module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesTanh
public import CORALean.Specification.SyntaxTree.Theorems.TanhSound

@[expose] public section

/-!
# `tanh` of a sound tree is sound

The node `tanh` builds over a sound tree is sound: its interval encloses it (`encloses_tanh`) and
its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the hyperbolic tangent tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `tanh` node over a sound tree is sound. -/
theorem SyntaxTree.sound_tanh (h : IsSound B t) : IsSound B (t.tanh) :=
  ⟨h, encloses_tanh (encloses_of_sound h), tanh_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

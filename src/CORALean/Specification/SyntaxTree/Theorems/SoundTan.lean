module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesTan
public import CORALean.Specification.SyntaxTree.Theorems.TanSound

@[expose] public section

/-!
# `tan` of a sound tree is sound

The node `tan` of an operand inside `(-pi/2, pi/2)` builds over a sound tree is sound: its interval
encloses it (`encloses_tan`) and its `funHan` is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `tan` of an operand inside `(-pi/2, pi/2)` node over a sound tree is sound. -/
theorem SyntaxTree.sound_tan (h : Sound B t) (hd₁ : -(Real.pi / 2) < t.value.inf 0) (hd₂ :
    t.value.sup 0 < Real.pi / 2) : Sound B (t.tan) :=
  ⟨h, encloses_tan (encloses_of_sound h) hd₁ hd₂, tan_sound t.value hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

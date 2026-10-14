module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAcos
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcosSound

@[expose] public section

/-!
# `acos` of a sound tree is sound

The node `acos` of an operand inside `[-1,1]` builds over a sound tree is sound: its interval
encloses it (`encloses_acos`) and its `funHan` is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `acos` of an operand inside `[-1,1]` node over a sound tree is sound. -/
theorem SyntaxTree.sound_acos (h : Sound B t) (hd₁ : -1 ≤ t.value.inf 0) (hd₂ : t.value.sup 0 ≤ 1)
    : Sound B (t.acos) :=
  ⟨h, encloses_acos (encloses_of_sound h) hd₁ hd₂, funHanAcos_sound t.value hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

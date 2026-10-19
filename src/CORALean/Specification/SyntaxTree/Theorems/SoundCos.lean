module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.CosSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesCos
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound

@[expose] public section

/-!
# `cos` of a sound tree is sound

The node `cos` builds over a sound tree is sound: its interval encloses it (`encloses_cos`) and its
`funHan` is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `cos` node over a sound tree is sound. -/
theorem SyntaxTree.sound_cos (h : Sound B t) : Sound B (t.cos) :=
  ⟨h, encloses_cos (encloses_of_sound h), cos_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

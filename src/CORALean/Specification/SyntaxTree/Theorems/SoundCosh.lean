module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.CoshSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesCosh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound

@[expose] public section

/-!
# `cosh` of a sound tree is sound

The node `cosh` builds over a sound tree is sound: its interval encloses it (`encloses_cosh`) and
its `funHan` is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `cosh` node over a sound tree is sound. -/
theorem SyntaxTree.sound_cosh (h : Sound B t) : Sound B (t.cosh) :=
  ⟨h, encloses_cosh (encloses_of_sound h), cosh_sound t.value⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

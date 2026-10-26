module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAcosh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcoshSound

@[expose] public section

/-!
# `acosh` of a sound tree is sound

The node `acosh` of an operand `≥ 1` builds over a sound tree is sound: its interval encloses it
(`encloses_acosh`) and its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound
* `hd` – the operand is at least one

## Conclusion
* the inverse hyperbolic cosine tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `acosh` of an operand `≥ 1` node over a sound tree is sound. -/
theorem SyntaxTree.isSound_acosh (h : IsSound B t) (hd : 1 ≤ t.value.inf 0) : IsSound B (t.acosh) :=
  ⟨h, encloses_acosh (encloses_of_isSound h) hd, funHanAcosh_sound t.value hd⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

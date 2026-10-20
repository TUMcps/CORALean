module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAsin
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinSound

@[expose] public section

/-!
# `asin` of a sound tree is sound

The node `asin` of an operand inside `[-1,1]` builds over a sound tree is sound: its interval
encloses it (`encloses_asin`) and its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound
* `hd₁` – the operand stays above minus one
* `hd₂` – the operand stays below one

## Conclusion
* the inverse sine tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `asin` of an operand inside `[-1,1]` node over a sound tree is sound. -/
theorem SyntaxTree.sound_asin (h : Sound B t) (hd₁ : -1 ≤ t.value.inf 0) (hd₂ : t.value.sup 0 ≤ 1)
    : Sound B (t.asin) :=
  ⟨h, encloses_asin (encloses_of_sound h) hd₁ hd₂, funHanAsin_sound t.value hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAtanh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanhSound

@[expose] public section

/-!
# `atanh` of a sound tree is sound

The node `atanh` of an operand inside `(-1,1)` builds over a sound tree is sound: its interval
encloses it (`encloses_atanh`) and its `funHan` is sound.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound
* `hd₁` – the operand stays above minus one
* `hd₂` – the operand stays below one

## Conclusion
* the inverse hyperbolic tangent tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `atanh` of an operand inside `(-1,1)` node over a sound tree is sound. -/
theorem SyntaxTree.sound_atanh (h : IsSound B t) (hd₁ : -1 < t.value.inf 0) (hd₂ : t.value.sup 0 <
    1)
    : IsSound B (t.atanh) :=
  ⟨h, encloses_atanh (encloses_of_sound h) hd₁ hd₂, funHanAtanh_sound t.value hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanTimesFloatSound

@[expose] public section

/-!
# `times` of two sound float trees is sound

The node `times` builds over two sound float trees is sound: its interval encloses the `*` of the
operands, rounded outward, and `funHanTimesFloat_sound` gives the `funHan`.

## Inputs
* none

## Hypotheses
* `h₁` – the first tree is sound
* `h₂` – the second tree is sound

## Conclusion
* the `times` tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t₁ t₂ : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `times` node over two sound float trees is sound. -/
theorem SyntaxTree.sound_timesFloat (h₁ : SyntaxTree.IsSoundFloat B t₁)
    (h₂ : SyntaxTree.IsSoundFloat B t₂) : SyntaxTree.IsSoundFloat B (SyntaxTree.timesFloat t₁ t₂) :=
  ⟨h₁, h₂, fun x hx => SyntaxTree.contains_timesFloat (SyntaxTree.encloses_of_soundFloat h₁ x hx)
    (SyntaxTree.encloses_of_soundFloat h₂ x hx), SyntaxTree.funHanTimesFloat_sound _ _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

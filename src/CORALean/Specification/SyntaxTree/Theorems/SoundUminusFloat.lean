module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanUminusFloatSound

@[expose] public section

/-!
# `uminus` of a sound float tree is sound

The node `uminus` builds over a sound float tree is sound: its interval is the exact negation, which
holds the negated function, and `funHanUminusFloat_sound` gives the `funHan`.

## Inputs
* none

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `uminus` tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `uminus` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_uminusFloat (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.uminusFloat t) :=
  ⟨h, fun x hx => SyntaxTree.contains_uminusFloat (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanUminusFloat_sound _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Theorems.CosOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanCosFloatSound

@[expose] public section

/-!
# `cos` of a sound float tree is sound

The node `cos` builds over a sound float tree is sound: its interval encloses the cosine:
`Interval.cos` encloses the cosine of the operand and `funHanCosFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of `pi` and of the cosine
* `k` – Newton steps

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `cos` tree is sound
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

/-- The `cos` node over a sound float tree is sound. -/
theorem SyntaxTree.sound_cosFloat [Float.ToRat 𝕋] (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.cosFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.cos_outer p _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanCosFloat_sound p k _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

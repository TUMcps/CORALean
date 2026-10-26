module

public import CORALean.ContSet.Interval.Float.Theorems.AtanOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanFloatSound

@[expose] public section

/-!
# `atan` of a sound float tree is sound

The node `atan` builds over a sound float tree is sound: its interval encloses the inverse tangent:
`Interval.atan` encloses the inverse tangent of the operand and `funHanAtanFloat_sound` gives the
`funHan`.

## Inputs
* `p` – precision of the tangent and of `pi`
* `k` – Newton steps

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `atan` tree is sound
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

/-- The `atan` node over a sound float tree is sound. -/
theorem SyntaxTree.sound_atanFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.atanFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.atan_outer p k _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAtanFloat_sound p k _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Theorems.SqrtOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanSqrtFloatSound

@[expose] public section

/-!
# `sqrt` of a sound float tree is sound

The node `sqrt` builds over a sound float tree is sound: its interval encloses the square root:
`Interval.sqrt` encloses the square root of the operand and `funHanSqrtFloat_sound` gives the
`funHan`.

## Inputs
* `p` – precision of the square root

## Hypotheses
* `h` – the operand tree is sound
* `hd` – the operand interval is nonnegative

## Conclusion
* the `sqrt` tree is sound
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

/-- The `sqrt` node over a sound float tree whose operand is nonnegative is sound. -/
theorem SyntaxTree.isSound_sqrtFloat (p : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hd : 0 ≤ toReal (t.value.inf 0)) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.sqrtFloat p t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.sqrt_outer p _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanSqrtFloat_sound _ _ hd⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

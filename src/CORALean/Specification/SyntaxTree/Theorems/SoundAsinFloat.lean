module

public import CORALean.ContSet.Interval.Float.Theorems.AsinOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinFloatSound

@[expose] public section

/-!
# `asin` of a sound float tree is sound

The node `asin` builds over a sound float tree is sound: its interval encloses the inverse sine:
`Interval.asin` encloses the inverse sine of the operand and `funHanAsinFloat_sound` gives the
`funHan`.

## Inputs
* `p` – precision of the sine and of `pi`
* `k` – Newton steps

## Hypotheses
* `h` – the operand tree is sound
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one

## Conclusion
* the `asin` tree is sound
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

/-- The `asin` node over a sound float tree whose operand stays inside `[-1,1]` is sound. -/
theorem SyntaxTree.sound_asinFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hd₁ : -1 ≤ toReal (t.value.inf 0)) (hd₂ : toReal (t.value.sup 0) ≤ 1) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.asinFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.asin_outer p k _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAsinFloat_sound p k _ _ hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

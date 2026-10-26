module

public import CORALean.ContSet.Interval.Float.Theorems.PowerOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanPowerFloatSound

@[expose] public section

/-!
# `power` of a sound float tree is sound

The node `power` builds over a sound float tree is sound: `Interval.power` encloses the power of the
operand and `funHanPowerFloat_sound` gives the `funHan`.

## Inputs
* `steps` – bisection steps of the roots
* `k` – exponent

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `power` tree is sound
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

/-- The `power` node over a sound float tree is sound. -/
theorem SyntaxTree.sound_powerFloat (steps k : ℕ) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.powerFloat steps k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat (f := fun y : ℝ => y ^ k)
    (Float.Interval.power_outer _ k) (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanPowerFloat_sound steps k _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.SoundPowerFloat

@[expose] public section

/-!
# `mpower` of a sound float tree is sound

The node `mpower` is the node `power`, so it is sound for the same operand trees.

## Inputs
* `steps` – bisection steps of the roots
* `k` – exponent

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `mpower` tree is sound
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

/-- The `mpower` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_mpowerFloat (steps k : ℕ) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.mpowerFloat steps k t) :=
  SyntaxTree.isSound_powerFloat steps k h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

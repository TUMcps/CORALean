module

public import CORALean.ContSet.Interval.Float.Theorems.AcosOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcosFloatSound

@[expose] public section

/-!
# `acos` of a sound float tree is sound

The node `acos` builds over a sound float tree is sound: its interval encloses the inverse cosine:
`Interval.acos` encloses the inverse cosine of the operand and `funHanAcosFloat_sound` gives the
`funHan`.

## Inputs
* `p` – precision of the cosine
* `k` – Newton steps of the inverse cosine

## Hypotheses
* `h` – the operand tree is sound
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one

## Conclusion
* the `acos` tree is sound
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

/-- The `acos` node over a sound float tree whose operand stays inside `[-1,1]` is sound. -/
theorem SyntaxTree.isSound_acosFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hd₁ : -1 ≤ toReal (t.value.inf 0)) (hd₂ : toReal (t.value.sup 0) ≤ 1) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.acosFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.acos_outer p k _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAcosFloat_sound p _ _ hd₁ hd₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Theorems.AsinhOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinhFloatSound

@[expose] public section

/-!
# `asinh` of a sound float tree is sound

The node `asinh` builds over a sound float tree is sound: its interval encloses the inverse
hyperbolic sine: `Interval.asinh` encloses the inverse hyperbolic sine of the operand and
`funHanAsinhFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps

## Hypotheses
* `h` – the operand tree is sound
* `hn` – the operand's lower bound stays within the range of the logarithm
* `hv` – the node's interval stays within the range of the exponential

## Conclusion
* the `asinh` tree is sound
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

/-- The `asinh` node over a sound float tree is sound. -/
theorem SyntaxTree.sound_asinhFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hn : 0 ≤ toReal (t.value.inf 0) → 2 * toReal (t.value.inf 0) + 1 ≤ 2 ^ p / 2)
    (hv : toReal ((Float.Interval.asinh p k t.value).sup 0) ≤ 2 ^ p / 2 ∧ -toReal
      ((Float.Interval.asinh p k t.value).inf 0) ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.asinhFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.asinh_outer p k _ (Fin.forall_fin_one.2 hn))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAsinhFloat_sound p _ _ hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

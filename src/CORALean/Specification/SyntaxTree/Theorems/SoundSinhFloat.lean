module

public import CORALean.ContSet.Interval.Float.Theorems.SinhOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanSinhFloatSound

@[expose] public section

/-!
# `sinh` of a sound float tree is sound

The node `sinh` builds over a sound float tree is sound: its interval encloses the hyperbolic sine:
`Interval.sinh` encloses the hyperbolic sine of the operand and `funHanSinhFloat_sound` gives the
`funHan`.

## Inputs
* `p` – precision of the exponential
* `k` – bisection and root steps

## Hypotheses
* `h` – the operand tree is sound
* `hI` – the operand interval stays within the range of the exponential
* `hv` – the node's interval stays within the range of the logarithm

## Conclusion
* the `sinh` tree is sound
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

/-- The `sinh` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_sinhFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hI : toReal (t.value.sup 0) ≤ 2 ^ p / 2 ∧ -toReal (t.value.inf 0) ≤ 2 ^ p / 2)
    (hv : 2 * toReal ((Float.Interval.sinh p t.value).sup 0) + 1 ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.sinhFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.sinh_outer p _ (Fin.forall_fin_one.2 hI))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanSinhFloat_sound p k _ _ hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

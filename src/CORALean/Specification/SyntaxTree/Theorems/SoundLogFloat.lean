module

public import CORALean.ContSet.Interval.Float.Theorems.LogOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanLogFloatSound

@[expose] public section

/-!
# `log` of a sound float tree is sound

The node `log` builds over a sound float tree is sound: its interval encloses the logarithm:
`Interval.log` encloses the logarithm of the operand and `funHanLogFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of the exponential
* `k` – bisection steps of the logarithm

## Hypotheses
* `h` – the operand tree is sound
* `hI` – the operand interval stays at least one, within the range of the exponential
* `hv` – the node's interval stays within the range of the exponential

## Conclusion
* the `log` tree is sound
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

/-- The `log` node over a sound float tree whose operand is at least `1` is sound. -/
theorem SyntaxTree.isSound_logFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hI : 1 ≤ toReal (t.value.inf 0) ∧ toReal (t.value.inf 0) ≤ 2 ^ p / 2)
    (hv : toReal ((Float.Interval.log p k t.value).sup 0) ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.logFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.log_outer p k _ (Fin.forall_fin_one.2 hI))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanLogFloat_sound p _ _ (zero_lt_one.trans_le hI.1) hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

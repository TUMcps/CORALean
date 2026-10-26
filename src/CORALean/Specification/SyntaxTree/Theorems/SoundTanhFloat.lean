module

public import CORALean.ContSet.Interval.Float.Theorems.TanhOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanTanhFloatSound

@[expose] public section

/-!
# `tanh` of a sound float tree is sound

The node `tanh` builds over a sound float tree is sound: its interval encloses the hyperbolic
tangent: `Interval.tanh` encloses the hyperbolic tangent of the operand and `funHanTanhFloat_sound`
gives the `funHan`.

## Inputs
* `p` – precision of the exponential
* `k` – bisection steps of the logarithm

## Hypotheses
* `h` – the operand tree is sound
* `hI` – the operand interval stays within the range of the exponential
* `hv` – the node's interval stays below one, within the range of the logarithm

## Conclusion
* the `tanh` tree is sound
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

/-- The `tanh` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_tanhFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hI : toReal (t.value.sup 0) ≤ 2 ^ p / 2)
    (hv : toReal ((Float.Interval.tanh p t.value).sup 0) < 1 ∧ (1 + toReal ((Float.Interval.tanh p
      t.value).sup 0)) / (1 - toReal ((Float.Interval.tanh p t.value).sup 0)) ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.tanhFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.tanh_outer p _ (Fin.forall_fin_one.2 hI))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanTanhFloat_sound p k _ _ hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

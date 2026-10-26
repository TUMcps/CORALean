module

public import CORALean.ContSet.Interval.Float.Theorems.AtanhOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanhFloatSound

@[expose] public section

/-!
# `atanh` of a sound float tree is sound

The node `atanh` builds over a sound float tree is sound: its interval encloses the inverse
hyperbolic tangent: `Interval.atanh` encloses the inverse hyperbolic tangent of the operand and
`funHanAtanhFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection steps

## Hypotheses
* `h` – the operand tree is sound
* `hI` – the operand interval stays inside `(-1,1)` within the range of the logarithm
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one
* `hv` – the node's interval stays within the range of the exponential

## Conclusion
* the `atanh` tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `atanh` node over a sound float tree whose operand stays inside `(-1,1)` is sound. -/
theorem SyntaxTree.isSound_atanhFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hI : 0 < toReal (subDown one (t.value.sup 0)) ∧ 0 < toReal (subDown one (neg (t.value.inf 0)))
      ∧ (0 ≤ toReal (t.value.inf 0) → (1 + toReal (t.value.inf 0)) / (1 - toReal (t.value.inf 0)) ≤
      2 ^ p / 2))
    (hd₁ : -1 < toReal (t.value.inf 0)) (hd₂ : toReal (t.value.sup 0) < 1)
    (hv : toReal ((Float.Interval.atanh p k t.value).sup 0) ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.atanhFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.atanh_outer p k _ (Fin.forall_fin_one.2 hI))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAtanhFloat_sound p _ _ hd₁ hd₂ hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

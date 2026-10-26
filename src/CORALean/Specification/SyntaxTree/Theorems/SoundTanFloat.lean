module

public import CORALean.ContSet.Interval.Float.Theorems.TanOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanTanFloatSound

@[expose] public section

/-!
# `tan` of a sound float tree is sound

The node `tan` builds over a sound float tree is sound: its interval encloses the tangent:
`Interval.tan` encloses the tangent of the operand and `funHanTanFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of `pi` and of the tangent
* `k` – Newton steps

## Hypotheses
* `h` – the operand tree is sound
* `hI` – the operand interval stays inside `(-pi/2, pi/2)`
* `hc` – the cosine of both ends is certified positive

## Conclusion
* the `tan` tree is sound
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

/-- The `tan` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_tanFloat [Float.ToRat 𝕋] (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hI : -(Real.pi / 2) < toReal (t.value.inf 0) ∧ toReal (t.value.sup 0) < Real.pi / 2)
    (hc : 0 < toReal (cosDown p (t.value.inf 0)) ∧ 0 < toReal (cosDown p (t.value.sup 0))) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.tanFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.tan_outer p _ (Fin.forall_fin_one.2 hI) (Fin.forall_fin_one.2 hc))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanTanFloat_sound p k _ _ hI.1 hI.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

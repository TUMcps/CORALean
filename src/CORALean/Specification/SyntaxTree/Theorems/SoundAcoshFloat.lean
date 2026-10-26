module

public import CORALean.ContSet.Interval.Float.Theorems.AcoshOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcoshFloatSound

@[expose] public section

/-!
# `acosh` of a sound float tree is sound

The node `acosh` builds over a sound float tree is sound: its interval encloses the inverse
hyperbolic cosine: `Interval.acosh` encloses the inverse hyperbolic cosine of the operand and
`funHanAcoshFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps

## Hypotheses
* `h` – the operand tree is sound
* `hd` – the operand interval stays above one
* `hn` – twice its lower bound stays within the range of the logarithm
* `hv` – the node's interval stays within the range of the exponential

## Conclusion
* the `acosh` tree is sound
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

/-- The `acosh` node over a sound float tree whose operand is at least `1` is sound. -/
theorem SyntaxTree.sound_acoshFloat (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t)
    (hd : 1 ≤ toReal (t.value.inf 0)) (hn : 2 * toReal (t.value.inf 0) ≤ 2 ^ p / 2)
    (hv : toReal ((Float.Interval.acosh p k t.value).sup 0) ≤ 2 ^ p / 2) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.acoshFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.acosh_outer p k _ (Fin.forall_fin_one.2 ⟨hd, hn⟩))
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanAcoshFloat_sound p _ _ hd hv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

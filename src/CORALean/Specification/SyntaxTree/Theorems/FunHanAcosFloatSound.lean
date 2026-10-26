module

public import CORALean.ContSet.Interval.Float.Theorems.CosOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aaux_cos_` over floats is sound

`SyntaxTree.funHanAcosFloat` keeps every solution of `acos s ∈ int` for an operand inside `[-1,1]`:
`s` is the cosine of its inverse, which lies in `int` cut to the nonnegative reals, and
`Interval.cos` encloses the cosine.

## Inputs
* `p` – precision of the cosine
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one

## Conclusion
* the float inverse of the inverse cosine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_cos_` over floats is sound for `acos` on an operand inside `[-1,1]`. -/
theorem SyntaxTree.funHanAcosFloat_sound (p : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd₁ : -1 ≤ toReal (prev.inf 0)) (hd₂ : toReal (prev.sup 0) ≤ 1) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.acos.fn prev v
      (SyntaxTree.funHanAcosFloat p) := by -- --- PROOF ---
  intro int _ s hs hi
  have hi' : int.contains (Real.arccos s) := hi
  have hnd : ¬ ltStrict (int.sup 0) zero = true := fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_zero] at this
    linarith [hi'.2, Real.arccos_nonneg s]
  have hcut : Float.SyntaxTree.Dom.contains
      (⟨fun _ => maximum (int.inf 0) zero, fun _ => int.sup 0⟩ : Float.SyntaxTree.Dom 𝕋)
      (Real.arccos s) :=
    ⟨by simp only [toReal_maximum, toReal_zero]; exact max_le hi'.1 (Real.arccos_nonneg s), hi'.2⟩
  have h := SyntaxTree.contains_of_outerFloat (f := Real.cos) (Float.Interval.cos_outer p _) hcut
  rw [Real.cos_arccos (hd₁.trans hs.1) (hs.2.trans hd₂)] at h
  unfold SyntaxTree.funHanAcosFloat
  rw [if_neg hnd]
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

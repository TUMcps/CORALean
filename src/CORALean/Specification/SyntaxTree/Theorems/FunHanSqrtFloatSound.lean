module

public import CORALean.ContSet.Interval.Float.Theorems.PowerOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrtFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_sqrt_` over floats is sound

`SyntaxTree.funHanSqrtFloat` keeps every solution of `sqrt s ∈ int` with `s ≥ 0`: `s` is the square
of its root, which lies in `int` cut to the nonnegative reals, and `Interval.power` encloses the
square.

## Inputs
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd` – the operand interval is nonnegative

## Conclusion
* the float inverse of the square root keeps every solution
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

/-- `aux_sqrt_` over floats is sound for `sqrt` on a nonnegative operand. -/
theorem SyntaxTree.funHanSqrtFloat_sound (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd : 0 ≤ toReal (prev.inf 0)) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.sqrt.fn prev v
      SyntaxTree.funHanSqrtFloat := by -- --- PROOF ---
  intro int _ s hs hi
  have hs0 : 0 ≤ s := hd.trans hs.1
  have hi' : int.contains (Real.sqrt s) := hi
  have hnd : ¬ ltStrict (int.sup 0) zero = true := fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_zero] at this
    linarith [hi'.2, Real.sqrt_nonneg s]
  have hcut : Float.SyntaxTree.Dom.contains
      (⟨fun _ => maximum (int.inf 0) zero, fun _ => int.sup 0⟩ : Float.SyntaxTree.Dom 𝕋)
      (Real.sqrt s) :=
    ⟨by simp only [toReal_maximum, toReal_zero]; exact max_le hi'.1 (Real.sqrt_nonneg s), hi'.2⟩
  have h := SyntaxTree.contains_of_outerFloat (f := fun x : ℝ => x ^ 2)
    (Float.Interval.power_outer _ 2) hcut
  simp only [Real.sq_sqrt hs0] at h
  unfold SyntaxTree.funHanSqrtFloat
  rw [if_neg hnd]
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

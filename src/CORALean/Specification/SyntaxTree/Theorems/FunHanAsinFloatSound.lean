module

public import CORALean.ContSet.Interval.Float.Theorems.SinOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# `aaux_sin_` over floats is sound

`SyntaxTree.funHanAsinFloat` keeps every solution of `asin s ∈ int` for an operand inside `[-1,1]`:
`s` is the sine of its inverse, which lies in `int`, or in the range of the inverse sine where the
cut is certified, and `Interval.sin` encloses the sine.

## Inputs
* `p` – precision of the sine and of `pi`
* `k` – Newton steps of `pi`
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one

## Conclusion
* the float inverse of the inverse sine keeps every solution
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

/-- `aaux_sin_` over floats is sound for `asin` on an operand inside `[-1,1]`. -/
theorem SyntaxTree.funHanAsinFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd₁ : -1 ≤ toReal (prev.inf 0)) (hd₂ : toReal (prev.sup 0) ≤ 1) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.asin.fn prev v
      (SyntaxTree.funHanAsinFloat p k) := by -- --- PROOF ---
  intro int _ s hs hi
  have hi' : int.contains (Real.arcsin s) := hi
  have hπ := SyntaxTree.piFloat_contains (𝕋 := 𝕋) p k
  have hh : Real.pi / 2 ≤ toReal (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup) := by
    rw [toReal_half]; linarith [hπ.2]
  have hlo := Real.neg_pi_div_two_le_arcsin s
  have hhi := Real.arcsin_le_pi_div_two s
-- the upper bound is not below the range of the inverse sine
  have hnd : ¬ ltStrict (int.sup 0) (neg (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup)) = true :=
    fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_neg] at this
    linarith [hi'.2]
-- the cut target holds the inverse sine
  have hcut : Float.SyntaxTree.Dom.contains
      (if ltStrict (int.inf 0) (neg (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup)) = true then
        (⟨fun _ => neg (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup),
          fun _ => half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup⟩ : Float.SyntaxTree.Dom 𝕋)
      else int) (Real.arcsin s) := by
    split_ifs
    · exact ⟨by simp only [toReal_neg]; linarith, hh.trans' hhi⟩
    · exact hi'
  have h := SyntaxTree.contains_of_outerFloat (f := Real.sin) (Float.Interval.sin_outer p _) hcut
  rw [Real.sin_arcsin (hd₁.trans hs.1) (hs.2.trans hd₂)] at h
  unfold SyntaxTree.funHanAsinFloat
  dsimp only
  rw [if_neg hnd]
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

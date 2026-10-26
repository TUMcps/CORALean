module

public import CORALean.ContSet.Interval.Float.Theorems.CoshOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcoshFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aaux_cosh_` over floats is sound

`SyntaxTree.funHanAcoshFloat` keeps every solution of `acosh s ∈ int` for an operand at least `1`:
`s` is the hyperbolic cosine of its inverse, which lies in `int` cut to the nonnegative reals, and
`Interval.cosh` encloses it. The target lies inside the node's interval, whose upper bound is within
the range of the float exponential.

## Inputs
* `p` – precision of the hyperbolic cosine
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd` – the operand interval stays above one
* `hv` – the value interval stays within the range of the exponential

## Conclusion
* the float inverse of the inverse hyperbolic cosine keeps every solution
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

/-- `aaux_cosh_` over floats is sound for `acosh` on an operand at least `1`. -/
theorem SyntaxTree.funHanAcoshFloat_sound (p : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd : 1 ≤ toReal (prev.inf 0)) (hv : toReal (v.sup 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.acosh.fn prev v
      (SyntaxTree.funHanAcoshFloat p) := by -- --- PROOF ---
  intro int hw s hs hi
  have hs1 : 1 ≤ s := hd.trans hs.1
  have hi' : int.contains (Real.arcosh s) := hi
  have hn : 0 ≤ Real.arcosh s := Real.arcosh_nonneg hs1
  -- an upper bound below zero would exclude the inverse
  have hnd : ¬ ltStrict (int.sup 0) zero = true := fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_zero] at this
    linarith [hi'.2]
  -- the target cut to the nonnegative reals holds the inverse
  set cut : Float.SyntaxTree.Dom 𝕋 := ⟨fun _ => maximum (int.inf 0) zero, fun _ => int.sup 0⟩
    with hcdef
  have hcut : cut.contains (Real.arcosh s) :=
    ⟨by simp only [hcdef, toReal_maximum, toReal_zero]; exact max_le hi'.1 hn, hi'.2⟩
  -- its bounds are within the range of the exponential
  have hI : ∀ i, toReal (cut.sup i) ≤ 2 ^ p / 2 ∧ -toReal (cut.inf i) ≤ 2 ^ p / 2 := fun i => by
    refine ⟨hw.2.trans hv, ?_⟩
    simp only [hcdef, toReal_maximum, toReal_zero]
    have : (0 : ℝ) ≤ 2 ^ p / 2 := by positivity
    linarith [le_max_right (toReal (int.inf 0)) 0]
  -- `cosh` encloses the hyperbolic cosine of the inverse
  have h := SyntaxTree.contains_of_outerFloat (f := Real.cosh)
    (Float.Interval.cosh_outer p cut hI) hcut
  rw [Real.cosh_arcosh hs1] at h
  unfold SyntaxTree.funHanAcoshFloat
  rw [if_neg hnd]
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

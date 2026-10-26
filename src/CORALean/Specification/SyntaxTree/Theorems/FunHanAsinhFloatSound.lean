module

public import CORALean.ContSet.Interval.Float.Theorems.SinhOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinhFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aaux_sinh_` over floats is sound

`SyntaxTree.funHanAsinhFloat` keeps every solution of `asinh s ∈ int`: `s` is the hyperbolic sine of
its inverse, which `Interval.sinh` encloses. The target lies inside the node's interval, whose
bounds are within the range of the float exponential.

## Inputs
* `p` – precision of the hyperbolic sine
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hv` – the value interval stays within the range of the exponential

## Conclusion
* the float inverse of the inverse hyperbolic sine keeps every solution
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

/-- `aaux_sinh_` over floats is sound for `asinh`, for a node interval within the exponential's
range. -/
theorem SyntaxTree.funHanAsinhFloat_sound (p : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hv : toReal (v.sup 0) ≤ 2 ^ p / 2 ∧ -toReal (v.inf 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.asinh.fn prev v
      (SyntaxTree.funHanAsinhFloat p) := by -- --- PROOF ---
  intro int hw s hs hi
  have hi' : int.contains (Real.arsinh s) := hi
  have hI : ∀ i, toReal (int.sup i) ≤ 2 ^ p / 2 ∧ -toReal (int.inf i) ≤ 2 ^ p / 2 := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact ⟨hw.2.trans hv.1, by linarith [hw.1, hv.2]⟩
  have h := SyntaxTree.contains_of_outerFloat (Float.Interval.sinh_outer p int hI) hi'
  rw [Real.sinh_arsinh] at h
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

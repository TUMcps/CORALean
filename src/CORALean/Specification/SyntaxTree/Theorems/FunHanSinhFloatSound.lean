module

public import CORALean.ContSet.Interval.Float.Theorems.AsinhOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinhFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_sinh_` over floats is sound

`SyntaxTree.funHanSinhFloat` keeps every solution of `sinh s ∈ int`: `s` is the inverse hyperbolic
sine of its hyperbolic sine, which `Interval.asinh` encloses. The target lies inside the node's
interval, whose upper bound is within the range of the float logarithm.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hv` – the value interval stays within the range of the logarithm

## Conclusion
* the float inverse of the hyperbolic sine keeps every solution
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

/-- `aux_sinh_` over floats is sound for `sinh`, within the logarithm's range. -/
theorem SyntaxTree.funHanSinhFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hv : 2 * toReal (v.sup 0) + 1 ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.sinh.fn prev v
      (SyntaxTree.funHanSinhFloat p k) := by -- --- PROOF ---
  intro int hw s hs hi
  have hi' : int.contains (Real.sinh s) := hi
  have hI : ∀ i, 0 ≤ toReal (int.inf i) → 2 * toReal (int.inf i) + 1 ≤ 2 ^ p / 2 := fun i _ => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    linarith [hi'.1, hi'.2, hw.2]
  have h := SyntaxTree.contains_of_outerFloat (Float.Interval.asinh_outer p k int hI) hi'
  rw [Real.arsinh_sinh] at h
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

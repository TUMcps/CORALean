module

public import CORALean.ContSet.Interval.Float.Theorems.TanhOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanhFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aaux_tanh_` over floats is sound

`SyntaxTree.funHanAtanhFloat` keeps every solution of `atanh s ∈ int` for an operand inside
`(-1,1)`: `s` is the hyperbolic tangent of its inverse, which `Interval.tanh` encloses. The target
lies inside the node's interval, whose upper bound is within the range of the float exponential.

## Inputs
* `p` – precision of the hyperbolic tangent
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd₁` – the operand interval stays above minus one
* `hd₂` – the operand interval stays below one
* `hv` – the value interval stays within the range of the exponential

## Conclusion
* the float inverse of the inverse hyperbolic tangent keeps every solution
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

/-- `aaux_tanh_` over floats is sound for `atanh` on an operand inside `(-1,1)`. -/
theorem SyntaxTree.funHanAtanhFloat_sound (p : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd₁ : -1 < toReal (prev.inf 0)) (hd₂ : toReal (prev.sup 0) < 1)
    (hv : toReal (v.sup 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.atanh.fn prev v
      (SyntaxTree.funHanAtanhFloat p) := by -- --- PROOF ---
  intro int hw s hs hi
  have hi' : int.contains (Real.artanh s) := hi
  have hI : ∀ i, toReal (int.sup i) ≤ 2 ^ p / 2 := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact hw.2.trans hv
  have hs1 : s ∈ Set.Ioo (-1) 1 := ⟨hd₁.trans_le hs.1, hs.2.trans_lt hd₂⟩
  have h := SyntaxTree.contains_of_outerFloat (Float.Interval.tanh_outer p int hI) hi'
  rw [Real.tanh_artanh hs1] at h
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

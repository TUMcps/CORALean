module

public import CORALean.ContSet.Interval.Float.Theorems.ExpOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanLogFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_log_` over floats is sound

`SyntaxTree.funHanLogFloat` keeps every solution of `log s ∈ int` for a positive operand: `s` is the
exponential of its logarithm, which `Interval.exp` encloses. The target lies inside the node's
interval, whose upper bound is within the range of the float exponential.

## Inputs
* `p` – precision of the exponential
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd` – the operand interval is positive
* `hv` – the value interval stays within the range of the exponential

## Conclusion
* the float inverse of the logarithm keeps every solution
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

/-- `aux_log_` over floats is sound for `log` on a positive operand. -/
theorem SyntaxTree.funHanLogFloat_sound (p : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd : 0 < toReal (prev.inf 0)) (hv : toReal (v.sup 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.log.fn prev v
      (SyntaxTree.funHanLogFloat p) := by -- --- PROOF ---
  intro int hw s hs hi
  have hs0 : 0 < s := hd.trans_le hs.1
  have hi' : int.contains (Real.log s) := hi
  have hI : ∀ i, toReal (int.sup i) ≤ 2 ^ p / 2 := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact hw.2.trans hv
  have h := SyntaxTree.contains_of_outerFloat (Float.Interval.exp_outer p int hI) hi'
  rw [Real.exp_log hs0] at h
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

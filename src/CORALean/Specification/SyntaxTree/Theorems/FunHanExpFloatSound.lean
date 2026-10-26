module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanExpFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_exp_` over floats is sound

`SyntaxTree.funHanExpFloat` keeps every real solution of `exp s ∈ int`: a lower bound `logDown` of a
bound certified at least `1` is below the logarithm of the bound, which is below `s`, and `logUp` of
a certified positive bound is above. The range of `logDown` is the node's: the target lies inside
the node's interval, whose upper bound is at most `2^p / 2`.

## Inputs
* `p` – precision of the exponentials
* `k` – bisection steps of the logarithms
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hv` – the value interval stays within the range of the exponential

## Conclusion
* the float inverse of the exponential keeps every solution
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

/-- `aux_exp_` over floats is sound for `exp`, within the exponential's range. -/
theorem SyntaxTree.funHanExpFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hv : toReal (v.sup 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.exp.fn prev v
      (SyntaxTree.funHanExpFloat p k) := by -- --- PROOF ---
  intro int hw s hs hi
  have h : toReal (int.inf 0) ≤ Real.exp s ∧ Real.exp s ≤ toReal (int.sup 0) := hi
  have hpos : 0 < toReal (int.sup 0) := (Real.exp_pos s).trans_le h.2
  have hnd : ¬ ltStrict (int.sup 0) zero = true := fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_zero] at this
    linarith
  -- the cut bound is at most `exp s`
  have hlo : toReal (maximum (int.inf 0) zero) ≤ Real.exp s := by
    rw [toReal_maximum, toReal_zero]
    exact max_le h.1 (Real.exp_pos s).le
-- the lower bound is `logDown` of the cut lower end where certified
  unfold SyntaxTree.funHanExpFloat
  rw [if_neg hnd]
  refine ⟨_, rfl, SyntaxTree.meet_containsFloat hs (show _ ∧ _ from ⟨?_, ?_⟩)⟩
  · by_cases hc : le one (maximum (int.inf 0) zero) = true
    · rw [if_pos hc]
      have h1 : 1 ≤ toReal (maximum (int.inf 0) zero) := by
        have := toReal_le_of_le hc
        rwa [toReal_one] at this
      refine (logDown_le p k _ h1 (hlo.trans (h.2.trans hw.2 |>.trans hv))).trans ?_
      calc Real.log (toReal (maximum (int.inf 0) zero)) ≤ Real.log (Real.exp s) :=
            Real.log_le_log (by linarith) hlo
        _ = s := Real.log_exp s
    · rw [if_neg hc]; exact hs.1
-- the upper bound is `logUp` of the upper end where certified
  · by_cases hc : ltStrict zero (int.sup 0) = true
    · rw [if_pos hc]
      have hp : 0 < toReal (int.sup 0) := by
        have := toReal_lt_of_ltStrict hc
        rwa [toReal_zero] at this
      calc s = Real.log (Real.exp s) := (Real.log_exp s).symm
        _ ≤ Real.log (toReal (int.sup 0)) := Real.log_le_log (Real.exp_pos s) h.2
        _ ≤ _ := le_logUp p k _ hp
    · rw [if_neg hc]; exact hs.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanhFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_tanh_` over floats is sound

`SyntaxTree.funHanTanhFloat` keeps every solution of `tanh s ∈ int`: `s` is the inverse hyperbolic
tangent of its hyperbolic tangent, which lies strictly inside `(-1,1)` and above the cut lower
bound; a bound is mapped only where it is certified inside the interval, so `atanhDown` and
`atanhUp` bound it. The ratio `(1+x)/(1-x)` of the lower bound stays within the range of the float
logarithm because the target lies inside the node's interval.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection steps of the logarithm
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hv` – the value interval stays below one, with its ratio within the range of the logarithm

## Conclusion
* the float inverse of the hyperbolic tangent keeps every solution
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

/-- `aux_tanh_` over floats is sound for `tanh`, within the logarithm's range. -/
theorem SyntaxTree.funHanTanhFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hv : toReal (v.sup 0) < 1 ∧
      (1 + toReal (v.sup 0)) / (1 - toReal (v.sup 0)) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.tanh.fn prev v
      (SyntaxTree.funHanTanhFloat p k) := by -- --- PROOF ---
  intro int hw s hs hi
  have hi' : int.contains (Real.tanh s) := hi
  have ht1 := Real.tanh_lt_one s
  have ht2 := Real.neg_one_lt_tanh s
  have hlo : toReal (maximum (int.inf 0) (neg one)) ≤ Real.tanh s := by
    rw [toReal_maximum, toReal_neg, toReal_one]; exact max_le hi'.1 ht2.le
  have hhi : Real.tanh s ≤ toReal (minimum (int.sup 0) one) := by
    rw [toReal_minimum, toReal_one]; exact le_min hi'.2 ht1.le
-- the lower bound is the inverse hyperbolic tangent of the cut lower end where certified
  unfold SyntaxTree.funHanTanhFloat
  dsimp only
  refine ⟨_, rfl, SyntaxTree.meet_containsFloat hs (show _ ∧ _ from ⟨?_, ?_⟩)⟩
  · by_cases hc : ltStrict zero (subDown one (neg (maximum (int.inf 0) (neg one)))) = true
    · rw [if_pos hc]
      have h2 := toReal_lt_of_ltStrict hc
      rw [toReal_zero] at h2
      -- the lower bound of the ratio
      have hD := Float.subDown_le_sub (one : 𝕋) (neg (maximum (int.inf 0) (neg one)))
      rw [toReal_one, toReal_neg] at hD
      have hgt : -1 < toReal (maximum (int.inf 0) (neg one)) := by linarith
      refine (Float.atanhDown_le p k _ (hlo.trans_lt ht1) h2 ?_).trans ?_
      · intro h0
        have hvs : toReal (maximum (int.inf 0) (neg one)) ≤ toReal (v.sup 0) :=
          hlo.trans (hi'.2.trans hw.2)
        have hx1 : toReal (maximum (int.inf 0) (neg one)) < 1 := hlo.trans_lt ht1
        refine le_trans ?_ hv.2
        exact div_le_div₀ (by linarith [hv.1]) (by linarith) (by linarith [hv.1]) (by linarith)
      · calc Real.artanh (toReal (maximum (int.inf 0) (neg one)))
            ≤ Real.artanh (Real.tanh s) := Real.artanh_le_artanh hgt ht1 hlo
          _ = s := Real.artanh_tanh s
    · rw [if_neg hc]; exact hs.1
-- the upper bound is the inverse hyperbolic tangent of the cut upper end where certified
  · by_cases hc : ltStrict zero (subDown one (minimum (int.sup 0) one)) = true
    · rw [if_pos hc]
      have h2 := toReal_lt_of_ltStrict hc
      rw [toReal_zero] at h2
      have hD := Float.subDown_le_sub (one : 𝕋) (minimum (int.sup 0) one)
      rw [toReal_one] at hD
      refine le_trans ?_ (Float.le_atanhUp p k _ (ht2.trans_le hhi) (by exact h2))
      calc s = Real.artanh (Real.tanh s) := (Real.artanh_tanh s).symm
        _ ≤ Real.artanh (toReal (minimum (int.sup 0) one)) :=
            Real.artanh_le_artanh ht2 (by linarith) hhi
    · rw [if_neg hc]; exact hs.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

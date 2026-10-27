module

public import CORALean.Specification.STL.Definitions.MILPEncoding

@[expose] public section

/-!
# A threshold under the robust unbounded until

[1, Sec. V (correctness)] encodes the unbounded until with `max` and `min` along the recursion
of [1, Sec. IV-B.3 (until)]. In its non-strict reading, `m ≤ r_i` iff the Boolean recursion holds
at `i` for the predicates `m ≤ r^{φ₁}` and `m ≤ r^{φ₂}`: the step that carries every Boolean fact
about the encoding over to the robust one.

## Inputs
* `N` – horizon
* `A` – left operand robustness
* `B` – right operand robustness
* `m` – threshold

## Hypotheses
* none

## Conclusion
* the threshold is below the robust until iff the until holds for the thresholds

## References

* [1] [V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia.
      "Model Predictive Control with Signal Temporal Logic Specifications". 53rd IEEE Conference on
      Decision and Control, 2014.](../../../../../references/2014/raman-cdc-mpc-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.le_untilRob_nonstrict_iff {N : ℕ} {A B : ℕ → ℝ} (m : ℝ) : -- --- CONCL ---
    ∀ i, (m ≤ STL.untilRob N true A B i ↔
      STL.IsUntilEnc N true (fun s => m ≤ A s) (fun s => m ≤ B s) i) := by -- --- PROOF ---
  intro i
  induction hk : N - i using Nat.strong_induction_on generalizing i with
  | _ k ih =>
  rw [STL.untilRob, STL.IsUntilEnc]
  simp only [if_true]
  by_cases hiN : i < N
  · -- `max` and `min` are `∨` and `∧` above a threshold
    rw [if_pos hiN, if_pos hiN, le_max_iff, le_min_iff, le_min_iff,
      ih (N - (i + 1)) (by omega) (i + 1) rfl]
  · rw [if_neg hiN, if_neg hiN, le_min_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.STLInterval.Operations.MinkDiffCora
public import CORALean.Specification.STLInterval.Definitions.FieldsContainsPoint

@[expose] public section

/-!
# CORA's `minkDiff` loses the unbounded upper end

`minkDiff([0,∞),[0,∞))` should be `[0,∞)`: `t + [0,∞) ⊆ [0,∞)` for every `t ≥ 0`. CORA computes
`ub = Inf - Inf = NaN`, so the object it returns contains no `t > 0`. See
`STLInterval.minkDiffCora`; `STLInterval.minkDiff` takes the upper bound `+∞`, and `set_minkDiff`
is the documented set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.minkDiffCora_counterexample :
    ∃ (I J : STLInterval) (t : ℝ), (0 ≤ t ∧ ∀ y ∈ J.set, t + y ∈ I.set) ∧
      ¬ STLInterval.fieldsContainsPoint (STLInterval.minkDiffCora I J) t := by -- --- PROOF ---
  -- the operands are `[0, ∞)`, `stlInterval(0,inf)`
  let I : STLInterval := .nonempty 0 ⊤ true false (by simp) (by simp) (Or.inl (by simp))
  refine ⟨I, I, 1, ⟨zero_le_one, fun y hy => ?_⟩, ?_⟩
  · -- `1 + y ≥ 0` for `y ≥ 0`
    have hy0 : 0 ≤ y := by
      rcases hy.1 with h0 | ⟨_, h0⟩
      · exact (EReal.coe_pos.1 h0).le
      · exact (EReal.coe_eq_zero.1 h0.symm).ge
    exact ⟨Or.inl (EReal.coe_pos.2 (by linarith)), Or.inl (EReal.coe_lt_top _)⟩
  · simp [STLInterval.minkDiffCora, STLInterval.fieldsContainsPoint, I]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

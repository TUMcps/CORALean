module

public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Definitions.FieldsContainsPoint
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `minkDiff`, as printed

`@stlInterval/minkDiff.m` with `ub = obj.upper - sub.upper` as MATLAB computes it: `Inf - Inf` is
`NaN`, which the constructor `stlInterval(lb,ub,lc,rc)` keeps (`abs(NaN) == inf`, `lb > NaN` and
`lb == NaN` are false), so for two unbounded operands the object has `upper = NaN`. Elsewhere the
result is that of `STLInterval.minkDiff`. See `STLInterval.minkDiffCora_counterexample`.

# CORA's `minkDiff` loses the unbounded upper end

`minkDiff([0,∞),[0,∞))` should be `[0,∞)`: `t + [0,∞) ⊆ [0,∞)` for every `t ≥ 0`. CORA computes
`ub = Inf - Inf = NaN`, so the object it returns contains no `t > 0`. See
`STLInterval.minkDiffCora`; `STLInterval.minkDiff` takes the upper bound `+∞`, and `set_minkDiff`
is the documented set.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's Minkowski difference omits a time that belongs to it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- The model: CORA's code as printed, kept only to be refuted.
noncomputable def STLInterval.minkDiffCora :
    STLInterval ℝ → STLInterval ℝ → Option (STLInterval.Fields ℝ)
  | _, .empty => fieldsOf (stlInterval 0 ⊤ true false (by simp))
  | .empty, _ => none
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let lb := l₁ - l₂
    let lc := lc₁ || !lc₂
    let rc := rc₁ || !rc₂
    match u₁, u₂ with
    -- `Inf - Inf` is `NaN`
    | none, none => if lb < 0 then some ⟨0, none, true, rc⟩ else some ⟨lb, none, lc, rc⟩
    -- `upper - Inf` is `-Inf`, and the constructor makes `stlInterval()`
    | some _, none => none
    | _, _ => if h : lb < 0 then fieldsOf (stlInterval 0 (subUpTop u₁ u₂) true rc (by simp))
      else fieldsOf (stlInterval lb (subUpTop u₁ u₂) lc rc (by simpa using not_lt.1 h))


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.minkDiffCora_counterexample : -- --- CONCL ---
    ∃ (I J : STLInterval ℝ) (t : ℝ), (0 ≤ t ∧ ∀ y ∈ J.set, t + y ∈ I.set) ∧
      ¬ STLInterval.fieldsContainsPoint (STLInterval.minkDiffCora I J) t := by -- --- PROOF ---
  -- the operands are `[0, ∞)`, `stlInterval(0,inf)`
  let I : STLInterval ℝ := .nonempty 0 ⊤ true false (fun _ => rfl) (Or.inl (by simp)) (by simp)
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

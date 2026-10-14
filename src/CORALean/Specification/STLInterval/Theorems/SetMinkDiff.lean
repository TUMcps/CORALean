module

public import CORALean.Specification.STLInterval.Operations.MinkDiff
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetMinkDiff
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `minkDiff` denotes the Minkowski difference

`minkDiff(I, J)` denotes the times `t ≥ 0` with `t + J ⊆ I`, as its documentation says.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minkDiff` denotes the times `t ≥ 0` with `t + J ⊆ I`. -/
theorem STLInterval.set_minkDiff (I J : STLInterval) :
    (I.minkDiff J).set = {t | 0 ≤ t ∧ ∀ y ∈ J.set, t + y ∈ I.set} := by -- --- PROOF ---
  cases J with
  | empty =>
    -- an empty `J` leaves every time `t ≥ 0`
    simp only [STLInterval.minkDiff]
    rw [set_stlInterval]
    ext t
    simp only [rawSet, STLInterval.set, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      false_imp_iff, implies_true, and_true]
    simp only [EReal.coe_lt_top, true_or, and_true, true_and, EReal.coe_pos, le_iff_lt_or_eq]
    exact or_congr_right ⟨fun h => (EReal.coe_eq_zero.1 h.symm).symm, fun h => by rw [← h]; rfl⟩
  | nonempty l₂ u₂ lc₂ rc₂ d e f =>
    -- a nonempty `J` against an empty or a nonempty `I`
    cases I with
    | empty =>
      obtain ⟨y, hy⟩ := set_nonempty _ _ _ _ d e f
      ext t
      simp only [STLInterval.minkDiff, STLInterval.set, Set.mem_empty_iff_false, Set.mem_setOf_eq,
        false_iff, not_and]
      exact fun _ h => h y hy
    | nonempty l₁ u₁ lc₁ rc₁ a b c =>
      simp only [STLInterval.minkDiff]
      have h := rawSet_minkDiff (set_nonempty _ _ _ _ a b c)
        (set_nonempty _ _ _ _ d e f)
      show _ = {t | 0 ≤ t ∧ ∀ y ∈ rawSet l₂ u₂ lc₂ rc₂, t + y ∈ rawSet l₁ u₁ lc₁ rc₁}
      rw [h]
      split_ifs <;> exact set_stlInterval _ _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

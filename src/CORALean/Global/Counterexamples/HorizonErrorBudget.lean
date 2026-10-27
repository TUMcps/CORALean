module

public import CORALean.Global.HasSuperlinearDecrease
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Order.Lattice

@[expose] public section

/-!
# `Prop. 2` needs `ε_P(Δt)/Δt → 0`, not only Def. 1

[1, Prop. 2] concludes that, for `ε_P` decreasing superlinearly (Def. 1), a finite partition
of `[0, t_f]` has `ε_P`-errors summing below any `ε_{P,max} > 0`. Def. 1 compares `ε_P(φΔt)`
with `φ ε_P(Δt)` and a linear `ε_P(Δt) = Δt` meets it with equality, at every length. Its
errors over any partition of `[0, t_f]` then sum to exactly `t_f`, so the budget
`ε_{P,max} = t_f / 2` is never met.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a superlinearly decreasing error exists whose partitions never meet the budget

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] as printed: the linear `ε_P(Δt) = Δt` decreases superlinearly in the sense of
Def. 1, and no partition of `[0, 2]` keeps its errors below `1`. -/
theorem exists_finPartition_sum_particularError_le_counterexample : -- --- CONCL ---
    ∃ εP : ℝ → ℝ, (∀ Δt, HasSuperlinearDecrease (fun d => ({εP d} : Set ℝ)) Δt) ∧
      ¬ ∃ (M : ℕ) (Δt : Fin (M + 1) → ℝ), (∀ i, 0 < Δt i) ∧ (∑ i, Δt i = 2) ∧
        (∑ i, εP (Δt i) ≤ 1) := by -- --- PROOF ---
  refine ⟨id, fun Δt φ _ => ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨Δt, rfl, by simp [hx]⟩
  · rintro ⟨M, Δt, -, hsum, hle⟩
    simp only [id_eq] at hle
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

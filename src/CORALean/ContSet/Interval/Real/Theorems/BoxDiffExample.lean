import CORALean.ContSet.Interval.Real.Operations.BoxDiff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation

/-!
# The box difference of [1, Example 4]

`I₁ = [0, 4] × [0, 6]`, `I₂ = [2, 3] × [1, 3]`: the margins are `dₗ = (2, 1)` and
`dᵤ = (1, 3)`, the widest is `dᵤ(2) = 3`, so `I₁ \ I₂ ⊇ [0, 4] × ]3, 6]`, as printed.

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Example 4]: `[0, 4] × [0, 6]` minus `[2, 3] × [1, 3]` by [1, Prop. 3] is
`[0, 4] × ]3, 6]`. -/
theorem boxDiff_example :
    boxDiff ![0, 0] ![4, 6] ![2, 1] ![3, 3] =
      {x | x 0 ∈ Icc 0 4 ∧ x 1 ∈ Ioc 3 6} := by -- --- PROOF ---
  -- the second axis wins, `max(1, 3) > max(2, 1)`
  have harg : ((List.finRange 2).argmax fun i =>
      max ((![2, 1] - ![0, 0] : Fin 2 → ℝ) i) ((![4, 6] - ![3, 3] : Fin 2 → ℝ) i)) = some 1 := by
    simp [List.argmax, List.finRange_succ, List.argAux]
    norm_num
  ext x
  simp only [boxDiff]
  rw [harg]
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left', mem_setOf_eq, mem_Icc,
    Pi.le_def, Fin.forall_fin_two, mem_Ico, mem_Ioc, Pi.sub_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨⟨h0, -⟩, h2, -⟩, ⟨h4, -⟩ | ⟨-, h4, h5⟩⟩
    · exact absurd h4 (by norm_num)
    · exact ⟨⟨h0, h2⟩, h4, h5⟩
  · rintro ⟨⟨h0, h2⟩, h4, h5⟩
    exact ⟨⟨⟨h0, by linarith⟩, h2, h5⟩, Or.inr ⟨by norm_num, h4, h5⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

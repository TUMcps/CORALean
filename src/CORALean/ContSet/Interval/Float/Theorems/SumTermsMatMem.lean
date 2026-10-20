module

public import CORALean.ContSet.Interval.Float.Operations.SumTermsMat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter

@[expose] public section

/-!
# A sum of members is a member of the float interval-matrix sum

If `M k ∈ f k` for every `k < N`, then `∑_{k<N} M k ∈ sumTermsMat f N`: the start is the point
`0`, read exactly, and each `matPlus` holds the sum of a member of each summand.

## Inputs
* `f` – family of interval matrices
* `M` – family of real matrices
* `N` – number of terms

## Hypotheses
* `h` – each member lies in its box below `N`

## Conclusion
* the sum of the members lies in the term-wise float sum
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sum_mem_sumTermsMat (f : ℕ → Interval (Mat 𝕋 m n)) (M : ℕ → Mat ℝ m n)
    (N : ℕ) (h : ∀ k, k < N → M k ∈ (f k).construct) :
    ∑ k ∈ Finset.range N, M k ∈ (Interval.sumTermsMat f N).construct := by -- --- PROOF ---
  induction N with
  | zero =>
    -- the empty sum is `0`, the stored point `0` read as reals
    rw [Finset.sum_range_zero, Interval.sumTermsMat]
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩
  | succ N ih =>
    -- one more term, held by `matPlus`
    rw [Finset.sum_range_succ, Interval.sumTermsMat, Interval.materialiseMat_eq]
    exact Interval.matPlus_outer _ _ (ih fun k hk => h k (Nat.lt_succ_of_lt hk))
      (h N (Nat.lt_succ_self N))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

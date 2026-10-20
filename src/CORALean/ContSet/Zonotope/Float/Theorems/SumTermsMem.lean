module

public import CORALean.ContSet.Zonotope.Float.Operations.SumTerms
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A sum of members is a member of the float sum

If `v m ∈ f m` for every `m < N`, then `∑_{m<N} v m ∈ sumTerms f N`: the start is the point `0`,
read exactly, and each `plus` holds the sum of a member of each summand (`Zonotope.plus_outer`).

## Inputs
* `f` – zonotope per index
* `v` – member per index
* `N` – number of terms

## Hypotheses
* `h` – each member lies in its zonotope

## Conclusion
* sum of the members lies in the Minkowski sum
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sum_mem_sumTerms (f : ℕ → Zonotope (Vec 𝕋 n)) (v : ℕ → Vec ℝ n) (N : ℕ)
    (h : ∀ m, m < N → v m ∈ (f m).construct) : -- --- CONCL ---
    ∑ m ∈ Finset.range N, v m ∈ (Zonotope.sumTerms f N).construct := by -- --- PROOF ---
  induction N with
  | zero =>
    -- the empty sum is `0`, the stored point `0` read as reals
    rw [Finset.sum_range_zero, Zonotope.sumTerms, Zonotope.construct_point]
    refine Set.mem_singleton_iff.mpr (funext fun i => ?_)
    exact (toReal_zero (𝕋 := 𝕋)).symm
  | succ N ih =>
    -- one more term, held by `plus`
    rw [Finset.sum_range_succ, Zonotope.sumTerms, Zonotope.materialise_eq]
    exact Zonotope.plus_outer _ _ (Set.add_mem_add (ih fun m hm => h m (Nat.lt_succ_of_lt hm))
      (h N (Nat.lt_succ_self N)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

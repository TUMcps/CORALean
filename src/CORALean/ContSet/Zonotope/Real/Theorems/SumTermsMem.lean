import CORALean.ContSet.Zonotope.Real.Operations.SumTerms
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# A sum of members is a member of the sum

If `v m ∈ f m` for every `m < N`, then `∑_{m<N} v m ∈ sumTerms f N`: `plus` is exact [1], so
each step adds one member.

## References

* [1] `contDynamics/@linearSys/trajectoryError.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sum_mem_sumTerms (f : ℕ → Zonotope α) (v : ℕ → α) (N : ℕ)
    (h : ∀ m, m < N → v m ∈ (f m).construct) :
    ∑ m ∈ Finset.range N, v m ∈ (Zonotope.sumTerms f N).construct := by -- --- PROOF ---
  induction N with
  | zero =>
    -- the empty sum is `0`, the point `{0}`
    exact ⟨Fin.elim0, fun j => j.elim0, by simp [Zonotope.sumTerms, Zonotope.ofPoint]⟩
  | succ N ih =>
    -- one more term, absorbed by the exact `plus`
    rw [Finset.sum_range_succ, Zonotope.sumTerms, ← Zonotope.plus_exact]
    exact Set.add_mem_add (ih fun m hm => h m (Nat.lt_succ_of_lt hm)) (h N (Nat.lt_succ_self N))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

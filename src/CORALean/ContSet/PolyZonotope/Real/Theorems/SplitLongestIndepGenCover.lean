import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestIndepGen
import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitLongestGenUnion
import Mathlib.Tactic.Module

/-!
# The halves of `splitLongestIndepGen` cover the set

A coefficient `β ∈ [0,1]` of the halved generator is `(1 + β')/2` with `β' = 2β - 1 ∈ [-1,1]` in
the half whose centre is `c + g/2`, and `β ∈ [-1,0]` is `(β' - 1)/2` with `β' = 2β + 1` in the
other. Both halves also lie in the set, the same substitution read backwards; only the cover is
needed and stated.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The independent sum with one coefficient and one generator replaced. -/
theorem PolyZonotope.aux_sum_update_smul {q : ℕ} (β : Fin q → ℝ) (GI : Fin q → Vec ℝ n)
    (j : Fin q) (t : ℝ) (v : Vec ℝ n) :
    ∑ i, Function.update β j t i • Function.update GI j v i
      = t • v + ∑ i ∈ Finset.univ.erase j, β i • GI i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self, Function.update_self]
  exact congrArg _ (Finset.sum_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)])


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongestIndepGen_cover (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.splitLongestIndepGen.1.construct
      ∪ pZ.splitLongestIndepGen.2.construct := by -- --- PROOF ---
  unfold PolyZonotope.splitLongestIndepGen
  cases hm : (List.finRange pZ.q).argmax (fun i => ∑ c, pZ.GI i c ^ 2) with
  | none => exact Set.subset_union_left
  | some j =>
    rintro x ⟨a, β, ha, hβ, rfl⟩
    -- the halved generator's term, split off the independent sum
    have hsplit : ∑ i, β i • pZ.GI i = β j • pZ.GI j + ∑ i ∈ Finset.univ.erase j, β i • pZ.GI i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    have hb := abs_le.mp (hβ j)
    by_cases h0 : 0 ≤ β j
    · -- a non-negative coefficient lies in the half with centre `c + g/2`, at `2β - 1`
      have hβ' : ∀ i : Fin pZ.q, |Function.update β j (2 * β j - 1) i| ≤ 1 := fun i => by
        by_cases hi : i = j
        · subst hi
          rw [Function.update_self, abs_le]
          constructor <;> linarith
        · rw [Function.update_of_ne hi]; exact hβ i
      refine Or.inl ⟨a, Function.update β j (2 * β j - 1), ha, hβ', ?_⟩
      show _ = pZ.c + (2 : ℝ)⁻¹ • pZ.GI j + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        + ∑ i, Function.update β j (2 * β j - 1) i
          • Function.update pZ.GI j ((2 : ℝ)⁻¹ • pZ.GI j) i
      rw [PolyZonotope.aux_sum_update_smul, hsplit]
      module
    · -- a negative one in the half with centre `c - g/2`, at `2β + 1`
      have hβ' : ∀ i : Fin pZ.q, |Function.update β j (2 * β j + 1) i| ≤ 1 := fun i => by
        by_cases hi : i = j
        · subst hi
          rw [Function.update_self, abs_le]
          constructor <;> linarith
        · rw [Function.update_of_ne hi]; exact hβ i
      refine Or.inr ⟨a, Function.update β j (2 * β j + 1), ha, hβ', ?_⟩
      show _ = pZ.c - (2 : ℝ)⁻¹ • pZ.GI j + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        + ∑ i, Function.update β j (2 * β j + 1) i
          • Function.update pZ.GI j ((2 : ℝ)⁻¹ • pZ.GI j) i
      rw [PolyZonotope.aux_sum_update_smul, hsplit]
      module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

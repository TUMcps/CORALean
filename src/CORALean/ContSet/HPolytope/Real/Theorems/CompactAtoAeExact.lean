module

public import CORALean.ContSet.HPolytope.Real.Operations.CompactAtoAe
public import CORALean.ContSet.HPolytope.Real.Theorems.AtoAeStateSpec
public import CORALean.ContSet.HPolytope.Real.Theorems.MoveToEqConstruct
public import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact

@[expose] public section

/-!
# `compactAtoAe` denotes the same set, exactly

A pair `aᵀx ≤ b`, `-aᵀx ≤ -b` is the equality `aᵀx = b`, and the equalities appended by the loop
imply the rows that were moved.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactAtoAe_exact (P : HPolytope (Vec ℝ n)) :
    P.compactAtoAe.construct = P.construct := by -- --- PROOF ---
  rw [← P.normalizeRows_exact]
  unfold HPolytope.compactAtoAe
  generalize P.normalizeRows = Q
  obtain ⟨hadd, hmov⟩ := Q.atoAeState_spec
  simp only [HPolytope.moveToEq_construct, Finset.mem_filter, Finset.mem_univ, true_and]
  ext x
  simp only [Set.mem_setOf_eq, HPolytope.construct]
  constructor
  · -- the moved rows are implied by the appended equalities
    rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, h2⟩
    by_cases hi : i ∈ Q.atoAeState.1
    · obtain ⟨k, hk, hik⟩ := hmov i hi
      have hkx := h3 k hk
      rcases hik with rfl | ⟨hA, hb⟩
      · exact hkx.le
      · rw [hA, hb]
        simp [hkx]
    · exact h1 i hi
  · -- an appended equality is the pair of inequalities
    rintro ⟨h1, h2⟩
    refine ⟨fun i _ => h1 i, h2, fun k hk => ?_⟩
    obtain ⟨j, hA, hb⟩ := hadd k hk
    have h1k := h1 k
    have h1j := h1 j
    rw [hA, hb] at h1j
    simp only [LinearMap.neg_apply] at h1j
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

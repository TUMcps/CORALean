module

public import CORALean.ContSet.VPolytope.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff

@[expose] public section

/-!
# The support function of a V-polytope

[1, Eq. 32]: the support function of `⟨[v₁ … vₘ]⟩` is `max_i ℓᵀ vᵢ`, the value
`VPolytope.supportBound` stores; [1, Eq. 34]: the maximizing point is a support vector, which is
`VPolytope.supportBound_attained`. At `m = 0` the polytope is empty and the value is `-∞`, which
the paper fixes for the empty set at [1, Eq. 33].

## Inputs
* `P` – polytope
* `c` – linear functional

## Hypotheses
* `hk` – `P` has a vertex

## Conclusion
* the support function is the maximum of `c` over the vertices

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.supportFunc_eq (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) (hk : 0 < P.k) : -- --- CONCL ---
    supportFunc P.construct c = ((⨆ l, c (P.V l) : ℝ) : EReal) := by -- --- PROOF ---
  refine le_antisymm (supportFunc_le_coe_iff.mpr fun x hx => (P.supportBound c).le x hx) ?_
  -- the bound is attained, so the supremum reaches it
  obtain ⟨x, hx, hcx⟩ := P.supportBound_attained c hk
  have hval : (P.supportBound c).val = ⨆ l, c (P.V l) := rfl
  rw [← hval, ← hcx]
  exact le_iSup₂_of_le x hx le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

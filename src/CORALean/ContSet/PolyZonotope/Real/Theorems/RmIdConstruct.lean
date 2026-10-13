import CORALean.ContSet.PolyZonotope.Real.Operations.RmId
import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `rmId` pins the removed factors at `1`, exactly

The set of `pZ.rmId S` is the set of `pZ` restricted to factor vectors whose coordinates in `S`
are `1`: the removed factor scaled its generators by `1 ^ e`, and now scales nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [AddCommGroup α] [Module ℝ α] in
/-- A monomial at a vector that is `1` on `S` only sees the rows that stay. -/
theorem PolyZonotope.aux_monomial_rmId (pZ : PolyZonotope α) (S : Finset (Fin pZ.p))
    (a : Fin pZ.p → ℝ) (ha : ∀ k ∈ S, a k = 1) (i : Fin pZ.h) :
    PolyZonotope.monomial (pZ.rmId S).E (fun k => a (Sᶜ.orderIsoOfFin rfl k).1) i
      = PolyZonotope.monomial pZ.E a i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  -- the rows in `S` contribute `1 ^ e`, the others are the image of the iso
  rw [← Finset.prod_subset (Finset.subset_univ Sᶜ) fun k _ hk => by
    rw [ha k (by simpa using hk), one_pow], ← Finset.prod_coe_sort Sᶜ]
  exact Equiv.prod_comp ((Sᶜ).orderIsoOfFin rfl).toEquiv fun x => a x ^ pZ.E x i


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.rmId_construct (pZ : PolyZonotope α) (S : Finset (Fin pZ.p)) :
    (pZ.rmId S).construct
      = {x | ∃ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ), (∀ k, |a k| ≤ 1) ∧ (∀ k ∈ S, a k = 1)
          ∧ (∀ j, |β j| ≤ 1) ∧ x = pZ.point a + ∑ j, β j • pZ.GI j} := by -- --- PROOF ---
  -- a factor vector over the rows that stay, read as one over all rows
  have key : ∀ (b : Fin Sᶜ.card → ℝ) (i : Fin pZ.h),
      PolyZonotope.monomial (pZ.rmId S).E b i = PolyZonotope.monomial pZ.E
        (fun k => if hk : k ∈ Sᶜ then b ((Sᶜ).orderIsoOfFin rfl |>.symm ⟨k, hk⟩) else 1) i := by
    intro b i
    -- the extension is `1` on `S`, so the lemma above applies
    rw [← PolyZonotope.aux_monomial_rmId pZ S _ (fun k hk => by simp [Finset.mem_compl.not.mpr
      (not_not.mpr hk)])]
    congr 1
    funext k
    -- on the kept rows the extension reads `b` back
    have hk : ((Sᶜ).orderIsoOfFin rfl k).1 ∈ Sᶜ := ((Sᶜ).orderIsoOfFin rfl k).2
    simp only [hk, dif_pos]
    exact (congrArg b (((Sᶜ).orderIsoOfFin rfl).symm_apply_apply k)).symm
  ext x
  constructor
  · rintro ⟨b, β, hb, hβ, rfl⟩
    refine ⟨fun k => if hk : k ∈ Sᶜ then b ((Sᶜ).orderIsoOfFin rfl |>.symm ⟨k, hk⟩) else 1, β,
      fun k => ?_, fun k hk => ?_, hβ, ?_⟩
    · by_cases hk : k ∈ Sᶜ <;> simp [hk, hb]
    · simp [Finset.mem_compl.not.mpr (not_not.mpr hk)]
    · simp only [PolyZonotope.point, key]
      rfl
  · rintro ⟨a, β, ha, hS, hβ, rfl⟩
    refine ⟨fun k => a (Sᶜ.orderIsoOfFin rfl k).1, β, fun k => ha _, hβ, ?_⟩
    have hpt : (pZ.rmId S).point (fun k => a (Sᶜ.orderIsoOfFin rfl k).1) = pZ.point a := by
      show pZ.c + ∑ i, PolyZonotope.monomial (pZ.rmId S).E _ i • pZ.G i = _
      exact congrArg _ (Finset.sum_congr rfl fun i _ => by
        rw [PolyZonotope.aux_monomial_rmId pZ S a hS i])
    exact congrArg (· + ∑ j, β j • pZ.GI j) hpt.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

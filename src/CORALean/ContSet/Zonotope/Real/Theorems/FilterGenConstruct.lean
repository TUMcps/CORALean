import CORALean.ContSet.Zonotope.Real.Operations.FilterGen

/-!
# Dropping zero generators changes no point

If every generator the predicate drops is the zero vector, `Zonotope.filterGen` denotes the same
set. Exact: a zero generator contributes `β • 0 = 0` whatever its coefficient.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.filterGen_construct (Z : Zonotope α) (keep : Fin Z.h → Bool)
    (hz : ∀ j, keep j = false → Z.G j = 0) :
    (Z.filterGen keep).construct = Z.construct := by -- --- PROOF ---
  set S := Finset.univ.filter fun j => keep j = true with hS
  -- a sum over all generators is the sum over the kept ones, the dropped terms being zero
  have hsum : ∀ β : Fin Z.h → ℝ, ∑ j, β j • Z.G j = ∑ j ∈ S, β j • Z.G j := by
    intro β
    rw [hS, Finset.sum_filter_of_ne]
    intro j _ hne
    by_contra hk
    exact hne (by rw [hz j (by simpa using hk), smul_zero])
  -- and over the kept ones, the sum along the order embedding of the filtered family
  have hemb : ∀ f : Fin Z.h → α,
      ∑ j : Fin S.card, f (S.orderEmbOfFin rfl j) = ∑ j ∈ S, f j := by
    intro f
    rw [← Finset.sum_coe_sort S f]
    refine (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv (fun s : S => f s)).symm ▸ ?_
    rfl
  -- a point of the filtered zonotope: extend its coefficients by zero
  apply Set.Subset.antisymm
  · rintro _ ⟨β', hβ', rfl⟩
    refine ⟨fun i => if hi : i ∈ S then β' ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) else 0, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ S
      · simp only [hi, dif_pos]; exact hβ' _
      · simp only [hi, dif_neg, not_false_eq_true, abs_zero, zero_le_one]
    · -- the same sum, term by term
      show Z.c + ∑ j, β' j • Z.G (S.orderEmbOfFin rfl j) = _
      congr 1
      rw [hsum, ← hemb]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hmem : S.orderEmbOfFin rfl j ∈ S := Finset.orderEmbOfFin_mem S rfl j
      simp only [hmem, dif_pos]
      have : (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl j, hmem⟩ = j := by
        rw [OrderIso.symm_apply_eq]; rfl
      rw [this]
  -- a point of the original: restrict its coefficients to the kept ones
  · rintro _ ⟨β, hβ, rfl⟩
    refine ⟨fun j => β (S.orderEmbOfFin rfl j), fun j => hβ _, ?_⟩
    show Z.c + ∑ j, β j • Z.G j =
      Z.c + ∑ j : Fin S.card, β (S.orderEmbOfFin rfl j) • Z.G (S.orderEmbOfFin rfl j)
    congr 1
    exact (hsum β).trans (hemb fun j => β j • Z.G j).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

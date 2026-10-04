import CORALean.ContSet.PolyZonotope.Real.Theorems.ReplaceIdSubset

/-!
# Renaming factors injectively changes nothing

A map `f` that is injective only renames: every factor vector `a` of the original is the composite
`a' ∘ f` of the extension of `a` by `0` off the range of `f`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.replaceId_exact (pZ : PolyZonotope α) {p' : ℕ} (f : Fin pZ.p → Fin p')
    (hf : Function.Injective f) : (pZ.replaceId f).construct = pZ.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm (PolyZonotope.replaceId_subset pZ f) ?_
  rintro _ ⟨a, β, ha, hβ, rfl⟩
  -- extend `a` by `0` off the range of `f`, so that the composite is `a`
  have hext : ∀ k, Function.extend f a 0 (f k) = a k := fun k => hf.extend_apply a 0 k
  refine ⟨Function.extend f a 0, β, fun k' => ?_, hβ, ?_⟩
  · by_cases hk : ∃ k, f k = k'
    · obtain ⟨k, rfl⟩ := hk
      exact le_of_eq_of_le (congrArg abs (hext k)) (ha k)
    · have h0 := Function.extend_apply' (g := a) (e' := (0 : Fin p' → ℝ)) k' hk
      exact le_of_eq_of_le (congrArg abs h0) (abs_zero.trans_le zero_le_one)
  · have := PolyZonotope.replaceId_point pZ f (Function.extend f a 0)
    unfold PolyZonotope.point at this
    simp only [hext] at this
    exact (congrArg (fun s => s + ∑ j, β j • pZ.GI j) this).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

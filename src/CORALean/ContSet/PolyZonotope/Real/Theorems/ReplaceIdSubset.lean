import CORALean.ContSet.PolyZonotope.Real.Theorems.ReplaceIdPoint

/-!
# Renaming factors can only shrink the set

At a factor vector `a'` of the renamed set the point is the original's at `a' ∘ f`, which lies in
the unit box too. Strictly smaller in general: identifying two independent factors adds a
dependency.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.replaceId_subset (pZ : PolyZonotope α) {p' : ℕ} (f : Fin pZ.p → Fin p') :
    (pZ.replaceId f).construct ⊆ pZ.construct := by -- --- PROOF ---
  rintro _ ⟨a', β, ha', hβ, rfl⟩
  refine ⟨fun k => a' (f k), β, fun k => ha' (f k), hβ, ?_⟩
  -- the renamed dependent part is the original's at the composite
  have := PolyZonotope.replaceId_point pZ f a'
  unfold PolyZonotope.point at this
  exact congrArg (fun s => s + ∑ j, β j • pZ.GI j) this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

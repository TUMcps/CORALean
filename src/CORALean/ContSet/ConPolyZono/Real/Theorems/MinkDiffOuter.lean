import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffConstruct

/-!
# `ConPolyZono.minkDiff` contains the Minkowski difference

If `x + Z ⊆ P` then `x` passes the test at every corner of `Z`, which is what `minkDiff_construct`
says the result is. So the result is an enclosure of `P ⊖ Z` for every minuend, convex or not;
it is the whole difference when the minuend is convex (`minkDiff_inner_of_convex`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer: `P ⊖ Z ⊆ minkDiff P Z`. -/
theorem ConPolyZono.minkDiff_outer (cPZ₁ : ConPolyZono (Vec ℝ n)) (Z : Zonotope (Vec ℝ n)) :
    {x | ∀ z ∈ Z.construct, x + z ∈ cPZ₁.construct} ⊆
      (cPZ₁.minkDiff Z).construct := by -- --- PROOF ---
  intro x hx
  rw [ConPolyZono.minkDiff_construct]
  intro s
  -- the corner `c + Σ ±gⱼ` is the point of `Z` at the coefficients `±1`
  refine hx _ ⟨fun j => if s j then 1 else -1, fun j => ?_, ?_⟩
  · by_cases hs : s j = true <;> simp [hs]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hs : s j = true <;> simp [hs]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

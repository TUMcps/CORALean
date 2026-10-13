import CORALean.ContSet.Ellipsoid.Real.Operations.CartProd

/-!
# `Ellipsoid.cartProd` encloses the product

Each factor lies in its bounding box (`Ellipsoid.interval_contains`), the product of the boxes is
the box of the concatenated bounds, and a box lies in its ellipsoid. Outer only, as CORA's
`'outer'` mode: the product of two ellipsoids is not an ellipsoid.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProd_outer (E₁ : Ellipsoid n) (E₂ : Ellipsoid m) :
    (fun p : Vec ℝ n × Vec ℝ m => (Fin.append p.1 p.2 : Vec ℝ (n + m))) ''
        (E₁.construct ×ˢ E₂.construct) ⊆ (E₁.cartProd E₂).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  refine Interval.ellipsoid_contains _ ?_
  have h1 := E₁.interval_contains hx
  have h2 := E₂.interval_contains hy
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa [Entrywise.entry, Fin.append_left] using h1 i
  · simpa [Entrywise.entry, Fin.append_right] using h2 i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

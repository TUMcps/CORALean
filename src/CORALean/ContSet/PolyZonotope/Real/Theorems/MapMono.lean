import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

/-!
# `map` grows with its operand

`map` is exact, so what it denotes is the image of what its operand does, and an
image is monotone in the set mapped. The counterpart of `plus_mono`, and used
the same way: once per layer of an algorithm written in linear images.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger operand denotes a larger image. -/
theorem PolyZonotope.map_mono (f : α →ₗ[ℝ] β) {pZ₁ pZ₂ : PolyZonotope α}
    (h : pZ₁.construct ⊆ pZ₂.construct) : (pZ₁.map f).construct ⊆ (pZ₂.map f).construct := by
  rw [← PolyZonotope.map_exact, ← PolyZonotope.map_exact]
  exact Set.image_mono h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

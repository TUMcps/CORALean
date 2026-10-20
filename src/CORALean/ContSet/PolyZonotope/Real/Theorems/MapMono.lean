module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `map` grows with its operand

`map` is exact, so what it denotes is the image of what its operand does, and an
image is monotone in the set mapped. The counterpart of `plus_mono`, and used
the same way: once per layer of an algorithm written in linear images.

## Inputs
* `f` – linear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `h` – the first set is contained in the second

## Conclusion
* the image of the first is contained in the image of the second
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

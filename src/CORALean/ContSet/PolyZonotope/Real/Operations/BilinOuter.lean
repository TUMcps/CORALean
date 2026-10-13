module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.BilinGI

@[expose] public section

/-!
# `PolyZonotope.bilinOuter`

`bilin` over shared factors plus the independent generators it drops: the dependent part, the
product of the two points, exactly as `bilin` has it, and the cross terms with an independent
coefficient as new independent generators (`bilinGI`). A product of two coefficients each in
`[-1, 1]` is in `[-1, 1]` but is not independent of the others, so this is an enclosure, which
`bilin_exact` is not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `bilin`, with `bilinGI` for the independent block. -/
def PolyZonotope.bilinOuter (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) : PolyZonotope γ :=
  { pZ₁.bilin f pZ₂ hp with
    q := pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q
    GI := PolyZonotope.bilinGI f pZ₁ pZ₂ }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

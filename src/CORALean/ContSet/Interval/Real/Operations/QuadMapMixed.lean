module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

@[expose] public section

/-!
# `Interval.quadMapMixed`

CORA's `@interval/quadMap(I₁, I₂, Q)`: the two-box form, `(x₁, x₂) ↦ x₁ᵀQₖx₂` over two
boxes, bounded through their zonotopes and `Zonotope.bilin`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.quadMapMixed (Q : Fin m → Mat ℝ n n) (I₁ I₂ : Interval (Vec ℝ n)) :
    Interval (Vec ℝ m) :=
  (Zonotope.bilin (PolyZonotope.quadBilin Q) I₁.zonotope I₂.zonotope).interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

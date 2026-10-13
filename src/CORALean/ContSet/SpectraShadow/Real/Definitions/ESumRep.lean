module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Existential sum representations

CORA's hidden property `ESumRep = {B, C}` of a spectrahedral shadow
(`@spectraShadow/generateESumRep.m`): the shadow is `{x | ∃ y, B₀ + Σ xᵢ Bᵢ + Σ yⱼ Cⱼ ⪰ 0}`, the
point's own coordinates `x` among the free variables of the inequality and the existential variables
`y` the remaining ones. Intersections and cones (`and_`, `convHull_`) are built from it in CORA.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure SpectraShadow.ESumRep (n : ℕ) where
  k : ℕ
  q : ℕ
  B₀ : Mat ℝ k k
  B : Fin n → Mat ℝ k k
  C : Fin q → Mat ℝ k k

/-- The set an existential sum representation stands for. -/
def SpectraShadow.ESumRep.construct (E : SpectraShadow.ESumRep n) : Set (Vec ℝ n) :=
  {x | ∃ y : Fin E.q → ℝ, (E.B₀ + ∑ i, x i • E.B i + ∑ j, y j • E.C j).PosSemidef}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

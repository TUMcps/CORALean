import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyMulVec
import CORALean.Global.LinProg.API

/-!
# An ellipsoid answers any direction in closed form

`sup {⟨d, x⟩ | x ∈ E}` is `⟨d, q⟩ + ‖Gᵀ d‖₂`. Unlike a halfspace description
there is no linear program to solve and no dual solution to check: Cauchy–Schwarz
is the whole of the `≤` direction, and the bound holds for *every* direction at
once rather than for the ones a caller enumerated. That is what makes the
conversions out of an ellipsoid tight rather than merely sound.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program and no dual solution: the value is closed form and the
maximum is attained, which `Theorems.SupportBoundAttained` states. -/
noncomputable def Ellipsoid.supportBound (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound E.construct c where
  val := c E.q + ‖E.pullback c‖₂
  le := by
    rintro _ ⟨u, hu, rfl⟩
    rw [map_add]
    refine add_le_add le_rfl ?_
    calc c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := E.apply_mulVec c u
      _ ≤ ‖E.pullback c‖₂ * ‖u‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
      _ ≤ ‖E.pullback c‖₂ * 1 := mul_le_mul_of_nonneg_left hu (norm₂_nonneg _)
      _ = ‖E.pullback c‖₂ := mul_one _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

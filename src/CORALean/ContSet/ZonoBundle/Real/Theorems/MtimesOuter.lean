import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# `ZonoBundle.mtimes` over-approximates the linear image

Sound because `M (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ M Zᵢ`: a point in every component maps into
every image, `Zonotope.mtimes_exact` reading that image back as the one
component of the mapped bundle it came from.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimes_outer (M : Mat ℝ m n) (B : ZonoBundle (Vec ℝ n)) :
    (M *ᵥ ·) '' B.construct ⊆ (B.mtimes M).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show M *ᵥ a ∈ (Zonotope.mtimes M (B.Z i)).construct
  rw [← Zonotope.mtimes_exact]
  exact ⟨a, ha _, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

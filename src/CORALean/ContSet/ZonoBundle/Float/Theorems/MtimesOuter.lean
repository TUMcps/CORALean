import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter

/-!
# `ZonoBundle.mtimes` over-approximates the linear image

Sound because `M (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ M Zᵢ`: a point in every member maps into every
image, and `Zonotope.mtimes_outer` encloses that image in the member of the
mapped bundle it came from. `M` is read at `toRealMat`, so the statement is
about the matrix the stored floats denote and rounding is paid inside each
member.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimes_outer (M : Mat 𝕋 m n) (zB : ZonoBundle (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' zB.construct ⊆ (zB.mtimes M).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show toRealMat M *ᵥ a ∈ (Zonotope.mtimes M (zB.Z i)).construct
  exact Zonotope.mtimes_outer M (zB.Z i) ⟨a, ha i, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

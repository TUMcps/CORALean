import CORALean.ContSet.ZonoBundle.Float.Operations.Project
import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter

/-!
# `ZonoBundle.project` over-approximates the projection

Sound because `P (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ P Zᵢ`: a point in every member projects into every projected
member, and `Zonotope.project_outer` encloses that image in the member of the projected bundle it
came from.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.project_outer (zB : ZonoBundle (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' zB.construct ⊆ (zB.project dims).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show _ ∈ (Zonotope.project (zB.Z i) dims).construct
  exact Zonotope.project_outer (zB.Z i) dims ⟨a, ha i, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

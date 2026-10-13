import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact

/-!
# `HPolytope.mapEquiv` is exactly the image

`comap` already gives the preimage, and for an equivalence the image under `e` is
the preimage under `e.symm`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mapEquiv_exact (e : α ≃ₗ[ℝ] β) (P : HPolytope α) :
    ⇑e '' P.construct = (HPolytope.mapEquiv e P).construct := by -- --- PROOF ---
  have h : (HPolytope.mapEquiv e P).construct = ⇑e.symm ⁻¹' P.construct :=
    HPolytope.comap_exact _ _
  rw [h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show e.symm (e y) ∈ P.construct
    rwa [e.symm_apply_apply]
  · intro hx
    refine ⟨e.symm x, hx, ?_⟩
    show e (e.symm x) = x
    rw [e.apply_symm_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

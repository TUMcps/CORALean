import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds

/-!
# The certified linear image encloses

The same line again, with the direction pulled back through the map before the
certificate is asked for: a bound on `(Aq i) ∘ M` over the source is a bound on
`Aq i` over the image.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mtimesOf_outer {P : HPolytope α} (M : α →ₗ[ℝ] β)
    (Aq : Fin q → (β →ₗ[ℝ] ℝ)) (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) :
    ⇑M '' P.construct ⊆ (HPolytope.mtimesOf M Aq u).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

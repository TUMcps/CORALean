import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# `HPolytope.mtimesOf`

The image under an arbitrary linear map. `mapEquiv` handles the invertible case
exactly; a singular map collapses the description and there is nothing to
precompose with, so the image is enclosed on chosen directions instead. A
direction on the target is pulled back through the map, and the source answers
it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {q : ℕ} {P : HPolytope α}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.mtimesOf (M : α →ₗ[ℝ] β) (Aq : Fin q → (β →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) : HPolytope β :=
  HPolytope.ofBounds Aq fun i => SupportBound.image M (u i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.HPolytope.Real.Operations.Mtimes

/-!
# The certified linear image encloses

The same line again, with the direction pulled back through the map before the
certificate is asked for: a bound on `(Aq i) ∘ M` over the source is a bound on
`Aq i` over the image.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {q : ℕ}

theorem HPolytope.mtimesOf_outer {P : HPolytope α} (M : α →ₗ[ℝ] β)
    (Aq : Fin q → (β →ₗ[ℝ] ℝ)) (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) :
    ⇑M '' P.construct ⊆ (HPolytope.mtimesOf M Aq u).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real

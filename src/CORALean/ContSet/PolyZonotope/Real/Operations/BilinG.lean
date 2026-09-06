import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG

/-!
# The generators of `bilin`

Generator `(i, j)` is `f` at the two extended generators. Every product of two
polynomial zonotopes over shared factors differs only here: `mulG` is the
entrywise product, the uncertain-structure graph layer is matrix
multiplication, and both are bilinear, so both are this definition at a
different `f`.

`f` is a `→ₗ →ₗ` and not a function with two hypotheses, because bilinearity is
what makes the pairing distribute over the two sums that a point of each set
is — nothing else about `f` is ever used.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the pairing: `f` at the two extended generators. -/
def PolyZonotope.bilinG (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (S₁ : PolyZonotope α) (S₂ : PolyZonotope β) :
    Fin ((S₁.h + 1) * (S₂.h + 1)) → γ :=
  fun l => f (PolyZonotope.extG S₁ (finProdFinEquiv.symm l).1)
      (PolyZonotope.extG S₂ (finProdFinEquiv.symm l).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

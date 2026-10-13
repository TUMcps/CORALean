module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.bilin`

Any bilinear map applied to two vertex-representation sets: pair every vertex of
`P` with every vertex of `Q`, using `finProdFinEquiv` to carry the pairing.

`bilin_outer`, in `Theorems/BilinOuter.lean`, is what says this pairing loses
nothing.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.bilin (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : VPolytope α) (Q : VPolytope β) :
    VPolytope γ where
  k := P.k * Q.k
  V := fun m => f (P.V (finProdFinEquiv.symm m).1) (Q.V (finProdFinEquiv.symm m).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

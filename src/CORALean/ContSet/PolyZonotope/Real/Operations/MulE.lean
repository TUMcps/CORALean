import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE

/-!
# The exponent matrix of `mul`

`bilinE` at `Vec`. The exponent arithmetic of a product never reads the ambient
type, so there is nothing here beyond the name: `mul` is the entrywise case of
`bilin`, and this is its exponent matrix under the name the float layer's
`Theorems/MulOuter.lean` and `Theorems/MulGClose.lean` cite it by.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added, `pZ₂`'s read at `pZ₁`'s factor
indices. -/
def PolyZonotope.mulE (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    Fin pZ₁.p → Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → ℕ :=
  PolyZonotope.bilinE pZ₁ pZ₂ hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

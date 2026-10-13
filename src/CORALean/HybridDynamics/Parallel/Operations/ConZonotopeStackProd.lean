module

public import CORALean.HybridDynamics.Parallel.Operations.ZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.stackProd`

The Cartesian product of one constrained zonotope per component, in the stacked space: the
generators and centres as `Zonotope.stackProd`, and the constraint on the coefficients the
`HPolytope.stackProd` of the components' constraints, each answering only to its own block of
coefficients. CORA's `cartProd_` of two constrained zonotopes is the same, with block-diagonal
generators and constraints; `Theorems.ConZonotopeStackProdExact` says it is exactly the product.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.stackProd (zs : ∀ i, ConZonotope (Vec ℝ (n i))) :
    ConZonotope (Vec ℝ (∑ i, n i)) :=
  let Z := Zonotope.stackProd fun i => (⟨(zs i).h, (zs i).c, (zs i).G⟩ : Zonotope (Vec ℝ (n i)))
  { h := Z.h
    c := Z.c
    G := Z.G
    P := HPolytope.stackProd fun i => (zs i).P }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.HybridDynamics.Parallel.Operations.Unstack
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.stackProd`

The Cartesian product of one zonotope per component, as a zonotope of the stacked space: the
centres stacked, and the generators those of every component, each embedded at zero in the other
blocks. The generator count is the sum of the components', indexed through `finSigmaFinEquiv` as
`stack` is. CORA's `cartProd_` of two zonotopes is the same, `blkdiag(G1, G2)`;
`Theorems.ZonotopeStackProdExact` says it is exactly the product.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.stackProd (zs : ∀ i, Zonotope (Vec ℝ (n i))) : Zonotope (Vec ℝ (∑ i, n i)) where
  h := ∑ i, (zs i).h
  c := stack fun i => (zs i).c
  G p :=
    let q := (finSigmaFinEquiv (n := fun i => (zs i).h)).symm p
    stack (Function.update (fun i => (0 : Vec ℝ (n i))) q.1 ((zs q.1).G q.2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

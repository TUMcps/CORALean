import CORALean.HybridDynamics.Parallel.Operations.BlockProj
import CORALean.ContSet.HPolytope.Real.Operations.Comap

/-!
# `HPolytope.stackProd`

The Cartesian product of one halfspace description per component, in the stacked space: every
component's row precomposed with the projection onto its block, all rows kept. A sum of the
components' row counts, indexed through `finSigmaFinEquiv` as `stack` is. A component's
constraint says nothing about the other blocks, which is why `Interval` could not do this for a
guard: an unbounded set is no box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.stackProd (gs : ∀ i, HPolytope (Vec ℝ (n i))) : HPolytope (Vec ℝ (∑ i, n i)) where
  m := ∑ i, (gs i).m
  A := (fun p : (Σ i, Fin (gs i).m) => ((gs p.1).A p.2).comp (blockProj p.1)) ∘
    finSigmaFinEquiv.symm
  b := (fun p : (Σ i, Fin (gs i).m) => (gs p.1).b p.2) ∘ finSigmaFinEquiv.symm
  me := ∑ i, (gs i).me
  Ae := (fun p : (Σ i, Fin (gs i).me) => ((gs p.1).Ae p.2).comp (blockProj p.1)) ∘
    finSigmaFinEquiv.symm
  be := (fun p : (Σ i, Fin (gs i).me) => (gs p.1).be p.2) ∘ finSigmaFinEquiv.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

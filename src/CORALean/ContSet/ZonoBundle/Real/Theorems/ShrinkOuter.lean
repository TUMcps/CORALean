module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Operations.Shrink
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOuter

@[expose] public section

/-!
# `ZonoBundle.shrink` over-approximates the bundle

`methC` encloses each member, so the bundle lies in the intersection of the reduced members;
`enclosingParallelotope` encloses that intersection, whichever edges it is given, so each new
member holds the bundle, and so does their intersection.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Conclusion
* the bundle is contained in the shrunk bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.shrink_outer (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.shrink hk).construct := by -- --- PROOF ---
  intro x hx
  -- the bundle lies in the intersection of the reduced members
  have hP : x ∈ (⟨zB.k, fun i => (zB.Z i).reduceMethC 1⟩ : ZonoBundle (Vec ℝ n)).construct := by
    simp only [ZonoBundle.construct_eq_iInter, Set.mem_iInter] at hx ⊢
    exact fun i => Zonotope.reduceMethC_outer _ 1 (hx i)
  rw [ZonoBundle.shrink]
  refine SetIntersection.mem_construct_ofFn.mpr fun i => ?_
  exact ZonoBundle.enclosingParallelotope_outer (⟨zB.k, fun i => (zB.Z i).reduceMethC 1⟩ :
    ZonoBundle (Vec ℝ n)) hk _ hP

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalAll
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Real.Operations.Parallelotope
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `ZonoBundle.enclosingParallelotope`

The parallelotope with edges along the columns of `Γ` that CORA's `shrink` and `reduceCombined`
enclose a bundle by: `Γ box(Γ⁻¹ Z_∩)` [1, Eq. 2], the box that of the whole bundle
(`intervalAll`) mapped back by `Γ`. CORA's `shrink` writes this as `parallelotope(P, G)` on a
polytope, a function CORA does not have.

A singular `Γ` has no inverse to map by, and Mathlib's is `0`, which would enclose nothing: it
is replaced by the identity, so the result holds the bundle at any `Γ`, and is the box when `Γ`
is no basis.

## Inputs
* `zB` – zonotope bundle
* `Γ` – edge directions

## Hypotheses
* `hk` – the bundle has a member

## Output
* parallelotope along the given directions enclosing the bundle

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Γ box(Γ⁻¹ Z_∩)` of a bundle with a member, at `Γ` if it is invertible, at `1` if not. -/
noncomputable def ZonoBundle.enclosingParallelotope (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (Γ : Mat ℝ n n) : Zonotope (Vec ℝ n) :=
  let Γ' : Mat ℝ n n := if IsUnit Γ.det then Γ else 1             -- directions that can be undone
  ZonoBundle.parallelotope Γ' ((zB.mtimes Γ'⁻¹).intervalAll hk)    -- `Γ' box(Γ'⁻¹ Z_∩)`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

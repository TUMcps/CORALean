module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.Global.Corners

@[expose] public section

/-!
# A polynomial zonotope as its corners

## Inputs
* `pZ` – polynomial zonotope

## Output
* vertex polytope of the polynomial zonotope

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.vPolytope (pZ : PolyZonotope α) : VPolytope α :=
  pZ.zonotope.vPolytope

/-- The vertex a choice of sign picks out, one sign per factor and then one per
independent generator. -/
def PolyZonotope.corner (pZ : PolyZonotope α) (σ : Fin (pZ.p + pZ.q) → Bool) : α :=
  pZ.c
    + ∑ i, PolyZonotope.monomial pZ.E
        (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i • pZ.G i
    + ∑ j, (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else -1) • pZ.GI j

/-- The hull of a polynomial zonotope's corners, one per sign pattern of its dependent and
independent factors. -/
noncomputable def PolyZonotope.vPolytopeCorners (pZ : PolyZonotope α) : VPolytope α where
  k := 2 ^ (pZ.p + pZ.q)
  V := fun v => pZ.corner (signEquiv (pZ.p + pZ.q) v)

/-- The paper's `H` block, read column by column: a column with no exponent above
one is zeroed rather than deleted, so the index set stays `Fin pZ.h`. -/
def PolyZonotope.high (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := 0
  G := fun i => if ∀ k, pZ.E k i ≤ 1 then 0 else pZ.G i
  E := pZ.E
  GI := pZ.GI

/-- The paper's `PZ̄`: what `H` reaches is made independent, through the tight
zonotope enclosure of [1, Prop. 5], and `K` keeps its exponents. -/
noncomputable def PolyZonotope.binarize (pZ : PolyZonotope α) : PolyZonotope α :=
  let H := pZ.high.zonotopeEven                       -- [1, Prop. 5]'s tight enclosure of H
  { p := pZ.p
    h := pZ.h
    q := pZ.h + pZ.q
    c := pZ.c + H.c
    G := fun i => if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0
    E := fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0
    GI := H.G }

/-- [1, Prop. 6]'s `poly`: the corners of `binarize`, which keeps every
column the zonotope enclosure of `vPolytope` would have freed. -/
noncomputable def PolyZonotope.vPolytopeSplit (pZ : PolyZonotope α) : VPolytope α :=
  pZ.binarize.vPolytopeCorners

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

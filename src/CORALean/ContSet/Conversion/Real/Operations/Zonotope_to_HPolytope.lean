module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.Global.EuclideanNorm
public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import Mathlib.Data.List.Sublists

@[expose] public section

/-!
# A zonotope as halfspaces, as CORA's `polytope(Z)` computes the facets

`@zonotope/polytope.m` at its default `'exact'`: a zonotope without generators is the box rows
`[I; -I] x ≤ [c; -c]`; otherwise every combination of `n - 1` generators (`combinator(nrGen, n-1,
'c')`) gives the normal `ndimCross` of those generators, normalized, the zero normals (MATLAB's
`NaN` rows) dropped, and the rows `±C` at `±C c + Σ |C G|` ([1, Thm. 2]). At `n = 1` the one
combination is empty and its cross product is `1`, CORA's `C = 1`.

Departures. CORA first removes the zero generators (`compact_`), which only removes zero normals
here, and tests "no generators" after that, which is the test that every generator is zero. The
combinations come in the order `List.sublistsLen` lists them, not CORA's, and a row set is
unordered. CORA's degenerate branch (`rank G < n`, an SVD projection) is not here: these rows
still enclose a degenerate zonotope but need not describe it, and exactness asks for generators
that span (`Zonotope.hPolytopeFacets_exact`).

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Classical

variable {m : ℕ}


/-- CORA's `ndimCross(G(:, comb(i,:)))` for every `comb = combinator(nrGen, n-1, 'c')`. -/
noncomputable def Zonotope.facetNormals (Z : Zonotope (Vec ℝ (m + 1))) : List (Vec ℝ (m + 1)) :=
  ((List.finRange Z.h).sublistsLen m).attach.map fun l =>
    Z.facetNormal fun j => l.1.get ⟨j, by rw [(List.mem_sublistsLen.mp l.2).2]; exact j.isLt⟩

/-- The rows `C`: the nonzero normals, each divided by its length. -/
noncomputable def Zonotope.facetRows (Z : Zonotope (Vec ℝ (m + 1))) : List (Vec ℝ (m + 1)) :=
  (Z.facetNormals.filter (· ≠ 0)).map fun v => (‖v‖₂)⁻¹ • v


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polytope(Z)` at `'exact'`: the box rows without generators, else `[C; -C]`. -/
noncomputable def Zonotope.hPolytopeFacets (Z : Zonotope (Vec ℝ (m + 1))) :
    HPolytope (Vec ℝ (m + 1)) :=
  -- 1. no generators: `C = [eye(n); -eye(n)]`, `d = [c; -c]`
  if ∀ j, Z.G j = 0 then
    let I : Mat ℝ (m + 1) (m + 1) := 1
    HPolytope.ineqs (Fin.append I (-I)) (Fin.append Z.c (-Z.c))
  else
    -- 2. the normalized facet normals `C`, and `deltaD = sum(abs(C*G), 2)`
    let C : Fin Z.facetRows.length → Vec ℝ (m + 1) := fun k => Z.facetRows.get k
    let δ : Fin Z.facetRows.length → ℝ := fun k => ∑ j, |C k ⬝ᵥ Z.G j|
    -- 3. `d = [C*c + deltaD; -C*c + deltaD]`, `C = [C; -C]`
    HPolytope.ineqs (Fin.append C (-C)) (Fin.append (fun k => C k ⬝ᵥ Z.c + δ k)
      fun k => -(C k ⬝ᵥ Z.c) + δ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

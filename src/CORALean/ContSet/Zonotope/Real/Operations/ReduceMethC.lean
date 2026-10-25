module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Real.Operations.MethCBasis
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

@[expose] public section

/-!
# `Zonotope.reduceMethC`

CORA's `reduce(Z, 'methC', o)` [1], descended from [2, Sec. 5.4.2]'s method C, `Zonotope.methodC`.
Its partition is Girard's (`pickedGenerators` ranks by `‖g‖₁ - ‖g‖∞` as `girardSplit` does). What
differs is the enclosure: the dropped block is boxed along `n` of the dropped generators
themselves, prefiltered by length and then chosen by an exhaustive search over spanned volume.
Two scalings CORA carries are absent because they cancel: `P·box(P⁻¹·)` is unchanged by a positive
diagonal on `P`'s columns, and the row scaling `W` multiplies out against the `W⁻¹` inside. The
determinant test is what a `pinv` hides in CORA: at a singular basis every candidate scores `inf`
and the result encloses nothing; here it boxes along the axes.

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* zonotope with the dropped block boxed along method C

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025). No
      paper behind the rule was confirmed.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'methC', o)`: Girard's partition, with the dropped block
boxed along the filtered generators of largest spanned volume — along the axes
where that basis is singular, and nothing at all at order `o` or below. -/
noncomputable def Zonotope.reduceMethC (Z : Zonotope (Vec ℝ n)) (o : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then
    let split := Z.girardSplit o hlt                 -- Girard's partition, kept and dropped
    let basis := Z.methCBasis split                   -- the filtered candidate basis
    if IsUnit basis.det then
      Z.reduceByBasis split basis                      -- box along that basis
    else Z.reduceBy split                              -- singular: box along the axes instead
  else Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

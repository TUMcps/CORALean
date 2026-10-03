import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Real.Operations.MethCBasis
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

/-!
# `Zonotope.reduceMethC`

CORA's `reduce(Z, 'methC', o)` [1], descended from [2, Sec. 5.4.2]'s method C,
`Zonotope.methodC`. Its partition is Girard's — CORA reaches it
through `pickedGenerators`, which ranks by `‖g‖₁ - ‖g‖∞` exactly as
`girardSplit` does. What differs is the enclosure: the dropped block is boxed
along `n` of the dropped generators themselves, prefiltered by length and then
chosen by an exhaustive search over spanned volume, instead of along the axes.

Two scalings CORA carries are absent because they cancel: `P·box(P⁻¹·)` is
unchanged by a positive diagonal on `P`'s columns, which is CORA's
normalization of `P`, and its row scaling `W` multiplies out against the `W⁻¹`
inside. `W` changes an outcome only through `methCFilter`'s ranking, and the
`|det|` ranking is invariant under it, so it survives there and nowhere else.

The determinant test is what a `pinv` hides in CORA: at a singular basis
`priv_volumeFilter` scores every candidate `inf` and still returns one, and the
result encloses nothing. Here that case boxes along the axes instead.

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025). No
      paper behind the rule was confirmed.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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

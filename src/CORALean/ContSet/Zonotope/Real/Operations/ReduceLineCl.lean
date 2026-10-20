module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Real.Operations.LineClBasis

@[expose] public section

/-!
# `Zonotope.reduceLineCl`

Over-approximation by line clustering [1, Alg. 3], as CORA's `reduce(Z, 'cluster', o)`
is meant to run it [2]: Girard's partition, with the dropped block boxed along the
clustering basis `lineClBasis` instead of along the axes. CORA's file dispatches to
`emLineMean`, which the repository does not ship, so the definition follows the
paper; `lineClBasis` lists what it fixes where the listing is open.

## Inputs
* `Z` – zonotope
* `o` – target order
* `ξ` – convergence threshold
* `fuel` – iteration budget
* `runs` – number of restarts

## Output
* zonotope with the dropped block boxed along the found basis

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
* [2] `contSet/@zonotope/private/priv_reduceCluster.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Girard's partition, with the dropped block boxed along `lineClBasis`, and nothing
at all at order `o` or below. `ξ` is the convergence threshold, `fuel` bounds the
iterations and `runs` is the number of restarts. -/
noncomputable def Zonotope.reduceLineCl (Z : Zonotope (Vec ℝ n)) (o : ℕ) (ξ : ℝ)
    (fuel runs : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then
    let split := Z.girardSplit o hlt                                -- the dropped generators
    let Lmin := Z.lineClBasis split ξ fuel runs                     -- Alg. 3
    Z.reduceByBasis split Lmin                                      -- Z_red = L_min · IH(L_min⁻¹ Z)
  else Z


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

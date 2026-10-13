module

public import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol

@[expose] public section

/-!
# `ConPolyZono.convHullEC`

The constraint exponent matrix of [1, Prop. 9]: the linear combination's, once
per copy and over that copy's own factors, then one column per weight factor for
the row that fixes their sum.

The two blocks read disjoint factors, so the copies' constraints and the weight
constraint never interfere.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each copy's constraint exponents, then the weight factors themselves. -/
def ConPolyZono.convHullEC (a : ℕ) {p s : ℕ} (EC : Fin p → Fin s → ℕ) :
    Fin (a * p + a) → Fin (a * s + a) → ℕ :=
  Fin.append
    (fun x => Fin.append (ConPolyZono.blkDiag a EC x) (fun _ => 0))
    (fun j => Fin.append (fun _ => 0) (ConPolyZono.unitCol j 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

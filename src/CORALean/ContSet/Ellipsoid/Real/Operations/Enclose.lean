module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter

@[expose] public section

/-!
# `Ellipsoid.enclose`

CORA's `@ellipsoid/enclose.m` with a matrix: `E2 = M * Eplus`, then `E = convHull(E, E2)`, and
`convHull_` for two ellipsoids is `or(E, E2, 'outer')`, which is `priv_orEllipsoidOA`: a
minimum-volume enclosing ellipsoid found by an SDP solver. A solver run is not a definition, so the
hull is an argument `orOA` owing `Ellipsoid.IsOrOuter`.

Read as printed: the header documents `E2 = M*E + Eplus`, but the code multiplies `Eplus` and
adds nothing (see `Ellipsoid.enclose_cora_counterexample`).

## Inputs
* `orOA` – outer hull of two ellipsoids
* `E` – ellipsoid
* `M` – matrix
* `Eplus` – ellipsoid

## Output
* hull of `E` and `M Eplus` under `orOA`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enclose(E, M, Eplus)`: `E2 = M * Eplus`, then the hull `orOA` of `E` and `E2`. -/
def Ellipsoid.enclose (orOA : Ellipsoid n → Ellipsoid n → Ellipsoid n) (E : Ellipsoid n)
    (M : Mat ℝ n m) (Eplus : Ellipsoid m) : Ellipsoid n :=
  let E2 := Ellipsoid.mtimes M Eplus
  orOA E E2


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

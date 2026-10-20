module

public import CORALean.ContDynamics.LinearSys.Operations.ReachBoxFloat
public import CORALean.Global.Float.NoNaN
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `reachBoxFloatChecked`, without a NaN

`reachBoxFloat` ([1, Alg. 2] in floats) followed by `checkNoNaN`: `none` where it is `none` or
a float of its result is a NaN. A `some` is the unchecked `some`
(`reachBoxFloatChecked_eq_some`), so whatever is proved of `reachBoxFloat` holds of it, and the
NaN test that the trust base asks of the caller has been made.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `U` – input float zonotope
* `r` – float step length
* `η` – Taylor order
* `N` – number of steps

## Output
* float reachable zonotopes of the steps, or none if a result float is NaN

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachBoxFloat`, or `none` if a float of its result is a NaN. -/
def LinearSys.reachBoxFloatChecked (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec 𝕋 n)) (r : 𝕋)
    (η N : ℕ) : Option (List (Zonotope (Vec 𝕋 n))) :=
  checkNoNaN (𝕋 := 𝕋) (sys.reachBoxFloat X₀ U r η N)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

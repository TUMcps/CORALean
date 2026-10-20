module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.NormSq
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Zonotope.normSq` bounds every member

The box contains the zonotope (`Zonotope.interval_contains`) and a certificate `σ` with
`normSq ≤ σ·σ` makes `|σ|` an upper bound of `Interval.norm`. An upper bound only, and not
tight in general: a box is larger than its zonotope.

## Inputs
* `Z` – zonotope
* `σ` – certificate
* `x` – point

## Hypotheses
* `hσ` – squared length bounded by the squared certificate
* `hx` – point lies in the zonotope

## Conclusion
* norm of the point is at most the certificate's magnitude
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.normSq_le (Z : Zonotope (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal Z.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  Interval.norm_le Z.interval hσ (Zonotope.interval_contains Z hx)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

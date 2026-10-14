module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Alg. 1` lines 1-2 in floats: the loop state before the first iteration

`manualInit`, [1, Alg. 1] lines 1-2, computed in `𝕋`: `t₀ = 0`, bracketed by `[0, 0]`,
`H(t₀) = X₀`, and both input shares the point `{0}`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2, before the first iteration. -/
def LinearSys.manualInitFloat (X₀ : Zonotope (Vec 𝕋 n)) : LinearSys.ManualStateFloat 𝕋 n :=
  { t := 0, tLo := zero, tHi := zero                                -- 1. t₀ ← 0
    H := X₀                                                         -- 2. H(t₀) ← X₀
    Pu := Interval.point fun _ => zero                              -- 2. P^u(t₀) ← 0
    PU := (Interval.point fun _ => zero).zonotope }                 -- 2. P̂^U(t₀) ← 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

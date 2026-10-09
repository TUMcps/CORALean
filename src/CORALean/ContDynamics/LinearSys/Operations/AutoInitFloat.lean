import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `Alg. 2` lines 1-2 in floats: the loop state before the first iteration

`autoInit`, [1, Alg. 2] lines 1-2, computed in `𝕋`: `t₀ = 0`, bracketed by `[0, 0]`,
`Δt₋₁ = t_end`, `H(t₀) = X₀`, the particular solutions the point `{0}` and both accumulated
errors `0`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2, before the first iteration. -/
def LinearSys.autoInitFloat (X₀ : Zonotope 𝕋 n) (tend : 𝕋) : LinearSys.AutoStateFloat 𝕋 n :=
  { t := 0, tLo := zero, tHi := zero                                -- 1. t₀ ← 0
    Δt := tend                                                      -- 1. Δt₋₁ ← t_end
    H := X₀                                                         -- 1. H(t₀) ← X₀
    Pu := Interval.point fun _ => zero                              -- 2. P^u(t₀) ← 0
    PU0 := (Interval.point fun _ => zero).zonotope                  -- 2. P̂^U_0(t₀) ← 0
    PUinf := (Interval.point fun _ => zero).zonotope                -- 2. P̂^U_∞(t₀) ← 0
    εa := 0, εr := 0 }                                              -- 1. ε^a_0, ε^r_0 ← 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

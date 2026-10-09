import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# `Alg. 1` lines 1-6 in floats: the loop state before the first iteration

`minBackReachInit` computed in `𝕋`: [1, Alg. 1] lines 1-6, the two centred particular solutions of
the time-inverted dynamics `-A` accumulated up to `t₀`, by `inputSolutionFloat` rather than
`inputSolution`, and the origin as the start of `R̂^∃`. Negating a float is exact, so `-A` costs
no rounding.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2 and 5-6: the two particular solutions accumulated up to `t₀`, before the first
iteration. -/
def LinearSys.minBackReachInitFloat (sys : LinearSys 𝕋 n) (W₀ U₀ : Zonotope 𝕋 n) (t₀ : 𝕋)
    (η : ℕ) : LinearSys.MinBackReachStateOf 𝕋 (Zonotope 𝕋 n) (ConZonotope 𝕋 n) :=
  let Ā : LinearSys 𝕋 n := ⟨fun i j => neg (sys.A i j)⟩             -- time-inverted dynamics
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZW₀ := Ā.inputSolutionFloat t₀ η W₀                             -- 5. Ẑ_{W₀}(-t₀)
    ZU₀ := Ā.inputSolutionFloat t₀ η U₀                             -- 6. Ẑ_{U₀}(-t₀)
    R := (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.conZonotope }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

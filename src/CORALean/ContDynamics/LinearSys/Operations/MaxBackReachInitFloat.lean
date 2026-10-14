module

public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContSet.ConZonotope.Float.Operations.Origin
public import CORALean.ContSet.Interval.Float.Operations.Magnitude
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMatBox
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `Alg. 3` lines 1-2 in floats: the loop state before the first iteration

`maxBackReachInit` computed in `𝕋`: the two particular solutions accumulated up to `t₀`. The
integral `∫₀^{t₀} e^{As}ds` is only known to an interval matrix (`MatExp.adaptiveIntegral`),
and an inner set cannot be had as the image under it, so `Z̲_U(t₀)` is the outer float image
with its excess over the exact set recorded, `UErr`: a later step makes room for it
(`maxBackReachStepFloat`). `Ẑ_{W₀}(t₀)` is `inputSolutionFloat`, an outer set, which is the
direction a set that is subtracted wants. `η` is raised with `reachOrderFloat` to the first order
the float remainder bound at `t₀ · A` admits; `none` when that search fails.
The lines are those of [1, Alg. 3].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2: the two particular solutions accumulated up to `t₀`, before the first
iteration. -/
def LinearSys.maxBackReachInitFloat (sys : LinearSys 𝕋 n) (U W₀ : Zonotope (Vec 𝕋 n)) (t₀ : 𝕋)
    (η : ℕ) : Option (LinearSys.MaxBackReachStateFloat 𝕋 n) := do
  let η' ← sys.reachOrderFloat t₀ t₀ η                              -- η, raised until admissible
  let I := MatExp.adaptiveIntegral (Interval.point sys.A) t₀ η'     -- [∫₀^{t₀} e^{As}ds]
  let ZU := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- 2. Z̲_U(t₀)
    (S := 𝒵[𝕋]) I U
  let ZW₀ := sys.inputSolutionFloat t₀ η' W₀                        -- 2. Ẑ_{W₀}(t₀)
  pure { tLo := t₀                                                  -- 1. τ = [t₀, t_end]
         tHi := t₀
         ZU := ZU
         UErr := (Zonotope.mtimesIntervalMatBox I U).magnitude      -- what ZU lies outside by
         ZW₀ := ZW₀
         ZW := Zonotope.origin n
         RH := ConZonotope.origin n
         RU := Zonotope.origin n }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

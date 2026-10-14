module

public import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Alg. 2` lines 3-6: the linear pass, in floats

`adaptLinPass` in `𝕋`: the linearization at `linPointFloat` and the two sets *its linear system
alone* reaches, `R_lin(t_{k+1})` and `R_lin(τ_k)`, with the input `f(z✱) ⊕ B(U - u✱)` and the
abstraction error left out. What a step adds to them is `R_abs`, whose radius `adaptStepFloat`
reads off the difference to a full step; no soundness statement is made of the pass, it only
tunes. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, R_lin(t_{k+1}), R_lin(τ_k))`: the linearized system's matrix and the two sets it
reaches from `R` under inputs in `U`, or `none` if the linear step fails. -/
def NonlinearSys.FloatModel.adaptLinPassFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (fm : NonlinearSys.FloatModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachOptions 𝕋)
    (R : Zonotope (Vec 𝕋 n)) : Option (Mat 𝕋 n n × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) := do
  let zs := fm.linPointFloat options.Δt R U                   -- 3. linPoint, eq. (6)
  let AB := fm.linearizeFloat zs.1 zs.2                             -- 4.-5. taylor, linSys
  let f₀ := fm.f (Interval.point zs.1) (Interval.point zs.2)        -- [f(z✱)]
  let Ulin := f₀.zonotope ⊞                                         -- 5. f(z✱) ⊕ B(U - u✱)
    Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) AB.2 (Recentre.recentre U)
  let S ← NonlinearSys.oneStepFloat AB.1 zs.1 Ulin R options        -- 6. linReachAdaptive
  pure (AB.1, S.2, S.1)                                             -- eqs. (10), (12)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

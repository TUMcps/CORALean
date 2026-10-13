module

public import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `Alg. 1` lines 8-11 in floats: one iteration of the main loop

`minBackReachStep` computed in `𝕋`: [1, Alg. 1] lines 8-11. The exact layer's `e^{-A t_k}` is the
interval matrix `[e^{-A t_k}]` of `expSquaringFloat` (Taylor order `η`, then `ν` squarings), its
correction matrix `F` is `intervalCorrectionMatrix`, and every product with either is a set times
an interval matrix. The outer direction is the exact layer's: each set is enclosed, none is
shrunk, so the state encloses what the real iteration builds.

`t_{k+1}` is `t_k + Δt` rounded up; on a grid the floats represent exactly (a dyadic
`t₀` and `Δt`) that is the exact `t_k + Δt`, and off it the time points are those the
stored floats name.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 8-11: one iteration of [1, Alg. 1]'s main loop, propagating the two particular
solutions and the converted target set over `τ_k`. -/
def LinearSys.minBackReachStepFloat (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope 𝕋 (Vec 𝕋 n)) (W₀ U₀ : Zonotope (Vec 𝕋 n))
    (Zw : 𝕋 → Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η ν : ℕ) (s : LinearSys.MinBackReachStateOf 𝕋 (Zonotope (Vec 𝕋 n)) (ConZonotope 𝕋 (Vec 𝕋 n))) :
    LinearSys.MinBackReachStateOf 𝕋 (Zonotope (Vec 𝕋 n)) (ConZonotope 𝕋 (Vec 𝕋 n)) :=
  let Ā : LinearSys 𝕋 n := ⟨fun i j => neg (sys.A i j)⟩             -- time-inverted dynamics
  let tk1 := addUp s.t Δt                                           -- 8. t_{k+1} ← t_k + Δt
  let Φk := Ā.expSquaringFloat s.t s.t η ν                          -- 8. [e^{-A t_k}]
  let Φk1 := Ā.expSquaringFloat tk1 tk1 η ν                         -- 8. [e^{-A t_{k+1}}]
  let ZW₀ := Plus.plus s.ZW₀                                        -- 9. Ẑ_{W₀}(-t_{k+1})
    (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k)) Φk
      (Ā.inputSolutionFloat Δt η W₀))
  let ZU₀ := Plus.plus s.ZU₀                                        -- 12. Ẑ_{U₀}(-t_{k+1})
    (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k)) Φk
      (Ā.inputSolutionFloat Δt η U₀))
  let ZW := Plus.plus ZW₀ (Zw s.t)                                  -- 10. Ẑ_W(-τ_k)
  let CZk1 := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Φk1 CZ
  let hull := LinComb.linComb CZk1                                  -- 11. conv(…, …)
    (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Φk CZ)
  let curv := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- 11. F e^{-A t_{k+1}} CZ
    (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k))
    (MatExp.intervalCorrectionMatrix (Interval.point Ā.A) Δt η) CZk1
  let R := Plus.plus (Plus.plus hull curv)                          -- 11. ⊕ -Ẑ_W(-τ_k)
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) (negIdentityMat 𝕋 n)
      ZW).conZonotope
  { t := tk1, ZW₀ := ZW₀, ZU₀ := ZU₀, R := R }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

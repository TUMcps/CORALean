module

public import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# `Alg. 2` line 16: the AE time-interval backward reachable set

`minBackReachTimeInterval`: [1, Alg. 2] line 16, `R^{∀∃}(-τ)`, the `ω` steps' sets united, each cut
by the polytope `⟨N,p⟩_H` the propagated support functions built, over the time-inverted dynamics
`ẋ̃ = -A x̃ - u - w`. Nothing here searches, so no fuel: `ω` and `η` are fixed by
[1, Assumption 1] and the loop is bounded by `ω`. `ρ` is the caller's support oracle for a
constrained zonotope, a linear program which `HPolytope.supportBound` solves but only as an
`Option`. `Zw` is (27), the constant center trajectory's contribution over one interval. Line 16's
union is no constrained zonotope, so the result is a `Set`, as `tunedReach` returns one.

## Inputs
* `sys` – linear system
* `ρ` – support oracle for constrained zonotopes
* `CZ` – target constrained zonotope
* `W₀` – initial disturbance zonotope
* `U₀` – initial input zonotope
* `Zw` – center trajectory contribution
* `N` – direction matrix
* `t₀` – start time
* `tend` – end time
* `η` – Taylor order
* `ω` – number of iterations

## Output
* union of the steps' sets, each cut by the polytope of the support functions
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n q : ℕ} {𝕋 : Type} [Scalar 𝕋]
open Matrix ContSet Scalar NormedSpace


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 1-6: the two centered particular solutions accumulated up to `t₀`,
before the first iteration. -/
noncomputable def LinearSys.aux_minBackReachInit (sys : LinearSys 𝕋 n)
    (W₀ U₀ : Zonotope (Vec ℝ n)) (t₀ : ℝ) (η : ℕ) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := LinearSys.canonical (-toRealMat sys.A)  -- time-inverted dynamics
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZW₀ := Ā.inputSolution (S := 𝒵) t₀ η W₀                         -- 5. Ẑ_{W₀}(-t₀)
    ZU₀ := Ā.inputSolution (S := 𝒵) t₀ η U₀                         -- 6. Ẑ_{U₀}(-t₀)
    R := (Zonotope.ofPoint 0).conZonotope }

/-- Lines 8-11: one iteration of [1, Alg. 2]'s main loop, propagating the two
particular solutions and the converted target set over `τ_k`. -/
noncomputable def LinearSys.aux_minBackReachStep (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MinBackReachState n) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := LinearSys.canonical (-toRealMat sys.A)  -- time-inverted dynamics
  -- 8. t_{k+1} ← t_k + Δt
  let tk1 := s.t + Δt
  -- 8. e^{-A t_k}
  let Φk := exp (s.t • toRealMat Ā.A)
  -- 8. e^{-A t_{k+1}}
  let Φk1 := exp (tk1 • toRealMat Ā.A)
  -- 9. Ẑ_{W₀}(-t_{k+1})
  let ZW₀ := Zonotope.plus s.ZW₀
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η W₀))
  -- 12. Ẑ_{U₀}(-t_{k+1})
  let ZU₀ := Zonotope.plus s.ZU₀
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η U₀))
  -- 10. Ẑ_W(-τ_k)
  let ZW := Zonotope.plus ZW₀ (Zw s.t)
  -- 11. conv(…, …)
  let hull := ConZonotope.linComb (ConZonotope.mtimes Φk1 CZ)
    (ConZonotope.mtimes Φk CZ)
  -- 11. F e^{-A t_{k+1}} CZ
  let curv := ConZonotope.mtimesIntervalMat
    (MatExp.correctionMatrix (toRealMat Ā.A) Δt η) (ConZonotope.mtimes Φk1 CZ)
  -- 11. ⊕ -Ẑ_W(-τ_k)
  let R := ConZonotope.plus (ConZonotope.plus hull curv)
    (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) ZW))
  { t := tk1, ZW₀ := ZW₀, ZU₀ := ZU₀, R := R }

/-- Lines 7-15: the state after the `k`-th iteration, holding `R̂^∃(-τ_k)`. -/
noncomputable def LinearSys.aux_minBackReachRun (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MinBackReachState n
  | 0 => sys.aux_minBackReachStep CZ W₀ U₀ Zw Δt η (sys.aux_minBackReachInit W₀ U₀ t₀ η)
  | k + 1 =>
    sys.aux_minBackReachStep CZ W₀ U₀ Zw Δt η (sys.aux_minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k)

/-- Lines 12-13, eq. (46): `ρ(R̂^∃(-τ_k;u_j(·)), N_(j,·))`, the step's own support
value less what the direction's input trajectory takes off it. -/
noncomputable def LinearSys.aux_minBackReachSupport (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ)
    (k : ℕ) (j : Fin q) : ℝ :=
  let s := sys.aux_minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k
  (ρ s.R (HPolytope.rowLin N j)).val - (s.ZU₀.supportBound (-HPolytope.rowLin N j)).val

/-- Lines 4 and 14: `p_(j)` after the steps `0` to `k`. `max`, not line 14's
`min` — a union's support is the largest of its parts', see the findings. -/
noncomputable def LinearSys.aux_minBackReachP (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ) : ℕ → Fin q → ℝ
  | 0 => fun j => sys.aux_minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η 0 j
  | k + 1 => fun j => max (sys.aux_minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η k j)
      (sys.aux_minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η (k + 1) j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 16: `R̂^∀∃(-τ)`, the `ω` steps' sets united, each cut by the
polytope `⟨N,p⟩_H` the propagated support functions built. -/
noncomputable def LinearSys.minBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  -- 1. Δt ← (t_end - t₀)/ω
  let Δt := (tend - t₀) / ω
  -- 4. and 14. ⟨N,p⟩_H
  let P := HPolytope.ineqs N
    (sys.aux_minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η (ω - 1))
  ⋃ k < ω, ((sys.aux_minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k).R.construct ∩ P.construct)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

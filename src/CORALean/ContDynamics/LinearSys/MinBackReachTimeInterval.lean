import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

/-!
# `Alg. 1`: the minimal time-interval backward reachable set

[1, Alg. 1] over the time-inverted dynamics `ẋ̃ = -A x̃ - u - w`. `minBackReachInit`
is lines 1-6, `minBackReachStep` lines 8-11, `minBackReachRun` the loop of lines
7-15, `minBackReachSupport` lines 12-13, `minBackReachP` lines 4 and 14, and
`minBackReachTimeInterval` line 16. Nothing here searches, so no fuel: `ω` and
`η` are fixed by [1, Assumption 1] and the loop is bounded by `ω`.

Three departures. `p` accumulates by `max`, not line 14's `min`: `p_(j)` is to
bound `R̂^∃(-τ;u_j(·)) = ⋃_k R̂^∃(-τ_k;u_j(·))`, whose support is the largest over
the steps — see the findings on the paper's page. Line 13's `ρ(R̂^∃(-τ_k),·)` is
read off the step's own set rather than re-derived by (44), which drops (43)'s
curvature term. And line 16's union is no constrained zonotope, so the result is
a `Set`, as `tunedReach` returns one for the same reason.

`ρ` is the caller's support oracle for a constrained zonotope — a linear program,
which `HPolytope.supportBound` solves but only as an `Option`. `Zw` is (26), the
constant centre trajectory's contribution over one interval.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n q : ℕ} {𝕋 : Type} [Scalar 𝕋]

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure LinearSys.MinBackReachState (n : ℕ) where
  /-- `t_k`, line 8. -/
  t : ℝ
  /-- `Ẑ_{W₀}(-t_k)`, line 9. -/
  ZW₀ : Zonotope (Vec ℝ n)
  /-- `Ẑ_{U₀}(-t_k)`, line 12. -/
  ZU₀ : Zonotope (Vec ℝ n)
  /-- `R̂^∃(-τ_{k-1})`, line 11. -/
  R : ConZonotope (Vec ℝ n)

/-- Lines 1-6: the two centred particular solutions accumulated up to `t₀`,
before the first iteration. -/
noncomputable def LinearSys.minBackReachInit (sys : LinearSys 𝕋 n)
    (W₀ U₀ : Zonotope (Vec ℝ n)) (t₀ : ℝ) (η : ℕ) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := ⟨-toRealMat sys.A⟩                       -- time-inverted dynamics
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZW₀ := Ā.inputSolution (S := 𝒵) t₀ η W₀                         -- 5. Ẑ_{W₀}(-t₀)
    ZU₀ := Ā.inputSolution (S := 𝒵) t₀ η U₀                         -- 6. Ẑ_{U₀}(-t₀)
    R := (Zonotope.ofPoint 0).conZonotope }

/-- Lines 8-11: one iteration of [1, Alg. 1]'s main loop, propagating the two
particular solutions and the converted target set over `τ_k`. -/
noncomputable def LinearSys.minBackReachStep (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MinBackReachState n) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := ⟨-toRealMat sys.A⟩                       -- time-inverted dynamics
  let tk1 := s.t + Δt                                               -- 8. t_{k+1} ← t_k + Δt
  let Φk := exp (s.t • toRealMat Ā.A)                               -- 8. e^{-A t_k}
  let Φk1 := exp (tk1 • toRealMat Ā.A)                              -- 8. e^{-A t_{k+1}}
  let ZW₀ := Zonotope.plus s.ZW₀                                    -- 9. Ẑ_{W₀}(-t_{k+1})
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η W₀))
  let ZU₀ := Zonotope.plus s.ZU₀                                    -- 12. Ẑ_{U₀}(-t_{k+1})
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η U₀))
  let ZW := Zonotope.plus ZW₀ (Zw s.t)                              -- 10. Ẑ_W(-τ_k)
  let hull := ConZonotope.linComb (ConZonotope.mtimes Φk1 CZ)       -- 11. conv(…, …)
    (ConZonotope.mtimes Φk CZ)
  let curv := ConZonotope.mtimesIntervalMat                         -- 11. F e^{-A t_{k+1}} CZ
    (MatExp.correctionMatrix (toRealMat Ā.A) Δt η) (ConZonotope.mtimes Φk1 CZ)
  let R := ConZonotope.plus (ConZonotope.plus hull curv)            -- 11. ⊕ -Ẑ_W(-τ_k)
    (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) ZW))
  { t := tk1, ZW₀ := ZW₀, ZU₀ := ZU₀, R := R }

/-- Lines 7-15: the state after the `k`-th iteration, holding `R̂^∃(-τ_k)`. -/
noncomputable def LinearSys.minBackReachRun (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MinBackReachState n
  | 0 => sys.minBackReachStep CZ W₀ U₀ Zw Δt η (sys.minBackReachInit W₀ U₀ t₀ η)
  | k + 1 => sys.minBackReachStep CZ W₀ U₀ Zw Δt η (sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k)

/-- Lines 12-13, eq. (44): `ρ(R̂^∃(-τ_k;u_j(·)), N_(j,·))`, the step's own support
value less what the direction's input trajectory takes off it. -/
noncomputable def LinearSys.minBackReachSupport (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ)
    (k : ℕ) (j : Fin q) : ℝ :=
  let s := sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k
  (ρ s.R (HPolytope.rowLin N j)).val - (s.ZU₀.supportBound (-HPolytope.rowLin N j)).val

/-- Lines 4 and 14: `p_(j)` after the steps `0` to `k`. `max`, not line 14's
`min` — a union's support is the largest of its parts', see the findings. -/
noncomputable def LinearSys.minBackReachP (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ) : ℕ → Fin q → ℝ
  | 0 => fun j => sys.minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η 0 j
  | k + 1 => fun j => max (sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η k j)
      (sys.minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η (k + 1) j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 16: `R̂^∀∃(-τ)`, the `ω` steps' sets united, each cut by the
polytope `⟨N,p⟩_H` the propagated support functions built. -/
noncomputable def LinearSys.minBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  let Δt := (tend - t₀) / ω                                         -- 1. Δt ← (t_end - t₀)/ω
  let P := HPolytope.ineqs N                                        -- 4., 14. ⟨N,p⟩_H
    (sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η (ω - 1))
  ⋃ k < ω, ((sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k).R.construct ∩ P.construct)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

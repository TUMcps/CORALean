import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

/-!
# `Alg. 2`: the maximal time-interval backward reachable set

[1, Alg. 2]. `maxBackReachMu` is line 3, `maxBackReachPoly` lines 4-5,
`maxBackReachInit` lines 1-2, `maxBackReachCZ` line 11's conversion,
`maxBackReachStep` lines 7-12, `maxBackReachRun` the loop of lines 6-13, and
`maxBackReachTimeInterval` line 14. Nothing here searches, so no fuel: `ω` and
`η` are fixed by [1, Assumption 1] and the loop is bounded by `ω`.

`run 0` is line 2's pre-loop state, so line 14 unions `run (k+1)` — the sets the
`ω` iterations produce. Three departures. `P₁`, `P₂` are supplied rather than
computed inside, as `CZ` is to `Alg. 1`. (22)'s `‖·‖₂` is the spectral norm and
this tree's matrices carry the ℓ^∞ operator norm, so `maxBackReachMu` takes the
Frobenius norm, which dominates it; a larger `μ` only erodes more, which is the
sound direction for an inner approximation. And line 14's union is no
constrained zonotope, so the result is a `Set`, as in `Alg. 1`.

`ρ` is the caller's support oracle for a polytope — the linear program of (9).
`Zw` is (26), the constant centre trajectory's contribution over one interval.

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

/-- What one iteration of [1, Alg. 2] hands the next. -/
structure LinearSys.MaxBackReachState (n : ℕ) where
  /-- `t_k`, line 7. -/
  t : ℝ
  /-- `Z̲_U(t_k)`, line 8. -/
  ZU : Zonotope (Vec ℝ n)
  /-- `Ẑ_{W₀}(t_k)`, line 9. -/
  ZW₀ : Zonotope (Vec ℝ n)
  /-- `Ẑ_W(τ_{k-1})`, line 10. -/
  ZW : Zonotope (Vec ℝ n)
  /-- `R̂^{∃∀}(-τ_{k-1})`, line 12. -/
  R : ConZonotope (Vec ℝ n)

/-- Line 3: `μ ← √γ ‖(e^{AΔt} - I_n)G‖`, at the Frobenius norm, which dominates
(22)'s spectral one; `G` and `γ` come from `box(X_end)`. -/
noncomputable def LinearSys.maxBackReachMu (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (B : Zonotope (Vec ℝ n)) : ℝ :=
  Real.sqrt B.h
    * Real.sqrt (∑ j, ∑ i, ((exp (Δt • toRealMat sys.A) - 1) *ᵥ B.G j) i ^ 2)

/-- Lines 4-5: `X ⊖ F box(X_end) ⊖ B_μ`, one of the two polytopes of the inner
approximated homogeneous time-interval solution (21). -/
noncomputable def LinearSys.maxBackReachPoly (X : HPolytope (Vec ℝ n))
    (FB : Zonotope (Vec ℝ n)) (μ : ℝ) : HPolytope (Vec ℝ n) :=
  let XF := X.minkDiffOf FB.construct fun i => FB.supportBound (X.A i)  -- ⊖ F box(X_end)
  XF.minkDiffOf (⟨0, 0, μ⟩ : Capsule n).construct                       -- ⊖ B_μ
    fun i => (⟨0, 0, μ⟩ : Capsule n).supportBound (XF.A i)

/-- Lines 1-2: the two particular solutions accumulated up to `t₀`, before the
first iteration. -/
noncomputable def LinearSys.maxBackReachInit (sys : LinearSys 𝕋 n)
    (U W₀ : Zonotope (Vec ℝ n)) (t₀ : ℝ) (η : ℕ) : LinearSys.MaxBackReachState n :=
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZU := Zonotope.mtimes                                           -- 2. Z̲_U(t₀), see (24)
      (MatExp.expIntegral (toRealMat sys.A) t₀) U
    ZW₀ := sys.inputSolution (S := 𝒵) t₀ η W₀                       -- 2. Ẑ_{W₀}(t₀), see (23)
    ZW := Zonotope.ofPoint 0
    R := (Zonotope.ofPoint 0).conZonotope }

/-- Line 11: `CZ(P ⊖ Ẑ_W(τ_k))`, the eroded polytope converted by (17). -/
noncomputable def LinearSys.maxBackReachCZ
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P : HPolytope (Vec ℝ n)) (ZW : Zonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  let Q := P.minkDiffOf ZW.construct fun i => ZW.supportBound (P.A i)   -- ⊖ Ẑ_W(τ_k)
  HPolytope.conZonotope (P := Q)
    (fun j => ρ Q (LinearMap.proj j)) (fun j => ρ Q (-LinearMap.proj j))

/-- Lines 7-12: one iteration of [1, Alg. 2]'s main loop, propagating the two
particular solutions and assembling `R̂^{∃∀}(-τ_k)` from `P₁` and `P₂`. -/
noncomputable def LinearSys.maxBackReachStep (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MaxBackReachState n) : LinearSys.MaxBackReachState n :=
  let tk1 := s.t + Δt                                               -- 7. t_{k+1} ← t_k + Δt
  let Φk := exp (s.t • toRealMat sys.A)                             -- 7. e^{A t_k}
  let ZU := Zonotope.plus s.ZU (Zonotope.mtimes Φk                  -- 8. Z̲_U(t_{k+1})
    (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U))
  let ZW₀ := Zonotope.plus s.ZW₀                                    -- 9. Ẑ_{W₀}(t_{k+1})
    (Zonotope.mtimes Φk (sys.inputSolution (S := 𝒵) Δt η W₀))
  let ZW := Zonotope.plus ZW₀ (Zw s.t)                              -- 10. Ẑ_W(τ_k)
  let CZ := ConZonotope.linComb                                     -- 11. conv(CZ(…), CZ(…))
    (LinearSys.maxBackReachCZ ρ P₁ ZW) (LinearSys.maxBackReachCZ ρ P₂ ZW)
  let R := ConZonotope.mtimes (exp ((-tk1) • toRealMat sys.A))  -- 12. e^{-A t_{k+1}}(CZ ⊕ -Z̲_U)
    (ConZonotope.plus CZ (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) s.ZU)))
  { t := tk1, ZU := ZU, ZW₀ := ZW₀, ZW := ZW, R := R }

/-- Lines 6-13: the state after the first `k` iterations; `0` is line 2's
pre-loop state, so the `k`-th iteration's set is `run (k+1)`'s. -/
noncomputable def LinearSys.maxBackReachRun (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ Δt : ℝ) (η : ℕ) : ℕ → LinearSys.MaxBackReachState n
  | 0 => sys.maxBackReachInit U W₀ t₀ η
  | k + 1 => sys.maxBackReachStep ρ P₁ P₂ U W₀ Zw Δt η
      (sys.maxBackReachRun ρ P₁ P₂ U W₀ Zw t₀ Δt η k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 14: `R̂^{∃∀}(-τ)`, the union of the `ω` iterations' inner
approximated time-interval solutions. -/
noncomputable def LinearSys.maxBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  let Δt := (tend - t₀) / ω                                         -- 1. Δt ← (t_end - t₀)/ω
  ⋃ k < ω, (sys.maxBackReachRun ρ P₁ P₂ U W₀ Zw t₀ Δt η (k + 1)).R.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero
public import CORALean.ContDynamics.LinearSys.Theorems.ErrorConvergesToZeroTimeIntervalStepCurvatureError
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `Alg. 2`'s step sweep does run out of budget-violating steps

[1, Alg. 2] shrinks `Δt_i` by `μ` with no stated iteration count, so the definition carries a `fuel`
and returns `none` where it runs out. This is the fact that makes that honest: some fuel suffices.
The two halves are [1]'s own argument at the coarsest order. `ε_H` converges to `0` (`Prop. 3`), so
it eventually clears any positive `ε_H,max`; `ε_P` carries `Δt_i` as a factor whose cofactor
converges to `0`, so it eventually clears eq. (10)'s share, which is *linear* in `Δt_i`. The
geometric sequence `Δt_i μ^k` reaches into `𝓝[>] 0`, where both statements live. The check must be
complete here, `a ≤ b → le a b = true`, where `adaptTimeStep_budget` asks only the converse: a check
that gives up early is sound but need never report anything.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `εHmax` – maximal homogeneous error
* `εPmax` – maximal particular error
* `εPacc` – accumulated particular error
* `tf` – final time
* `ti` – step start time
* `Δtprev` – previous step length
* `μ` – shrink factor
* `ηmax` – maximal Taylor order

## Hypotheses
* `hle` – comparison oracle is complete
* `hεH` – homogeneous bound positive
* `hshare` – particular share positive
* `hΔtprev` – previous step positive
* `hμ0` – shrink factor positive
* `hμ1` – shrink factor below one
* `hηmax` – maximal order at least two

## Conclusion
* some fuel makes the sweep report a step within both budgets

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The geometric sequence of steps the sweep walks reaches into the punctured
neighbourhood both convergence facts are stated over. -/
theorem aux_tendsto_geometric_nhdsGT {Δt μ : ℝ} (hΔt : 0 < Δt) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) : -- --- CONCL ---
    Tendsto (fun k : ℕ => Δt * μ ^ k) atTop (𝓝[>] (0 : ℝ)) := by -- --- PROOF ---
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hpow : Tendsto (fun k : ℕ => μ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1
    simpa using hpow.const_mul Δt
  · exact Eventually.of_forall fun k => Set.mem_Ioi.mpr (by positivity)

/-- The step sweep reaches every `Δt μ^j` its fuel allows, so an order clearing
both bounds anywhere along that sequence is one it finds. -/
theorem aux_adaptTimeStepSearch_exists (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εPacc tf ti μ : ℝ) (ηmax : ℕ) : -- --- CONCL ---
    ∀ (j : ℕ) (Δt : ℝ) (η : ℕ),
      LinearSys.adaptTimeStepOrder sys le X₀ U εHmax ((εPmax - εPacc) / (tf - ti) * (Δt * μ ^ j))
          (Δt * μ ^ j) 2 (ηmax - 1) = some η →
      ∃ p, LinearSys.adaptTimeStepSearch sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt (j + 1)
        = some p := by -- --- PROOF ---
  intro j
  induction j with
  | zero =>
    intro Δt η h
    rw [pow_zero, mul_one] at h
    simp only [LinearSys.adaptTimeStepSearch, h]
    exact ⟨(Δt, η), rfl⟩
  | succ j ih =>
    intro Δt η h
    simp only [LinearSys.adaptTimeStepSearch]
    split
    · rename_i η' _
      exact ⟨(Δt, η'), rfl⟩
    -- no order cleared at this step, so the sweep moves to `Δt * μ` with the rest of the fuel
    · refine ih (Δt * μ) η ?_
      rwa [mul_assoc, ← pow_succ']

/-- One step of the order sweep: a candidate its own check clears is reported,
and `2 ≤ Φ_prop,max` is what leaves the sweep an iteration to report it in. -/
theorem aux_adaptTimeStepOrder_exists (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPi Δt : ℝ) {ηmax : ℕ} (hηmax : 2 ≤ ηmax)
    (hc : (le (sys.timeIntervalStepCurvatureError Δt 2 X₀) εHmax
      && le (sys.timePointStepRemainderError Δt 2 U) εPi) = true) : -- --- CONCL ---
    LinearSys.adaptTimeStepOrder sys le X₀ U εHmax εPi Δt 2 (ηmax - 1)
      = some 2 := by -- --- PROOF ---
  obtain ⟨m, hm⟩ : ∃ m, ηmax - 1 = m + 1 := ⟨ηmax - 2, by omega⟩
  rw [hm]
  simp only [LinearSys.adaptTimeStepOrder]
  split
  · rfl
  · rename_i hne
    exact absurd hc hne

/-- `ε_P`'s cofactor past the `Δt_i` it carries vanishes along the sweep, which
is what lets a *linear* share eventually cover it. -/
theorem aux_tendsto_remainderCofactor (sys : LinearSys 𝕋 n) (U : Zonotope (Vec ℝ n))
    {Δt μ : ℝ} (hΔt : 0 < Δt) (hμ0 : 0 < μ) (hμ1 : μ < 1) : -- --- CONCL ---
    Tendsto (fun k : ℕ => 2 * (∑ j, U.absBound j)
      * MatExp.expRemainderBound ((Δt * μ ^ k) • toRealMat sys.A) 2)
      atTop (𝓝 0) := by -- --- PROOF ---
  have h := (MatExp.tendsto_expRemainderBound_zero (toRealMat sys.A) 2).comp
    (aux_tendsto_geometric_nhdsGT hΔt hμ0 hμ1)
  simpa using h.const_mul (2 * ∑ j, U.absBound j)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: some fuel is enough. The sweep reports a step, at the coarsest
order, inside `ε_H,max` and inside eq. (10)'s share. -/
theorem LinearSys.exists_adaptTimeStep (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (X₀ U : Zonotope (Vec ℝ n))
    {εHmax εPmax εPacc tf ti Δtprev μ : ℝ} {ηmax : ℕ} (hεH : 0 < εHmax)
    (hshare : 0 < (εPmax - εPacc) / (tf - ti)) (hΔtprev : 0 < Δtprev) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hηmax : 2 ≤ ηmax) : -- --- CONCL ---
    ∃ (fuel : ℕ) (Δti εP : ℝ) (ηi : ℕ),
      sys.adaptTimeStep le X₀ U εHmax εPmax εPacc tf ti Δtprev μ ηmax fuel
        = some (Δti, ηi, εP) := by -- --- PROOF ---
  set Δt₀ := Δtprev / μ with hΔt₀
  have hΔt₀pos : 0 < Δt₀ := div_pos hΔtprev hμ0
  -- `ε_H` clears its own fixed bound eventually
  have hH : ∀ᶠ k : ℕ in atTop,
      sys.timeIntervalStepCurvatureError (Δt₀ * μ ^ k) 2 X₀ ≤ εHmax := by
    have h := (sys.errorConvergesToZero_timeIntervalStepCurvatureError 2 X₀).comp
      (aux_tendsto_geometric_nhdsGT hΔt₀pos hμ0 hμ1)
    exact (h.eventually_lt_const hεH).mono fun k hk => hk.le
  -- and `ε_P`'s cofactor clears the share's *slope*, which is what covers `ε_P` itself
  have hP : ∀ᶠ k : ℕ in atTop, sys.timePointStepRemainderError (Δt₀ * μ ^ k) 2 U
      ≤ (εPmax - εPacc) / (tf - ti) * (Δt₀ * μ ^ k) := by
    refine ((aux_tendsto_remainderCofactor sys U hΔt₀pos hμ0 hμ1).eventually_lt_const
      hshare).mono fun k hk => ?_
    have hpos : (0:ℝ) < Δt₀ * μ ^ k := by positivity
    rw [LinearSys.timePointStepRemainderError]
    calc 2 * (∑ j, U.absBound j) * ((Δt₀ * μ ^ k)
          * MatExp.expRemainderBound ((Δt₀ * μ ^ k) • toRealMat sys.A) 2)
        = (Δt₀ * μ ^ k) * (2 * (∑ j, U.absBound j)
          * MatExp.expRemainderBound ((Δt₀ * μ ^ k) • toRealMat sys.A) 2) := by ring
      _ ≤ (Δt₀ * μ ^ k) * ((εPmax - εPacc) / (tf - ti)) :=
          mul_le_mul_of_nonneg_left hk.le hpos.le
      _ = (εPmax - εPacc) / (tf - ti) * (Δt₀ * μ ^ k) := by ring
  obtain ⟨k, hHk, hPk⟩ := (hH.and hP).exists
  -- the check clears at the coarsest order, so the order sweep at that step reports it
  have hchk := aux_adaptTimeStepOrder_exists sys le X₀ U εHmax
    ((εPmax - εPacc) / (tf - ti) * (Δt₀ * μ ^ k)) (Δt₀ * μ ^ k) hηmax
    (by rw [Bool.and_eq_true]; exact ⟨hle _ _ hHk, hle _ _ hPk⟩)
  obtain ⟨p, hp⟩ := aux_adaptTimeStepSearch_exists sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax
    k Δt₀ 2 hchk
  exact ⟨k + 1, p.1, εPacc + sys.timePointStepRemainderError p.1 p.2 U, p.2, by
    simp only [LinearSys.adaptTimeStep, ← hΔt₀, hp]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
